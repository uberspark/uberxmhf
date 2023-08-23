'''
	Test running LHV in XMHF in QEMU
'''

from subprocess import Popen, check_call
from collections import defaultdict
import argparse, subprocess, time, os, re, random, socket, threading

println_lock = threading.Lock()

SERIAL_WAITING = 0
SERIAL_PASS = 1
SERIAL_FAIL = 2

def parse_args():
	parser = argparse.ArgumentParser()
	parser.add_argument('--xmhf-img', required=True)
	parser.add_argument('--lhv-img', required=True)
	parser.add_argument('--smp', type=int, default=4)
	parser.add_argument('--work-dir', required=True)
	parser.add_argument('--no-display', action='store_true')
	parser.add_argument('--verbose', action='store_true')
	parser.add_argument('--watch-serial', action='store_true')
	parser.add_argument('--memory', default='1024M')
	parser.add_argument('--qemu-timeout', type=int, default=30)
	args = parser.parse_args()
	return args

def printlog(line):
	with println_lock:
		print(line)

def println(*args):
	with println_lock:
		print('{', *args, '}')

def spawn_qemu(args, serial_file):
	qemu_args = [
		'qemu-system-x86_64', '-m', args.memory,
		'--drive', 'media=disk,file=%s,format=raw,index=0' % args.xmhf_img,
		'--drive', 'media=disk,file=%s,format=raw,index=1' % args.lhv_img,
		'-smp', str(args.smp), '-cpu', 'Haswell,vmx=yes', '--enable-kvm',
		'-serial', 'file:%s' % serial_file,
	]
	if args.no_display:
		qemu_args.append('-display')
		qemu_args.append('none')
	popen_stderr = { 'stderr': -1 }
	if args.verbose:
		del popen_stderr['stderr']
		print(' '.join(qemu_args))
	p = Popen(qemu_args, stdin=-1, stdout=-1, **popen_stderr)
	return p

def serial_thread(args, serial_file, serial_result):
	def gen_lines():
		while not os.path.exists(serial_file):
			time.sleep(0.1)
		println('serial_file exists')
		with open(serial_file, 'r') as f:
			while True:
				line = f.readline()
				if line:
					i = line.strip('\n')
					if args.watch_serial:
						printlog(i)
					yield i
				else:
					time.sleep(0.1)
	gen = gen_lines()
	for i in gen:
		if 'eXtensible Modular Hypervisor' in i:
			println('Banner found!')
			break
	for i in gen:
		if 'e820' in i:
			println('E820 found!')
			break
	test_count = defaultdict(int)
	for i in gen:
		assert len(test_count) <= args.smp
		if len(test_count) == args.smp and min(test_count.values()) > 20:
			with serial_result[0]:
				serial_result[1] = SERIAL_PASS
				break
		fmt = 'CPU\((0x[0-9a-f]+)\): LHV in XMHF test iter \d+'
		matched = re.fullmatch(fmt, i)
		if matched:
			test_count[matched.groups()[0]] += 1
			continue
	for i in gen:
		pass

def main():
	args = parse_args()
	serial_file = os.path.join(args.work_dir, 'serial')
	check_call(['rm', '-f', serial_file])
	p = spawn_qemu(args, serial_file)

	try:
		serial_result = [threading.Lock(), SERIAL_WAITING]
		threading.Thread(target=serial_thread,
						args=(args, serial_file, serial_result),
						daemon=True).start()
		for i in range(args.qemu_timeout):
			println('MET = %d' % i)
			with serial_result[0]:
				if serial_result[1] != SERIAL_WAITING:
					break
			time.sleep(1)
	finally:
		p.kill()
		p.wait()

	with serial_result[0]:
		if serial_result[1] == SERIAL_PASS:
			println('TEST PASSED')
			return 0
		elif serial_result[1] == SERIAL_WAITING:
			println('TEST TIME OUT')
			return 1

	println('TEST FAILED')
	return 1

if __name__ == '__main__':
	exit(main())

