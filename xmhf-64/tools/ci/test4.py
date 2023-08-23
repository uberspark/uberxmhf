'''
	Test XMHF using QEMU, but do not use SSH
'''

from subprocess import Popen, check_call
import argparse, subprocess, time, os, re, random, socket, threading

println_lock = threading.Lock()

SERIAL_WAITING = 0
SERIAL_PASS = 1
SERIAL_FAIL = 2

def parse_args():
	parser = argparse.ArgumentParser()
	parser.add_argument('--guest-subarch', required=True,
						help='Subarch of guest OS')
	parser.add_argument('--qemu-image', required=True)
	parser.add_argument('--smp', type=int, default=2)
	parser.add_argument('--work-dir', required=True)
	parser.add_argument('--windows-dir', default='tools/ci/windows/')
	parser.add_argument('--no-display', action='store_true')
	parser.add_argument('--verbose', action='store_true')
	parser.add_argument('--watch-serial', action='store_true')
	parser.add_argument('--memory', default='1024M')
	parser.add_argument('--qemu-timeout', type=int, default=200)
	args = parser.parse_args()
	return args

def printlog(line):
	with println_lock:
		print(line)

def println(*args):
	with println_lock:
		print('{', *args, '}')

def spawn_qemu(args, xmhf_img, serial_file):
	bios_bin = os.path.join(args.windows_dir, 'bios.bin')
	windows_grub_img = os.path.join(args.windows_dir, 'grub_windows.img')
	pal_demo_img = os.path.join(args.work_dir, 'pal_demo.img')
	qemu_args = [
		'qemu-system-x86_64', '-m', args.memory,
		'--drive', 'media=disk,file=%s,format=raw,index=0' % xmhf_img,
		'--drive', 'media=disk,file=%s,format=raw,index=1' % windows_grub_img,
		'--drive', 'media=disk,file=%s,format=qcow2,index=2' % args.qemu_image,
		'--drive', 'media=disk,file=%s,format=raw,index=3' % pal_demo_img,
		'--bios', bios_bin,
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
	aborted = False
	started_tests = set()
	passed_tests = set()
	for i in gen:
		call_arg = -1
		call_arg_found = False
		if 'test hypercall, ecx=' in i:
			searched = re.search('test hypercall, ecx=(0x[0-9a-f]{8})$', i)
			if searched:
				call_arg = int(searched.groups()[0], 16);
				call_arg_found = True
		if 'test hypercall, rcx=' in i and not call_arg_found:
			searched = re.search('test hypercall, rcx=(0x[0-9a-f]{16})$', i)
			if searched:
				call_arg = int(searched.groups()[0], 16);
				call_arg_found = True
		if not call_arg_found:
			continue
		# Process call_arg
		println('hypercall: %d' % call_arg);
		if call_arg == 1000700086:
			println('OS: Windows 7 x86')
		elif call_arg == 1000700064:
			println('OS: Windows 7 x64')
		elif call_arg == 1000810064:
			println('OS: Windows 8.1 x64')
		elif call_arg == 1001000086:
			println('OS: Windows 10 x86')
		elif call_arg == 1001000064:
			println('OS: Windows 10 x64')
		elif call_arg == 1100000032:
			println('32 test started')
			started_tests.add(32)
		elif call_arg == 1100000064:
			println('64 test started')
			started_tests.add(64)
		elif call_arg == 1200000032:
			println('32 test failed')
			aborted = True
		elif call_arg == 1200000064:
			println('64 test failed')
			aborted = True
		elif call_arg == 1300000032:
			println('32 test passed')
			passed_tests.add(32)
		elif call_arg == 1300000064:
			println('64 test passed')
			passed_tests.add(64)
		elif call_arg == 1444444444:
			println('Something failed')
			aborted = True
		elif call_arg == 1555555555:
			expected_tests = None
			if args.guest_subarch == 'i386':
				expected_tests = {32}
			elif args.guest_subarch == 'amd64':
				expected_tests = {32, 64}
			else:
				raise ValueError
			result = SERIAL_FAIL
			println('passed_tests   =', passed_tests)
			println('started_tests  =', started_tests)
			println('expected_tests =', expected_tests)
			if (passed_tests == started_tests and
				passed_tests == expected_tests and not aborted):
				result = SERIAL_PASS
			with serial_result[0]:
				serial_result[1] = result
				break
		else:
			println('Unknown call_arg: %d' % call_arg)
			aborted = True
		if aborted:
			with serial_result[0]:
				serial_result[1] = SERIAL_FAIL
				break
	for i in gen:
		pass

def main():
	args = parse_args()
	serial_file = os.path.join(args.work_dir, 'serial')
	xmhf_img = os.path.join(args.work_dir, 'grub/c.img')
	check_call(['rm', '-f', serial_file])
	p = spawn_qemu(args, xmhf_img, serial_file)

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

