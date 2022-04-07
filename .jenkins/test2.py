from subprocess import Popen, check_call
import argparse, subprocess, time, os, random, socket, threading

SSH_CONNECTING = 0
SSH_RUNNING = 1
SSH_COMPLETED = 2

SSH_TIMEOUT = 2
HALT_TIMEOUT = 10

def parse_args():
	parser = argparse.ArgumentParser()
	parser.add_argument('--subarch', required=True)
	parser.add_argument('--xmhf-bin', required=True)
	parser.add_argument('--qemu-image', required=True)
	parser.add_argument('--qemu-image-back', required=True)
	parser.add_argument('--smp', type=int, default=2)
	parser.add_argument('--work-dir', required=True)
	parser.add_argument('--no-display', action='store_true')
	parser.add_argument('--sshpass', help='Password for ssh')
	parser.add_argument('--verbose', action='store_true')
	parser.add_argument('--watch-serial', action='store_true')
	args = parser.parse_args()
	return args

def reset_qemu(args):
	'''
	Remove changes relative to backing qcow2 file
	'''
	assert os.path.exists(args.qemu_image)
	assert os.path.exists(args.qemu_image_back)
	check_call(['qemu-img', 'create', '-f', 'qcow2', '-b', args.qemu_image_back,
				'-F', 'qcow2', args.qemu_image])

def get_port():
	s = socket.socket(socket.AF_INET, socket.SOCK_STREAM, 0)
	for i in range(10000):
		num = random.randrange(1024, 65536)
		try:
			s.bind(('127.0.0.1', num))
		except OSError:
			continue
		s.close()
		return num
	else:
		raise RuntimeError('Cannot get port')

def spawn_qemu(args, serial_file):
	qemu_args = [
		'qemu-system-x86_64', '-m', '512M',
		'--drive', 'media=disk,file=%s,index=2' % args.qemu_image,
		'-device', 'e1000,netdev=net0',
		'-netdev', 'user,id=net0,hostfwd=tcp::%d-:22' % ssh_port,
		'-smp', str(args.smp), '-cpu', 'Haswell,vmx=yes', '--enable-kvm',
		'-serial', 'file:%s' % serial_file,
	]
	if args.no_display:
		qemu_args.append('-display')
		qemu_args.append('none')
	p = Popen(qemu_args, stdin=-1, stdout=-1, stderr=-1)
	return p

def get_ssh_cmd(args, ssh_port, exe='ssh', port_opt='-p'):
	ssh_cmd = []
	if args.sshpass:
		ssh_cmd += ['sshpass', '-p', args.sshpass]
	ssh_cmd += [exe, port_opt, str(ssh_port),
				'-o', 'ConnectTimeout=%d' % SSH_TIMEOUT,
				'-o', 'StrictHostKeyChecking=no',
				'-o', 'UserKnownHostsFile=/dev/null']
	return ssh_cmd

def send_ssh(args, ssh_port, bash_script, status):
	'''
	bash_script: script to run, must print something, or will retry forever
	status[0] = lock
	status[1] = SSH_CONNECTING (0): test not started yet
	status[1] = SSH_RUNNING (1): test started
	status[1] = SSH_COMPLETED (2): test finished
	status[2] = command return code
	status[3] = stdout lines
	'''
	ssh_cmd = get_ssh_cmd(args, ssh_port)
	ssh_cmd += ['lxy@127.0.0.1', 'bash', '-c', bash_script]
	state = None
	if args.verbose:
		print('send_ssh:', bash_script)
	while True:
		p = Popen(ssh_cmd, stdin=-1, stdout=-1, stderr=-1)
		while True:
			line = p.stdout.readline().decode()
			if not line:
				p.wait()
				assert p.returncode is not None
				# Connection failed
				# Warning: will incorrectly retry is script has no output. This
				# is necessary to distinguish between connection failure and
				# command failure.
				if status[1] == SSH_CONNECTING and p.returncode == 255:
					break
				# Command successfully completed
				with status[0]:
					status[1] = SSH_COMPLETED
					status[2] = p.returncode
				return
			print('ssh:     ', line.rstrip())
			with status[0]:
				status[1] = SSH_RUNNING
				status[2] = time.time()
				status[3].append(line.strip())
		time.sleep(1)
		if args.verbose:
			print('send_ssh:  retry SSH')

def run_ssh(bash_script, connect_timeout, run_timeout, ss):
	'''
	Run an ssh command with timeout control etc
	'''
	ts = threading.Thread(target=send_ssh,
							args=(args, ssh_port, bash_script, ss), daemon=True)
	ts.start()

	start_time = time.time()
	run_time = None
	while True:
		state = [None]
		with ss[0]:
			state[1:] = ss[1:]
		if args.verbose:
			print('run_ssh:  MET = %d;' % int(time.time() - start_time),
					'state =', state[:-1], len(state[-1]))
		if state[1] == SSH_CONNECTING:
			if time.time() - start_time > connect_timeout:
				return 'connect_aborted'
		elif state[1] == SSH_RUNNING:
			if run_time is None:
				run_time = time.time()
			if time.time() - run_time > run_timeout:
				return 'run_time_exceeded'
		elif state[1] == SSH_COMPLETED:
			# test completed
			return None
		else:
			raise ValueError
		time.sleep(1)

def ssh_operations(args, ssh_port):
	'''
	Return None if successful, error message otherwise
	'''
	wordsize = { 'i386': 32, 'amd64': 64 }[args.subarch]
	# 1. test booted
	ss = [threading.Lock(), SSH_CONNECTING, 0, []]
	stat = run_ssh('date; echo 1. test boot; ', 120, 10, ss)
	if stat or ss[2] != 0:
		return 'Failed to boot 1: (%s, %d, %s)' % (stat, ss[2], ss[3])
	# 2. scp
	scp_cmd = get_ssh_cmd(args, ssh_port, 'scp', '-P')
	scp_cmd += [
		os.path.join(args.xmhf_bin, 'init-x86-%s.bin' % args.subarch),
		os.path.join(args.xmhf_bin, 'hypervisor-x86-%s.bin.gz' % args.subarch),
		'lxy@127.0.0.1:/tmp',
	]
	print('scp')
	check_call(scp_cmd)
	print('scp done')
	# 3. install
	ss = [threading.Lock(), SSH_CONNECTING, 0, []]
	install_num = { 'i386': 86, 'amd64': 64 }[args.subarch]
	stat = run_ssh('date; echo 3. install; ./install%d.sh' % install_num,
					10, 20, ss)
	if stat or ss[2] != 0:
		return 'Failed to install: (%s, %d, %s)' % (stat, ss[2], ss[3])
	# 4. restart
	ss = [threading.Lock(), SSH_CONNECTING, 0, []]
	stat = run_ssh('date; echo 4. restart; touch /tmp/asdf; sudo init 6; ',
					10, 20, ss)
	if stat:
		return 'Failed to restart: (%s, %d, %s)' % (stat, ss[2], ss[3])
	# 5. make sure restart started
	while True:
		print('Checking restart')
		ss = [threading.Lock(), SSH_CONNECTING, 0, []]
		stat = run_ssh('date; echo 5. restart start; ls /tmp/asdf', 10, 10, ss)
		if stat or ss[2] != 0:
			print('Restart checked')
			break
	# 6. test booted 2
	ss = [threading.Lock(), SSH_CONNECTING, 0, []]
	stat = run_ssh('date; echo 6. test boot 2; [ ! -f /tmp/asdf ]', 150, 10, ss)
	if stat or ss[2] != 0:
		return 'Failed to boot 2: (%s, %d, %s)' % (stat, ss[2], ss[3])
	# 7. run test
	ss = [threading.Lock(), SSH_CONNECTING, 0, []]
	stat = run_ssh('date; echo 7. run test; ./test_args%d 7 7 7' % wordsize,
					10, 30, ss)
	if stat or ss[2] != 0 or 'Test pass' not in ss[3]:
		return 'Test failed: (%s, %d, %s)' % (stat, ss[2], ss[3])
	# Success
	return None

if __name__ == '__main__':
	args = parse_args()
	reset_qemu(args)
	ssh_port = get_port()
	print('Use ssh port', ssh_port)
	serial_file = os.path.join(args.work_dir, 'serial')
	p = spawn_qemu(args, serial_file)

	# Simple workaround to watch serial output
	if args.watch_serial:
		threading.Thread(target=os.system, args=('tail -F %s' % serial_file,),
						daemon=True).start()

	result = 'Unknown'
	try:
		result = ssh_operations(args, ssh_port)
		if result is None:
			# give the OS 10 seconds to shutdown; if wait() succeeds, calling
			# wait() again will still succeed
			try:
				p.wait(timeout=HALT_TIMEOUT)
			except subprocess.TimeoutExpired:
				pass
	finally:
		p.kill()
		p.wait()

	if result is None:
		exit(0)
	else:
		print('ERROR in ssh_operations()')
		print(result)
		exit(1)

