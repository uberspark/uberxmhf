from subprocess import Popen, check_call
import argparse, subprocess, time, os, random, socket, threading

SSH_CONNECTING = 0
SSH_RUNNING = 1
SSH_COMPLETED = 2

SSH_TIMEOUT = 2
HALT_TIMEOUT = 10

println_lock = threading.Lock()

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
	parser.add_argument('--skip-install', action='store_true')
	parser.add_argument('--no-test-xmhf', action='store_true',
						help='Skip testing XMHF in QEMU for Circle CI set-up '
							'(deprecated)')
	args = parser.parse_args()
	return args

def println(*args):
	with println_lock:
		print('{', *args, '}')

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

def spawn_qemu(args, serial_file, ssh_port):
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
	popen_stderr = { 'stderr': -1 }
	if args.verbose:
		del popen_stderr['stderr']
	p = Popen(qemu_args, stdin=-1, stdout=-1, **popen_stderr)
	return p

class SSHOperations:
	def __init__(self, args, ssh_port):
		self.args = args
		self.ssh_port = ssh_port
	def get_ssh_cmd(self, exe='ssh', port_opt='-p'):
		ssh_cmd = []
		if self.args.sshpass:
			ssh_cmd += ['sshpass', '-p', self.args.sshpass]
		ssh_cmd += [exe, port_opt, str(self.ssh_port),
					'-o', 'ConnectTimeout=%d' % SSH_TIMEOUT,
					'-o', 'StrictHostKeyChecking=no',
					'-o', 'UserKnownHostsFile=/dev/null']
		return ssh_cmd
	def send_ssh(self, bash_script, status):
		'''
		bash_script: script to run, must print something, or will retry forever
		status[0] = lock
		status[1] = SSH_CONNECTING (0): test not started yet
		status[1] = SSH_RUNNING (1): test started
		status[1] = SSH_COMPLETED (2): test finished
		status[2] = command return code
		status[3] = stdout lines
		status[4] = whether abort
		'''
		ssh_cmd = self.get_ssh_cmd()
		ssh_cmd += ['lxy@127.0.0.1', 'bash', '-c', bash_script]
		state = None
		if self.args.verbose:
			println('send_ssh:', repr(bash_script))
		while True:
			p = Popen(ssh_cmd, stdin=-1, stdout=-1, stderr=-1)
			while True:
				line = p.stdout.readline().decode()
				if not line:
					p.wait()
					assert p.returncode is not None
					# Connection failed
					# Warning: will incorrectly retry is script has no output.
					# This is necessary to distinguish between connection
					# failure and command failure.
					if status[1] == SSH_CONNECTING and p.returncode == 255:
						break
					# Command successfully completed
					with status[0]:
						status[1] = SSH_COMPLETED
						status[2] = p.returncode
					return
				println('ssh:     ', repr(line.rstrip()))
				with status[0]:
					status[1] = SSH_RUNNING
					status[2] = time.time()
					status[3].append(line.strip())
					# Check abort
					if status[4]:
						return
			time.sleep(1)
			if self.args.verbose:
				println('send_ssh:  retry SSH', repr(bash_script))
	def run_ssh(self, bash_script, connect_timeout, run_timeout, ss):
		'''
		Run an ssh command with timeout control etc
		'''
		assert not ss
		for i in [threading.Lock(), SSH_CONNECTING, 0, [], 0]:
			ss.append(i)
		ts = threading.Thread(target=self.send_ssh,
								args=(bash_script, ss), daemon=True)
		ts.start()

		start_time = time.time()
		run_time = None
		while True:
			state = [None]
			with ss[0]:
				state[1:] = ss[1:]
			if self.args.verbose:
				println('run_ssh:  MET = %d;' % int(time.time() - start_time),
						'state =', state[:3], len(state[3]))
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
	def ssh_operations(self):
		'''
		Return None if successful, error message otherwise
		'''
		if not self.args.skip_install:
			ans = self.ssh_operations_install()
			if ans is not None:
				return ans
		return self.ssh_operations_test()
	def ssh_operations_install(self):
		# 1. test booted
		ss = []
		stat = self.run_ssh('date; echo 1. test boot; ', 120, 10, ss)
		if stat or ss[2] != 0:
			return 'Failed to boot 1: (%s, %d, %s)' % (stat, ss[2], ss[3])
		# 2. scp
		scp_cmd = self.get_ssh_cmd('scp', '-P')
		pf = lambda x: os.path.join(self.args.xmhf_bin, x % self.args.subarch)
		scp_cmd += [
			pf('init-x86-%s.bin'),
			pf('hypervisor-x86-%s.bin.gz'),
			'lxy@127.0.0.1:/tmp',
		]
		println('scp')
		check_call(scp_cmd)
		println('scp done')
		# 3. install
		ss = []
		install_num = { 'i386': 86, 'amd64': 64 }[self.args.subarch]
		stat = self.run_ssh(
					'date; echo 3. install; ./install%d.sh' % install_num,
					10, 20, ss)
		if stat or ss[2] != 0:
			return 'Failed to install: (%s, %d, %s)' % (stat, ss[2], ss[3])
		# 4. restart
		ss = []
		stat = self.run_ssh(
					'date; echo 4. restart; touch /tmp/asdf; sudo init 6; ',
					10, 20, ss)
		if stat:
			return 'Failed to restart: (%s, %d, %s)' % (stat, ss[2], ss[3])
		# 5. make sure restart started
		while True:
			println('Checking restart')
			ss = []
			stat = self.run_ssh('date; echo 5. restart start; ls /tmp/asdf',
								10, 10, ss)
			if stat or ss[2] != 0:
				println('Restart checked')
				break
	def ssh_operations_test(self):
		# For Circle CI, cannot boot Debian on XMHF on KVM, so return success
		if self.args.no_test_xmhf:
			sleep_dur = 50
			for i in range(sleep_dur):
				println('Sleep', i, '/', sleep_dur)
			return None
		# 6. test booted 2
		ss = []
		stat = self.run_ssh('date; echo 6. test boot 2; [ ! -f /tmp/asdf ]',
							150, 10, ss)
		if stat or ss[2] != 0:
			return 'Failed to boot 2: (%s, %d, %s)' % (stat, ss[2], ss[3])
		# 7. run test
		wordsizes = { 'i386': [32], 'amd64': [32, 64] }[self.args.subarch]
		for w in wordsizes:
			ss = []
			cmd = 'date; echo 7. run test %d; ./test_args%d 7 7 7' % (w, w)
			stat = self.run_ssh(cmd, 10, 45, ss)
			if stat or ss[2] != 0 or 'Test pass' not in ss[3]:
				return 'Test %d failed: (%s, %d, %s)' % (w, stat, ss[2], ss[3])
		# Success
		return None

def main():
	args = parse_args()
	if not args.skip_install:
		reset_qemu(args)
	ssh_port = get_port()
	println('Use ssh port', ssh_port)
	serial_file = os.path.join(args.work_dir, 'serial')
	p = spawn_qemu(args, serial_file, ssh_port)

	# Simple workaround to watch serial output
	if args.watch_serial:
		threading.Thread(target=os.system, args=('tail -F %s' % serial_file,),
						daemon=True).start()

	result = 'Unknown'
	try:
		result = SSHOperations(args, ssh_port).ssh_operations()
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
		println('PASS: successful ssh_operations()')
	else:
		println('ERROR in ssh_operations()')
		println(result)
		return 1

	# Test serial output
	println('Test XMHF banner in serial')
	check_call(['grep', 'eXtensible Modular Hypervisor', serial_file])
	println('Test E820 in serial')
	check_call(['grep', 'e820', serial_file])

	println('TEST PASSED')
	return 0

if __name__ == '__main__':
	exit(main())

