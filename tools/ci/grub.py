'''
	Generate a small MBR image that boots XMHF.
'''

from subprocess import Popen, check_call
import argparse, os, re

def parse_args():
	parser = argparse.ArgumentParser()
	parser.add_argument('--subarch', required=True,
						help='i386 or amd64 for XMHF, or windows for Windows')
	parser.add_argument('--xmhf-bin', required=False,
						help='Directory that contains XMHF binaries')
	parser.add_argument('--work-dir', required=True,
						help='Place to generate GRUB')
	parser.add_argument('--verbose', action='store_true')
	parser.add_argument('--boot-dir', required=True,
						help='Contain /boot and MBR image to generate GRUB')
	args = parser.parse_args()
	return args

def download_grub(args):
	'Download GRUB to args.boot_dir'
	mods_dir = os.path.join(os.path.join(args.boot_dir, 'grub/i386-pc/'))
	if not os.path.exists(mods_dir) or len(os.listdir(mods_dir)) < 284:
		check_call(['mkdir', '-p', mods_dir])
		deb_dir = os.path.join(args.work_dir, 'deb')
		check_call(['rm', '-rf', deb_dir])
		check_call(['mkdir', '-p', deb_dir])
		url_dir = 'http://http.us.debian.org/debian/pool/main/g/grub2/'
		deb_name = 'grub-pc-bin_2.04-20_amd64.deb'
		check_call(['wget', url_dir + deb_name], cwd=deb_dir)
		check_call(['ar', 'x', deb_name], cwd=deb_dir)
		check_call(['tar', 'Jxf', 'data.tar.xz'], cwd=deb_dir)
		src_dir = os.path.join(deb_dir, 'usr/lib/grub/i386-pc/')
		count = 0
		for i in os.listdir(src_dir):
			if (i.endswith('.mod') or i.endswith('.o') or i.endswith('.lst') or
				i in ('boot.img', 'core.img', 'modinfo.sh')):
				check_call(['cp', os.path.join(src_dir, i), mods_dir])
				count += 1
		assert count >= 284
	return mods_dir

def generate_xmhf_image(args):
	grub_dir = os.path.join(args.work_dir, 'grub')
	check_call(['rm', '-rf', grub_dir])
	assert not os.path.exists(grub_dir)
	os.mkdir(grub_dir)

	# As of writing test3.py, GRUB uses less than 4M, XMHF uses less than 1M.
	ext4_size_mb = 7

	# Construct ext4, prepare command file
	b_img = os.path.join(grub_dir, 'b.img')
	check_call(['dd', 'if=/dev/zero', 'of=%s' % b_img, 'bs=1M',
				'seek=%d' % ext4_size_mb, 'count=0'])
	check_call(['/sbin/mkfs.ext4', b_img])
	debugfs_cmds = []
	debugfs_cmds.append('mkdir boot')
	debugfs_cmds.append('cd boot')
	if args.subarch in ['i386', 'amd64']:
		for i in ['init-x86-%s.bin', 'hypervisor-x86-%s.bin.gz']:
			name = i % args.subarch
			src_pathname = os.path.join(args.xmhf_bin, name)
			debugfs_cmds.append('write %s %s' % (src_pathname, name))
	elif args.subarch == 'windows':
		pass
	else:
		raise Exception('Unknown subarch: %s' % repr(args.subarch))
	debugfs_cmds.append('mkdir grub')
	debugfs_cmds.append('cd grub')
	debugfs_cmds.append('write %s grub.cfg' %
						os.path.join(args.boot_dir,
									'grub.cfg.%s' % args.subarch))
	debugfs_cmds.append('mkdir i386-pc')
	debugfs_cmds.append('cd i386-pc')
	mods_dir = download_grub(args)
	for i in os.listdir(mods_dir):
		debugfs_cmds.append('write %s %s' % (os.path.join(mods_dir, i), i))
	cmd_file = os.path.join(grub_dir, 'debugfs.cmd')
	print(*debugfs_cmds, sep='\n', file=open(cmd_file, 'w'))

	# Run debugfs on debugfs.cmd
	popen_stdio = { 'stdout': -1, 'stderr': -1 }
	if args.verbose:
		del popen_stdio['stdout']
	p = Popen(['/sbin/debugfs', '-w', b_img, '-f', cmd_file], **popen_stdio)
	debugfs_stdout, debugfs_stderr = p.communicate(b'')
	assert p.returncode == 0
	errs = debugfs_stderr.decode().strip()
	# debugfs will not return non-zero code when error. So we parse stderr to
	# determine whether an error happens. We assume that when there are no
	# errors, only a line with version information is printed. For example,
	# 'debugfs 1.46.3 (27-Jul-2021)\n'
	if not re.fullmatch('debugfs [^\n]+', errs):
		print(errs)
		raise Exception('debugfs likely failed')

	# Concat to c.img
	a_img = os.path.join(args.boot_dir, 'a.img')
	c_img = os.path.join(grub_dir, 'c.img')
	check_call(['dd', 'if=/dev/zero', 'of=%s' % c_img, 'bs=1M',
				'seek=%d' % (ext4_size_mb + 1), 'count=0'])
	check_call(['dd', 'if=%s' % a_img, 'of=%s' % c_img, 'conv=sparse,notrunc',
				'bs=512', 'count=1M', 'iflag=count_bytes'])
	check_call(['dd', 'if=%s' % b_img, 'of=%s' % c_img, 'conv=sparse,notrunc',
				'bs=512', 'seek=1M', 'oflag=seek_bytes'])
	return c_img

def main():
	args = parse_args()
	xmhf_img = generate_xmhf_image(args)
	assert xmhf_img == os.path.join(args.work_dir, 'grub/c.img')
	return 0

if __name__ == '__main__':
	exit(main())

