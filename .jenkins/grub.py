'''
	Generate a small MBR image that boots XMHF.
'''

from subprocess import check_call
import argparse, os

def parse_args():
	parser = argparse.ArgumentParser()
	parser.add_argument('--subarch', required=True)
	parser.add_argument('--xmhf-bin', required=True)
	parser.add_argument('--work-dir', required=True)
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

	# Construct ext4
	b_img = os.path.join(grub_dir, 'b.img')
	check_call(['dd', 'if=/dev/zero', 'of=%s' % b_img, 'bs=1M',
				'seek=%d' % ext4_size_mb, 'count=0'])
	check_call(['/sbin/mkfs.ext4', b_img])
	debugfs_cmds = []
	debugfs_cmds.append('mkdir boot')
	debugfs_cmds.append('cd boot')
	for i in ['init-x86-%s.bin', 'hypervisor-x86-%s.bin.gz']:
		name = i % args.subarch
		src_pathname = os.path.join(args.xmhf_bin, name)
		debugfs_cmds.append('write %s %s' % (src_pathname, name))
	debugfs_cmds.append('mkdir grub')
	debugfs_cmds.append('cd grub')
	debugfs_cmds.append('write %s grub.cfg' %
						os.path.join(args.boot_dir, 'grub/grub.cfg'))
	envfile = 'grubenv-%s' % args.subarch
	debugfs_cmds.append('write %s grubenv' %
						os.path.join(args.boot_dir, envfile))
	debugfs_cmds.append('mkdir i386-pc')
	debugfs_cmds.append('cd i386-pc')
	mods_dir = download_grub(args)
	for i in os.listdir(mods_dir):
		debugfs_cmds.append('write %s %s' % (os.path.join(mods_dir, i), i))
	cmd_file = os.path.join(grub_dir, 'debugfs.cmd')
	print(*debugfs_cmds, sep='\n', file=open(cmd_file, 'w'))
	popen_stdout = { 'stdout': -1 }
	if args.verbose:
		del popen_stdout['stdout']
	check_call(['/sbin/debugfs', '-w', b_img, '-f', cmd_file], **popen_stdout)

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


