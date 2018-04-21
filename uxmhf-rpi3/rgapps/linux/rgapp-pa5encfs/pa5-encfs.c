/*
 * @UBERXMHF_LICENSE_HEADER_START@
 *
 * uber eXtensible Micro-Hypervisor Framework (Raspberry Pi)
 *
 * Copyright 2018 Carnegie Mellon University. All Rights Reserved.
 *
 * NO WARRANTY. THIS CARNEGIE MELLON UNIVERSITY AND SOFTWARE ENGINEERING
 * INSTITUTE MATERIAL IS FURNISHED ON AN "AS-IS" BASIS. CARNEGIE MELLON
 * UNIVERSITY MAKES NO WARRANTIES OF ANY KIND, EITHER EXPRESSED OR IMPLIED,
 * AS TO ANY MATTER INCLUDING, BUT NOT LIMITED TO, WARRANTY OF FITNESS FOR
 * PURPOSE OR MERCHANTABILITY, EXCLUSIVITY, OR RESULTS OBTAINED FROM USE OF
 * THE MATERIAL. CARNEGIE MELLON UNIVERSITY DOES NOT MAKE ANY WARRANTY OF
 * ANY KIND WITH RESPECT TO FREEDOM FROM PATENT, TRADEMARK, OR COPYRIGHT
 * INFRINGEMENT.
 *
 * Released under a BSD (SEI)-style license, please see LICENSE or
 * contact permission@sei.cmu.edu for full terms.
 *
 * [DISTRIBUTION STATEMENT A] This material has been approved for public
 * release and unlimited distribution.  Please see Copyright notice for
 * non-US Government use and distribution.
 *
 * Carnegie Mellon is registered in the U.S. Patent and Trademark Office by
 * Carnegie Mellon University.
 *
 * @UBERXMHF_LICENSE_HEADER_END@
 */

/*
 * Author: Amit Vasudevan (amitvasudevan@acm.org)
 *
 */

/*
 moune FUSE: Filesystem in Userspace
  Copyright (C) 2001-2007  Miklos Szeredi <miklos@szeredi.hu>

  Minor modifications and note by Andy Sayler (2012) <www.andysayler.com>

  Source: fuse-2.8.7.tar.gz examples directory
  http://sourceforge.net/projects/fuse/files/fuse-2.X/

  This program can be distributed under the terms of the GNU GPL.
  See the file COPYING.

  gcc -Wall `pkg-config fuse --cflags` fusexmp.c -o fusexmp `pkg-config fuse --libs`

  Note: This implementation is largely stateless and does not maintain
        open file handels between open and release calls (fi->fh).
        Instead, files are opened and closed as necessary inside read(), write(),
        etc calls. As such, the functions that rely on maintaining file handles are
        not implmented (fgetattr(), etc). Those seeking a more efficient and
        more complete implementation may wish to add fi->fh support to minimize
        open() and close() calls and support fh dependent functions.

*/

#define FUSE_USE_VERSION 28
#define HAVE_SETXATTR
#define ENCRYPT 1
#define DECRYPT 0
#define PASS_THROUGH (-1)

#ifdef HAVE_CONFIG_H
#include <config.h>
#endif

#ifdef linux
/* For pread()/pwrite() */
#define _XOPEN_SOURCE 500
#endif

#include <assert.h>
#include <fuse.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <linux/limits.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <dirent.h>
#include <errno.h>
#include <sys/time.h>
#include "aes-crypt.h"
#ifdef HAVE_SETXATTR
#include <sys/xattr.h>
#endif

/* #define XMP_DATA ((struct xmp_state *) fuse_get_context()->private_data) */

//////
// helper functions
//////


char* root_path;
char* password;

/* is_encrypted: returns 1 if encryption succeeded, 0 otherwise */
int is_encrypted(const char *path)
{
	int ret;
	char xattr_val[5];
	getxattr(path, "user.encfs", xattr_val, sizeof(char)*5);
	fprintf(stderr, "xattr set to: %s\n", xattr_val);

	ret = (strcmp(xattr_val, "true") == 0);
	return ret;
}

/* add_encrypted_attr: returns 1 on success, 0 on failure */
int add_encrypted_attr(const char *path)
{
	int ret;
	int setxattr_ret;
	setxattr_ret = setxattr(path, "user.encfs", "true", (sizeof(char)*5), 0);
	ret = setxattr_ret == 0;
	fprintf(stderr, "\n%s: setxattr %s\n", __FUNCTION__, ret > 0 ? "succeeded" : "failed");
	return ret;
}

// add non-padded size attr
// returns 1 on success, 0 on failure
int add_nonpaddedsize_attr(const char *path, unsigned int nonpaddedsize){
	int ret;
	int setxattr_ret;

	setxattr_ret = setxattr(path, "user.nonpaddedsize", &nonpaddedsize, sizeof(unsigned int), 0);
	ret = setxattr_ret == 0;
	fprintf(stderr, "\n%s: setxattr %s\n", __FUNCTION__, ((ret > 0) ? "succeeded" : "failed"));

	return ret;
}



char *prefix_path(const char *path)
{
	size_t len = strlen(path) + strlen(root_path) + 1;
	char *root_dir = malloc(len * sizeof(char));

	strcpy(root_dir, root_path);
	strcat(root_dir, path);

	return root_dir;
}

static inline int file_size(FILE *file) {
    struct stat st;

    if (fstat(fileno(file), &st) == 0)
        return st.st_size;

    return -1;
}

/* read_file: for debugging tempfiles */
int read_file(FILE *file)
{
	int c;
	int file_contains_something = 0;
	FILE *read = file; /* don't move original file pointer */
	if (read) {
		while ((c = getc(read)) != EOF) {
			file_contains_something = 1;
			putc(c, stderr);
		}
	}
	if (!file_contains_something)
		fprintf(stderr, "file was empty\n");
	rewind(file);
	/* fseek(tmpf, offset, SEEK_END); */
	return 0;
}






//////
// various fuse entry-points
//////

static int xmp_getattr(const char *fuse_path, struct stat *stbuf)
{
	char *path = prefix_path(fuse_path);

	int res;

	//////
	// TBD: return non-padded size in stbuf->st_size
	//////

	res = lstat(path, stbuf);
	if (res == -1)
		return -errno;

	return 0;
}

static int xmp_access(const char *fuse_path, int mask)
{
	char *path = prefix_path(fuse_path);

	int res;

	res = access(path, mask);
	if (res == -1)
		return -errno;

	return 0;
}

static int xmp_readlink(const char *fuse_path, char *buf, size_t size)
{
	char *path = prefix_path(fuse_path);

	int res;

	res = readlink(path, buf, size - 1);
	if (res == -1)
		return -errno;

	buf[res] = '\0';
	return 0;
}

static int xmp_readdir(const char *fuse_path, void *buf, fuse_fill_dir_t filler,
		       off_t offset, struct fuse_file_info *fi)
{
	char *path = prefix_path(fuse_path);

	DIR *dp;
	struct dirent *de;
	fprintf(stderr, "Path: %s\n", path);

	(void) offset;
	(void) fi;

	dp = opendir(path);
	if (dp == NULL)
		return -errno;

	while ((de = readdir(dp)) != NULL) {
		struct stat st;
		memset(&st, 0, sizeof(st));
		st.st_ino = de->d_ino;
		st.st_mode = de->d_type << 12;
		if (filler(buf, de->d_name, &st, 0))
			break;
	}

	closedir(dp);
	return 0;
}

static int xmp_mknod(const char *fuse_path, mode_t mode, dev_t rdev)
{
	char *path = prefix_path(fuse_path);

	int res;

	/* On Linux this could just be 'mknod(path, mode, rdev)' but this
	   is more portable */
	if (S_ISREG(mode)) {
		res = open(path, O_CREAT | O_EXCL | O_WRONLY, mode);
		if (res >= 0)
			res = close(res);
	} else if (S_ISFIFO(mode))
		res = mkfifo(path, mode);
	else
		res = mknod(path, mode, rdev);
	if (res == -1)
		return -errno;

	return 0;
}

static int xmp_mkdir(const char *fuse_path, mode_t mode)
{
	char *path = prefix_path(fuse_path);

	int res;

	res = mkdir(path, mode);
	if (res == -1)
		return -errno;

	return 0;
}

static int xmp_unlink(const char *fuse_path)
{
	char *path = prefix_path(fuse_path);

	int res;

	res = unlink(path);
	if (res == -1)
		return -errno;

	return 0;
}

static int xmp_rmdir(const char *fuse_path)
{
	char *path = prefix_path(fuse_path);

	int res;

	res = rmdir(path);
	if (res == -1)
		return -errno;

	return 0;
}

static int xmp_symlink(const char *from, const char *to)
{
	int res;

	res = symlink(from, to);
	if (res == -1)
		return -errno;

	return 0;
}

static int xmp_rename(const char *from, const char *to)
{
	int res;

	res = rename(from, to);
	if (res == -1)
		return -errno;

	return 0;
}

static int xmp_link(const char *from, const char *to)
{
	int res;

	res = link(from, to);
	if (res == -1)
		return -errno;

	return 0;
}

static int xmp_chmod(const char *fuse_path, mode_t mode)
{
	char *path = prefix_path(fuse_path);

	int res;

	res = chmod(path, mode);
	if (res == -1)
		return -errno;

	return 0;
}

static int xmp_chown(const char *fuse_path, uid_t uid, gid_t gid)
{
	char *path = prefix_path(fuse_path);

	int res;

	res = lchown(path, uid, gid);
	if (res == -1)
		return -errno;

	return 0;
}

static int xmp_truncate(const char *fuse_path, off_t size)
{
	char *path = prefix_path(fuse_path);

	int res;

	//////
	// TBD: check if file is encrypted, if so unencrypt and then
	// truncate and then re-encrypt.
	//////

	res = truncate(path, size);
	if (res == -1)
		return -errno;

	return 0;
}

static int xmp_utimens(const char *fuse_path, const struct timespec ts[2])
{
	char *path = prefix_path(fuse_path);

	int res;
	struct timeval tv[2];

	tv[0].tv_sec = ts[0].tv_sec;
	tv[0].tv_usec = ts[0].tv_nsec / 1000;
	tv[1].tv_sec = ts[1].tv_sec;
	tv[1].tv_usec = ts[1].tv_nsec / 1000;

	res = utimes(path, tv);
	if (res == -1)
		return -errno;

	return 0;
}

static int xmp_open(const char *fuse_path, struct fuse_file_info *fi)
{
	char *path = prefix_path(fuse_path);
	int res;

	////we dont support O_TMPFILE, sanity check
	//Note: this constant is not defined anywhere!
	//if( (fi->flags & O_TMPFILE) ){
	//	fprintf(stderr, "%s: unsupported O_TMPFILE in open -- error\n", __FUNCTION__);
	//	return EINVAL;
	//}

	res = open(path, fi->flags);
	if (res == -1)
		return -errno;


	if( (fi->flags & O_CREAT) ){
		if (!add_encrypted_attr(path)){
			fprintf(stderr, "%s: failed to add xattr-encrypted\n", __FUNCTION__);
			return -errno;
		}
	}

	if( (fi->flags & O_CREAT) || (fi->flags & O_TRUNC)){
		if(!add_nonpaddedsize_attr(path, 0)){
			fprintf(stderr, "%s: failed to add xattr-nonpaddedsize.\n", __FUNCTION__);
			return -errno;
		}
	}

	close(res);
	return 0;
}


static int xmp_read(const char *fuse_path, char *buf, size_t size, off_t offset,
		    struct fuse_file_info *fi)
{
	FILE *path_ptr, *tmpf;
	char *path;
	int res, action;

	path = prefix_path(fuse_path);
	path_ptr = fopen(path, "r");
	tmpf = tmpfile();

	/* Either encrypt, or just move along. */
	action = is_encrypted(path) ? DECRYPT : PASS_THROUGH;
	if (do_crypt(path_ptr, tmpf, action, password) == 0)
		return -errno;

	/* Something went terribly wrong if this is the case. */
	if (path_ptr == NULL || tmpf == NULL)
		return -errno;

	fflush(tmpf);
	fseek(tmpf, offset, SEEK_SET);

	//////
	// TBD: only read "size" bytes and account for padding
	//////

	/* Read our tmpfile into the buffer. */
	res = fread(buf, 1, file_size(tmpf), tmpf);
	if (res == -1)
		res = -errno;

	fclose(tmpf);
	fclose(path_ptr);

	return res;
}


static int xmp_write(const char *fuse_path, const char *buf, size_t size,
		     off_t offset, struct fuse_file_info *fi)
{
	FILE *path_ptr, *tmpf;
	char *path;
	int res, action;
	int tmpf_descriptor;

	path = prefix_path(fuse_path);
	path_ptr = fopen(path, "r+");
	tmpf = tmpfile();
	tmpf_descriptor = fileno(tmpf);


	/* Something went terribly wrong if this is the case. */
	if (path_ptr == NULL || tmpf == NULL)
		return -errno;

	/* if the file to write to exists, read it into the tempfile */
	if (xmp_access(fuse_path, R_OK) == 0 && file_size(path_ptr) > 0) {
		action = is_encrypted(path) ? DECRYPT : PASS_THROUGH;
		if (do_crypt(path_ptr, tmpf, action, password) == 0)
			return --errno;

		rewind(path_ptr);
		rewind(tmpf);
	}

	/* Read our tmpfile into the buffer. */
	res = pwrite(tmpf_descriptor, buf, size, offset);
	if (res == -1)
		res = -errno;

	/* Either encrypt, or just move along. */
	action = is_encrypted(path) ? ENCRYPT : PASS_THROUGH;

	if (do_crypt(tmpf, path_ptr, action, password) == 0)
		return -errno;

	fclose(tmpf);
	fclose(path_ptr);

	return res;
}

static int xmp_statfs(const char *fuse_path, struct statvfs *stbuf)
{
	char *path = prefix_path(fuse_path);

	int res;
	//////
	// TBD: return non-padded size in stbuf->st_size
	//////

	res = statvfs(path, stbuf);
	if (res == -1)
		return -errno;

	return 0;
}

static int xmp_create(const char* fuse_path, mode_t mode,
		      struct fuse_file_info* fi)
{
	char *path = prefix_path(fuse_path);

	(void) fi;

	int res;
	res = creat(path, mode);

	if(res == -1) {
		fprintf(stderr, "xmp_create: failed to creat\n");
		return -errno;
	}

	close(res);

	if (!add_encrypted_attr(path)){
		fprintf(stderr, "%s: failed to add xattr-encrypted\n", __FUNCTION__);
		return -errno;
	}

	if(!add_nonpaddedsize_attr(path, 0)){
		fprintf(stderr, "%s: failed to add xattr-nonpaddedsize.\n", __FUNCTION__);
		return -errno;
	}


	return 0;
}


static int xmp_release(const char *fuse_path, struct fuse_file_info *fi)
{
	/* Just a stub.	 This method is optional and can safely be left
	   unimplemented */
	char *path = prefix_path(fuse_path);

	(void) path;
	(void) fi;
	return 0;
}

static int xmp_fsync(const char *fuse_path, int isdatasync,
		     struct fuse_file_info *fi)
{
	/* Just a stub.	 This method is optional and can safely be left
	   unimplemented */
	char *path = prefix_path(fuse_path);

	(void) path;
	(void) isdatasync;
	(void) fi;
	return 0;
}

#ifdef HAVE_SETXATTR
static int xmp_setxattr(const char *fuse_path, const char *name,
			const char *value, size_t size, int flags)
{
	char *path = prefix_path(fuse_path);

	int res = lsetxattr(path, name, value, size, flags);
	if (res == -1)
		return -errno;
	return 0;
}

static int xmp_getxattr(const char *fuse_path, const char *name, char *value,
			size_t size)
{
	char *path = prefix_path(fuse_path);

	int res = lgetxattr(path, name, value, size);
	if (res == -1)
		return -errno;
	return res;
}

static int xmp_listxattr(const char *fuse_path, char *list, size_t size)
{
	char *path = prefix_path(fuse_path);

	int res = llistxattr(path, list, size);
	if (res == -1)
		return -errno;
	return res;
}

static int xmp_removexattr(const char *fuse_path, const char *name)
{
	char *path = prefix_path(fuse_path);

	int res = lremovexattr(path, name);
	if (res == -1)
		return -errno;
	return 0;
}
#endif /* HAVE_SETXATTR */

static struct fuse_operations xmp_oper = {
	/* .opendir        = xmp_opendir, */
	.getattr	= xmp_getattr,
	.access		= xmp_access,
	.readlink	= xmp_readlink,
	.readdir	= xmp_readdir,
	.mknod		= xmp_mknod,
	.mkdir		= xmp_mkdir,
	.symlink	= xmp_symlink,
	.unlink		= xmp_unlink,
	.rmdir		= xmp_rmdir,
	.rename		= xmp_rename,
	.link		= xmp_link,
	.chmod		= xmp_chmod,
	.chown		= xmp_chown,
	.truncate	= xmp_truncate,
	.utimens	= xmp_utimens,
	.open		= xmp_open,
	.read		= xmp_read,
	.write		= xmp_write,
	.statfs		= xmp_statfs,
	.create		= xmp_create,
	.release	= xmp_release,
	.fsync		= xmp_fsync,
#ifdef HAVE_SETXATTR
	.setxattr	= xmp_setxattr,
	.getxattr	= xmp_getxattr,
	.listxattr	= xmp_listxattr,
	.removexattr	= xmp_removexattr,
#endif
};

int main(int argc, char *argv[])
{
	umask(0);

	/* ./pa5-encfs mir mnt -e password */
	if ((root_path = realpath(argv[argc - 4], NULL)) == NULL){
		fprintf(stderr, "Please enter a valid root directory name.\n");
		return EXIT_FAILURE;
	}

	if ((password = argv[argc - 1]) == NULL){
		fprintf(stderr, "Please enter an encryption password.\n");
		return EXIT_FAILURE;
	}

	argv[argc-4] = argv[argc-3];
	argv[argc-1] = NULL;
	argc -= 3;

	return fuse_main(argc, argv, &xmp_oper, NULL);
}
