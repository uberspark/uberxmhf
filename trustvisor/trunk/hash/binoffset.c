/*
 * @XMHF_LICENSE_HEADER_START@
 *
 * eXtensible, Modular Hypervisor Framework (XMHF)
 * Copyright (c) 2009-2012 Carnegie Mellon University
 * Copyright (c) 2010-2012 VDG Inc.
 * All Rights Reserved.
 *
 * Developed by: XMHF Team
 *               Carnegie Mellon University / CyLab
 *               VDG Inc.
 *               http://xmhf.org
 *
 * This file is part of the EMHF historical reference
 * codebase, and is released under the terms of the
 * GNU General Public License (GPL) version 2.
 * Please see the LICENSE file for details.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND
 * CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES,
 * INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS
 * BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED
 * TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
 * ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR
 * TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF
 * THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * @XMHF_LICENSE_HEADER_END@
 */

/***************************************************************************
 * binoffset.c
 * (C) 2002 Randy Dunlap <rdunlap@xenotime.net>

#   This program is free software; you can redistribute it and/or modify
#   it under the terms of the GNU General Public License as published by
#   the Free Software Foundation; either version 2 of the License, or
#   (at your option) any later version.
#
#   This program is distributed in the hope that it will be useful,
#   but WITHOUT ANY WARRANTY; without even the implied warranty of
#   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#   GNU General Public License for more details.
#
#   You should have received a copy of the GNU General Public License
#   along with this program; if not, write to the Free Software
#   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

# binoffset.c:
# - searches a (binary) file for a specified (binary) pattern
# - returns the offset of the located pattern or ~0 if not found
# - exits with exit status 0 normally or non-0 if pattern is not found
#   or any other error occurs.

****************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/mman.h>

#define VERSION		"0.1"
#define BUF_SIZE	(16 * 1024)
#define PAT_SIZE	100

char		*progname;
char		*inputname;
int		inputfd;
unsigned int	bix;			/* buf index */
unsigned char	patterns [PAT_SIZE] = {0}; /* byte-sized pattern array */
int		pat_len;		/* actual number of pattern bytes */
unsigned char	*madr;			/* mmap address */
size_t		filesize;
int		num_matches = 0;
off_t		firstloc = 0;

void usage (void)
{
	fprintf (stderr, "%s ver. %s\n", progname, VERSION);
	fprintf (stderr, "usage:  %s filename pattern_bytes\n",
			progname);
	fprintf (stderr, "        [prints location of pattern_bytes in file]\n");
	exit (1);
}

void get_pattern (int pat_count, char *pats [])
{
	int ix, err, tmp;

#ifdef DEBUG
	fprintf (stderr,"get_pattern: count = %d\n", pat_count);
	for (ix = 0; ix < pat_count; ix++)
		fprintf (stderr, "  pat # %d:  [%s]\n", ix, pats[ix]);
#endif

	for (ix = 0; ix < pat_count; ix++) {
		tmp = 0;
		err = sscanf (pats[ix], "%5i", &tmp);
		if (err != 1 || tmp > 0xff) {
			fprintf (stderr, "pattern or value error in pattern # %d [%s]\n",
					ix, pats[ix]);
			usage ();
		}
		patterns [ix] = tmp;
	}
	pat_len = pat_count;
}

void search_pattern (void)
{
	for (bix = 0; bix < filesize; bix++) {
		if (madr[bix] == patterns[0]) {
			if (memcmp (&madr[bix], patterns, pat_len) == 0) {
				if (num_matches == 0)
					firstloc = bix;
				num_matches++;
			}
		}
	}
}

#ifdef NOTDEF
size_t get_filesize (int fd)
{
	off_t end_off = lseek (fd, 0, SEEK_END);
	lseek (fd, 0, SEEK_SET);
	return (size_t) end_off;
}
#endif

size_t get_filesize (int fd)
{
	int err;
	struct stat stat;

	err = fstat (fd, &stat);
	fprintf (stderr, "filesize: %ld\n", err < 0 ? (long)err : stat.st_size);
	if (err < 0)
		return err;
	return (size_t) stat.st_size;
}

int main (int argc, char *argv [])
{
	progname = argv[0];

	if (argc < 3)
		usage ();

	get_pattern (argc - 2, argv + 2);

	inputname = argv[1];

	inputfd = open (inputname, O_RDONLY);
	if (inputfd == -1) {
		fprintf (stderr, "%s: cannot open '%s'\n",
				progname, inputname);
		exit (3);
	}

	filesize = get_filesize (inputfd);

	madr = mmap (0, filesize, PROT_READ, MAP_PRIVATE, inputfd, 0);
	if (madr == MAP_FAILED) {
		fprintf (stderr, "mmap error = %d\n", errno);
		close (inputfd);
		exit (4);
	}

	search_pattern ();

	if (munmap (madr, filesize))
		fprintf (stderr, "munmap error = %d\n", errno);

	if (close (inputfd))
		fprintf (stderr, "%s: error %d closing '%s'\n",
				progname, errno, inputname);

	fprintf (stderr, "number of pattern matches = %d\n", num_matches);
	if (num_matches == 0)
		firstloc = ~0;
	printf ("%ld\n", firstloc);
	fprintf (stderr, "%ld\n", firstloc);

	exit (num_matches ? 0 : 2);
}

/* end binoffset.c */
