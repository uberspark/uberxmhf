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

/* config options */
struct cfg_option {
    char *domain;
    char *section;
    char *entry;
};    
struct cfg_cmdline {
    char               letter;
    char               *cmdline;
    struct cfg_option  option;
    char               *value;
    char               *desc;
    int                needsarg:1;
    int                yesno:1;
};
void   cfg_parse_cmdline(int *argc, char **argv, struct cfg_cmdline *opt);
void   cfg_help_cmdline(FILE *fp, struct cfg_cmdline *opt, int w1, int w2, int w3);

/* file I/O */
int    cfg_parse_file(char *dname, char *filename);
int    cfg_write_file(char *dname, char *filename);

/* update */
void   cfg_set_str(char *dname, char *sname, char *ename,
		   const char *value);
void   cfg_set_int(char *dname, char *sname, char *ename, int value);
void   cfg_set_bool(char *dname, char *sname, char *ename, int value);

void   cfg_del_section(char *dname, char *sname);
void   cfg_del_entry(char *dname, char *sname, char *ename);

/* search */
char*  cfg_sections_first(char *dname);
char*  cfg_sections_next(char *dname, char *current);
char*  cfg_sections_prev(char *dname, char *current);
char*  cfg_sections_index(char *dname, int i);
unsigned int cfg_sections_count(char *dname);

char*  cfg_entries_first(char *dname, char *sname);
char*  cfg_entries_next(char *dname, char *sname, char *current);
char*  cfg_entries_prev(char *dname, char *sname, char *current);
char*  cfg_entries_index(char *dname, char *sname, int i);
unsigned int cfg_entries_count(char *dname, char *sname);

#define cfg_sections_for_each(dname, item) \
	for (item = cfg_sections_first(dname); NULL != item; \
	     item = cfg_sections_next(dname,item))

char*  cfg_search(char *dname, char *sname, char *ename, char *value);

/* read */
char*  cfg_get_str(char *dname, char *sname, char *ename);
unsigned int cfg_get_int(char *dname, char *sname,
			 char *ename, unsigned int def);
signed int  cfg_get_signed_int(char *dname, char *sname,
			       char *ename, signed int def);
float  cfg_get_float(char *dname, char *sname, char *ename, float def);
int    cfg_get_bool(char *dname, char *sname, char *ename, int def);

unsigned int    cfg_get_sflags(char *dname, char *sname);
unsigned int    cfg_get_eflags(char *dname, char *sname, char *ename);
unsigned int    cfg_set_sflags(char *dname, char *sname,
			       unsigned int mask, unsigned int bits);
unsigned int    cfg_set_eflags(char *dname, char *sname, char *ename,
			       unsigned int mask, unsigned int bits);
