#ifndef SECTIONS_H
#define SECTIONS_H

/* The linker script ensures that these symbols point to beginnings
 * and ends of the named sections. The _end symbols point to the address
 * after the last byte of the section. e.g., the size of a section is
 * __SECTIONNAME_end - __SECTIONNAME_start
 */
extern unsigned int __scode_start, __scode_end;
extern unsigned int __stext_start, __stext_end;
extern unsigned int __sdata_start, __sdata_end;

#endif
