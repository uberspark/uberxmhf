#ifndef _STDARG_H
#define	_STDARG_H

typedef void *va_list;
#define	va_start(list, name) (void) (list = (void *)((char *)&name + \
	((sizeof (name) + (sizeof (int) - 1)) & ~(sizeof (int) - 1))))
#define	va_arg(list, mode) ((mode *)(list = (char *)list + sizeof (mode)))[-1]

#define	va_end(list) (void)0


#endif	/* _STDARG_H */
