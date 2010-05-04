/** @file
 * Util.c
 */
/* copyright ©2008, 2008 #001142 */
#include <stdlib.h>
#include <string.h>

extern	int 		printf(const char *format, ...);


void		delay(unsigned long d);
char*		itoa(unsigned int num, char* buf, int radix );
int			hex2int(char ch);
int			findstr(char* str1, char* str2);


void		delay(unsigned long d)
{
	for(; d; --d)
	{
		asm volatile ("nop");
	}
}

char*		itoa(unsigned int num, char* buf, int radix )
{
	char *p;
	buf[0]=buf[1]=buf[2]=buf[3]=buf[4]=buf[5]='0';
	buf[6] = '\0';		

	if ( num > 0 ) {
		p = &buf[5];
		while (num != 0) {
			*p-- = "0123456789abcdef"[num % radix];
			num /= radix;
		}
	}
	p = &buf[0];
	return p;
}

int		hex2int(char ch)
{
	if ( (ch>='0')&&(ch<='9') )
		return ch - '0';
		
	if ( (ch>='A')&&(ch<='F') )
		return ch - 'A' + 10;
		
	return -1;
}

int		findstr(char* str1, char* str2)
{
	int i, j, k, k1;
	int l1, l2;

	i = j = k = k1 = 0;
	l1 = strlen(str1);
	l2 = strlen(str2);
	// printf("\n\rFindStr l1=%d l2=%d", l1, l2);
	while (i<=l1)  {
		if (str1[i]==str2[j])  {
			i++;
			j++;
			k1=1;
			if (j==l2)  {
				k=1;
				break;
			}
		} else  {
			if (k1==1)  {
				j=0;
				k1=0;
			} else
				i++;
		}
	}

	if (k==1)  {
     //printf("\n\rStr %s Found i=%d j=%d Indx=%d", str2, i, j, (i-l2));
     return (i-l2);
  }  else  {
     //printf("\n\rStr not Found");
     return -1;
  }
}

