#include <types.h>
#include <print.h>
#include <target.h>
#include <str.h>

#define COLS     80
#define ROWS     25
#define ATTR     7

char *vidmem=(char *)0xB8000;
unsigned int vid_x, vid_y;

void vgamem_clrscr(void){
  memset((char *)vidmem, 0, COLS * ROWS * 2);
  vid_x = vid_y = 0;
}


void vgamem_newln(void){
    vid_x = 0;
    vid_y++;

    if (vid_y >= ROWS){
        vid_y = ROWS-1;
        memcpy((char*)vidmem,(char*)vidmem + 2*COLS, (ROWS-1)*2*COLS);
        memcpy((char*)vidmem + (ROWS-1)*2*COLS, 0, 2*COLS);
    }
}

void vgamem_putchar(int c)
{
    if ( c == '\n' )
        vgamem_newln();
    else
    {
        vidmem[(vid_x + vid_y * COLS) * 2]  = c & 0xFF;
        vidmem[(vid_x + vid_y * COLS) * 2 + 1] = ATTR;
        if ( ++vid_x >= COLS ) vgamem_newln();
    }
}

void putstr(const char *str)
{
    int c;

    while ( (c = *str++) != '\0' )
        vgamem_putchar(c);
}


