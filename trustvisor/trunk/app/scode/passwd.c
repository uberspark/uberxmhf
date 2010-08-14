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




//#include "passwd.h"
int junk[]={2,0,1,0};

#if 0                                                                                                      
int readpass(void)
{
  int i = 0;

  int j = 0;

  for (i = 0; i < 1000; i++)
    j += i;


  return 0;
} // end of readpass(void)  
#endif
//function int readpass(void)                                                                                                                                 
//todo: read password input and display it in terminal                                                                                                        
#if 0
int barbar2(int b)
{
	int i;
	for( i=0 ; i<20 ; i++ )  {
		b+=i;
	}
	return b;
}


int foo2(int b)
{
	do {
		b++;
	} while (b%20==0);
	b=foofoo2(b);
	b=barbar2(b);
	return b;
}

int foofoo2(int a)
{
	a=a*a;
	a=a/4;
	a=a+123;
	return a;
}
int barbar3(int b)
{
	int i;
	for( i=0 ; i<20 ; i++ )  {
		b+=i;
	}
	return b;
}


int foo3(int b)
{
	do {
		b++;
	} while (b%20==0);
	b=foofoo2(b);
	b=barbar2(b);
	return b;
}

int foofoo3(int a)
{
	a=a*a;
	a=a/4;
	a=a+123;
	return a;
}
#endif

#if 0
int password(void)
{
  struct termios ts, ots;
  char passbuf[100];

  //get and save termios settings                                                                                                                             
  tcgetattr(STDIN_FILENO, &ts);
  ots = ts;
  //change termios settings                                                                                                                                   
  ts.c_lflag &= ~ECHO;
  ts.c_lflag |= ECHONL;
  tcsetattr(STDIN_FILENO, TCSAFLUSH, &ts);
  //check settings                                                                                                                                            
  tcgetattr(STDIN_FILENO, &ts);
  if(ts.c_lflag & ECHO){
    fprintf(stderr, "Fail to trun off echo\n");
    tcsetattr(STDIN_FILENO, TCSANOW, &ots);
    exit(1);
  }
  //read and print password                                                                                                                                   
  printf("Please enter password:");
  fflush(stdout);
  fgets(passbuf, sizeof(passbuf), stdin);
  printf("read password: %s", passbuf);
  //reset the former termios settings                                                                                                                         
  tcsetattr(STDIN_FILENO, TCSANOW, &ots);

  return 0;
} // end of readpass(void)   
#endif
