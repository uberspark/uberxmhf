/*
	pa5-encfs encrypted filesystem test application

	author: amit vasudevan (amitvasudevan@acm.org)
*/

#ifndef __PA5ENCFS_H__
#define __PA5ENCFS_H__

#define UAPP_PA5ENCFS_FUNCTION_START	0x30
#define UAPP_PA5ENCFS_FUNCTION_ENCRYPT	0x31
#define UAPP_PA5ENCFS_FUNCTION_DECRYPT	0x32
#define UAPP_PA5ENCFS_FUNCTION_DONE		0x33


#define BLOCKSIZE 1024
#define FAILURE 0
#define SUCCESS 1

#define ENCRYPT 1
#define DECRYPT 0
#define PASS_THROUGH (-1)


#ifndef __ASSEMBLY__

typedef struct {
    unsigned char inbuf[BLOCKSIZE];
    int inlen;
    unsigned char outbuf[BLOCKSIZE];
    int outlen;
    int writelen;
    int result;
}pa5encfs_param_t;


#endif // __ASSEMBLY__



#endif //__PA5ENCFS_H__
