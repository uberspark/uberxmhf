/** file PageData.h 
 * webSite Data Header
 *
 * Rev 1.0 JD 3-10-2009
 * Copyright Digital Shortcut Inc. (BSD licence) 2009 **/

#ifndef PAGEDATA_H
#define PAGEDATA_H


struct p_rec {
	int			offset;
	int			size;
	int			type;
};


extern struct p_rec page_info[];
extern	int   getPFileMax(void);


#endif
