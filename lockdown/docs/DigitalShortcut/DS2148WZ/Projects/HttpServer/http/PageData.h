/*! \file PageData.h                                                         */
//*****************************************************************************
//
// File Name	: 'PageData.h'
// Title		: Timer Support Library for LPC2100
// Author		: JD - Copyright (C) 2008
// Created		: 2008.05.05
// Revised		: 2008.07.12
// Version		: 0.1
// Target MCU	: ARM processors
// Editor Tabs	: 2
//
// NOTE: This code is currently below version 1.0, and therefore is considered
// to be lacking in some functionality or documentation, or may not be fully
// tested.  Nonetheless, you can expect most functions to work.
//
// This code is distributed under the GNU Public License
//		which can be found at http://www.gnu.org/licenses/gpl.txt
//
//*****************************************************************************

#ifndef PAGEDATA_H
#define PAGEDATA_H



struct p_rec {
	int						offset;
	unsigned int	size;
	int						type;
};


extern struct p_rec page_info[];


#endif
