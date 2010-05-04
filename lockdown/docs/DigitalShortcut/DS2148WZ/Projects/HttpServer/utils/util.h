/*! \file VCOM.h \brief VCOM Support for LPC2100. */
//*****************************************************************************
//
// File Name	: 'util.h'
// Title		: General Utilities
// Author		: Digital Shortcut - Copyright (C) 2008
// Created		: 2008.12.05
// Revised		: 
// Version		: 0.1
// Target MCU	: ARM processors
// Editor Tabs	: 2
//
//*****************************************************************************

#ifndef UTIL_H
#define UTIL_H


extern	void	delay(unsigned long d);
extern	char* itoa(unsigned int num, char* buf, int radix );
extern	int	hex2int(char ch);
extern	int	findstr(char* str1, char* str2);

#endif
