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
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in
 * the documentation and/or other materials provided with the
 * distribution.
 *
 * Neither the names of Carnegie Mellon or VDG Inc, nor the names of
 * its contributors may be used to endorse or promote products derived
 * from this software without specific prior written permission.
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

//portable executable file format declarations/constants
//author: amit vasudevan (amitvasudevan@acm.org)

#ifndef __EXE_PE_H__
#define __EXE_PE_H__

#define IMAGE_DOS_SIGNATURE                 0x5A4D      // MZ
#define IMAGE_NT_SIGNATURE                  0x00004550  // PE00

//legacy DOS .EXE header format
typedef struct  {    
    u16   e_magic;                    
    u16   e_cblp;                     
    u16   e_cp;                       
    u16   e_crlc;                     
    u16   e_cparhdr;                  
    u16   e_minalloc;                 
    u16   e_maxalloc;                 
    u16   e_ss;                       
    u16   e_sp;                       
    u16   e_csum;                     
    u16   e_ip;                       
    u16   e_cs;                       
    u16   e_lfarlc;                   
    u16   e_ovno;                     
    u16   e_res[4];                   
    u16   e_oemid;                    
    u16   e_oeminfo;                  
    u16   e_res2[10];                 
    u32   e_lfanew;                   
} __attribute__((packed)) image_dos_header_t ;

// NT file header format.
typedef struct  {
    u16    Machine;
    u16    NumberOfSections;
    u32   TimeDateStamp;
    u32   PointerToSymbolTable;
    u32   NumberOfSymbols;
    u16    SizeOfOptionalHeader;
    u16    Characteristics;
} __attribute__((packed)) image_file_header_t;

typedef struct  {
    u32   VirtualAddress;
    u32   Size;
} __attribute__((packed)) image_data_directory_t;

#define IMAGE_NUMBEROF_DIRECTORY_ENTRIES    16

// NT Optional header format.
typedef struct {
    u16    Magic;
    u8    MajorLinkerVersion;
    u8    MinorLinkerVersion;
    u32   SizeOfCode;
    u32   SizeOfInitializedData;
    u32   SizeOfUninitializedData;
    u32   AddressOfEntryPoint;
    u32   BaseOfCode;
    u32   BaseOfData;

    u32   ImageBase;
    u32   SectionAlignment;
    u32   FileAlignment;
    u16    MajorOperatingSystemVersion;
    u16    MinorOperatingSystemVersion;
    u16    MajorImageVersion;
    u16    MinorImageVersion;
    u16    MajorSubsystemVersion;
    u16    MinorSubsystemVersion;
    u32   Win32VersionValue;
    u32   SizeOfImage;
    u32   SizeOfHeaders;
    u32   CheckSum;
    u16    Subsystem;
    u16    DllCharacteristics;
    u32   SizeOfStackReserve;
    u32   SizeOfStackCommit;
    u32   SizeOfHeapReserve;
    u32   SizeOfHeapCommit;
    u32   LoaderFlags;
    u32   NumberOfRvaAndSizes;
    image_data_directory_t DataDirectory[IMAGE_NUMBEROF_DIRECTORY_ENTRIES];
} __attribute__((packed)) image_optional_header32_t;


typedef struct  {
    u32 Signature;
    image_file_header_t FileHeader;
    image_optional_header32_t OptionalHeader;
} __attribute__((packed)) image_nt_headers32_t;


// Directory Entries
#define IMAGE_DIRECTORY_ENTRY_BASERELOC       5   // Base Relocation Table

// Based relocation format.
typedef struct  {
    u32   VirtualAddress;
    u32   SizeOfBlock;
    u16    TypeOffset[1];
} __attribute__((packed)) image_base_relocation_t;

#endif //__EXE_PE_H__
