/*
 * FEC.H
 * Forward Erasure Correction encoder and decoder
 *
 * Copyright 2021 Peraton Labs Inc.
 *
 * Originally developed by A. McAuley, Peraton Labs Inc.
 * 
 * This software was developed in work supported by the following U.S.
 * Government contracts:
 *
 * W15P7T-05-C-R402
 * HR0011-15-C-0098
 * HR0011-20-C-0160
 *
 * Any opinions, findings and conclusions or recommendations expressed in
 * this material are those of the author(s) and do not necessarily reflect
 * the views, either expressed or implied, of the U.S. Government.

 * This software embodies U.S. Patent 5,115,436
 *
 * DoD Distribution Statement A
 * Approved for Public Release, Distribution Unlimited
 * 
 * DISTAR Case 34797, cleared June 21, 2021.
 * 
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 */

#ifndef _FEC_H
#define _FEC_H

// $Revision: 1.8 $
// $Date: 2007/08/02 18:51:56 $

/***************************************************************************/
/* Definitions                                                             */
/***************************************************************************/

/** fec options **/

//#define  FEC_SMALL                 /* use 3-bit symbols */

#ifdef FEC_SMALL

#define         FEC_M		(3)             /* symbol size */
#define		FEC_MAX_H	(3)		/* MAX of h parities */
#define		FEC_MAX_COLS	(4)	        /* Max symbols/packet (c) */
#define         FEC_N           (8)             /* Max k+h = 2^m */

#else						/* default size symbols */

#define         FEC_M		(8)             /* symbol size */
//#define		FEC_MAX_H	(32)            /* MAX of h parities */
#define		FEC_MAX_H	(128)            /* MAX of h parities */
					/* increased.  bss, 8/14/2008	*/
//#define	FEC_MAX_COLS	(1600)		/* Max symbols/packet (c) */
#define	FEC_MAX_COLS	(16000)		/* Max symbols/packet (c) */
					/* increased.  bss, 4/12/2006	*/
//#define	FEC_MAX_COLS	(65536)			/* Max symbols/packet (c) */
					/* increased.  bss, 9/4/2018.	*/

#define         FEC_N           (256)           /* Max k+h = 2^m */

#endif

/** data flags **/

#define		FEC_FLAG_KNOWN  (0)	/* PFV (see above) */
#define		FEC_FLAG_WANTED	(1)	/* PFV (see above) */


/***************************************************************************/
/* Function prototypes                                                     */
/***************************************************************************/

void rse_init(void);

// If h>0, then this function appends h parity packets to the k data packets
// in pdata.  plen is an array of of the lengths of the data packets (with
// headers & shim).  c is max_i(plen).  pstat is a flag, initially FEC_FLAG_KNOWN.
//int rse_code(int k, int h, int c, unsigned char **pdata, int *plen, char *pstat);
int fec_blk_encode(int k, int h, int c, unsigned char **pdata, int *plen, char *pstat);
int fec_blk_decode(int k, int c, unsigned char **pdata, int *plen, char *pstat);


void rse_code_print(int k, int h, int c, unsigned char **pdata, int *plen, char *pstat);

#endif    //_FEC_H
