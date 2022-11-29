/*
 * Copyright 2022 Peraton Labs Inc.
 *
 * This software was developed in work supported by the following U.S.
 * Government contracts:
 *
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
 * 
 */
 
#ifndef _FECBLOCK_H_
#define _FECBLOCK_H_

#include "common.h"
#include "packetinfo.h"

#define FECMAXBLOCKSIZE		256


/************************************************************************/
/*									*/
/*	data structures.						*/
/*									*/
/************************************************************************/

struct fecBlock {
    BOOLEAN complete;		/* 1 if all needed packets received.	*/
    int blockSeq;		/* flow sequence number of first packet	*/
				/* and all parity packets in block.	*/
    int k;			/* number of source packets.		*/
    int h;			/* number of parity packets.		*/
    struct packetinfo *packets[FECMAXBLOCKSIZE];
				/* storage for packetinfo structures.	*/		
    int packetCount;		/* number of packets in packet list.	*/
    //double timeout;		/* last arrival time plus fixed timeout.*/
    unsigned int timeout; //JOSH - last arrival time plus fixed timeout

    struct fecBlock *prev;
    struct fecBlock *next;
};


/************************************************************************/
/*									*/
/*	global variables.						*/
/*									*/
/************************************************************************/


/************************************************************************/
/*									*/
/*	fecBlock_new() - create and initialize a new fecBlock structure.*/
/*									*/
/************************************************************************/

struct fecBlock *fecBlock_new();


/************************************************************************/
/*									*/
/*	fecBlock_free() - free the given fecBlock structure.		*/
/*									*/
/************************************************************************/

void fecBlock_free(struct fecBlock *fecBlock_p);


/************************************************************************/
/*									*/
/*	fecBlock_log() - 						*/
/*									*/
/************************************************************************/

void fecBlock_log(zlog_category_t *zc_blackFec, struct fecBlock *fecblock);


#endif
