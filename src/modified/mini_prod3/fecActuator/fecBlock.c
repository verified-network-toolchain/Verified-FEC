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

#include "fecBlock.h"

extern zlog_category_t *zc_blackFec;


/************************************************************************/
/*									*/
/*	global variables.						*/
/*									*/
/************************************************************************/


/************************************************************************/
/*									*/
/*	module-wide variables - global variables used only in the	*/
/*		current file.						*/
/*									*/
/************************************************************************/


/************************************************************************/
/*									*/
/*	fecBlock_new() - create and initialize a new fecBlock structure.	*/
/*									*/
/************************************************************************/

struct fecBlock *fecBlock_new()
{
    struct fecBlock *fecblock;

    fecblock = (struct fecBlock *) calloc(1, sizeof(struct fecBlock));

    return fecblock;
}


/************************************************************************/
/*									*/
/*	fecBlock_free() - free the given fecBlock structure.		*/
/*									*/
/************************************************************************/

void fecBlock_free(struct fecBlock *fecblock)
{
    int i;			/* loop counter.			*/

    /* free any packet information stored in the block.			*/
    for (i = 0; i < fecblock->packetCount; i++) {
	if (fecblock->packets[i] != 0) {
	    zlog_debug(zc_blackFec, "fecBlock_free freeing pinfo %p with pdata %p.\n",
		       fecblock->packets[i], fecblock->packets[i]->packetdata);

	    if( fecblock->packets[i]->isParity )
	      {
		// packetinfo_auditAdd(fecblock->packets[i]);
		// zlog_info(zc_blackFec, "Sending parity packetinfo %p to aggregator: %d/%d",
		//		  fecblock->packets[i], fecblock->packets[i]->inLinkSeq, fecblock->packets[i]->outLinkSeq);
	    // in immediate capture reporting, we're suppressing this sender 2 aggregator, but
	    // we then have to free the pinfo memory
	    packetinfo_free(fecblock->packets[i]);

		// fistq_enqueue_pinfo(sender2aggregator, fecblock->packets[i], FISTQ_FLUSH);
	      }
	    else
	      {
		zlog_debug(zc_blackFec, "Freeing original packetinfo:");
			     //  fecblock->packets[i]->inLinkSeq, fecblock->packets[i]->outLinkSeq);
		  packetinfo_free(fecblock->packets[i]);
	      }
	    fecblock->packets[i] = 0;
	}
    }

    /* free the block structure.					*/
    free(fecblock);

    return;
}


/************************************************************************/
/*									*/
/*	fecBlock_log() - 						*/
/*									*/
/************************************************************************/

void fecBlock_log(zlog_category_t *zc_blackFec, struct fecBlock *fecblock)
{
    zlog_debug(zc_blackFec, "fecblock=%p", fecblock);
    if (fecblock == 0) {
	return;
    }
    zlog_debug(zc_blackFec, "\tcomplete=%d, blockSeq=%d, k=%d, h=%d",
	       fecblock->complete, fecblock->blockSeq,
	       fecblock->k, fecblock->h);
    zlog_debug(zc_blackFec, "\tpacketCount=%d, timeout=%.06f",
	       fecblock->packetCount, fecblock->timeout);
    zlog_debug(zc_blackFec, "\tprev=%p, next=%p",
	       fecblock->prev, fecblock->next);
    
    return;
}
