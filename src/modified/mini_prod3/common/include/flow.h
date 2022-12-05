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

#ifndef _FLOW_H_
#define _FLOW_H_

#include "common.h"		

#include "flowTuple.h"
#include "composition.h"
#include "packetinfo.h"

#include "fecBlock.h"

#define HASHSIZE	65536


/************************************************************************/
/*									*/
/*	data structures.						*/
/*									*/
/************************************************************************/

struct flow {

  /* information uniquely identifying flow.				*/
  struct flowTuple *flowtuple;
  u_int32_t flowhash;		/* based on flowtuple.  not unique but	*/
				/* speeds up lookup.			*/
    u_int32_t flowid;		/* ID of flow (for internal use).	*/
 
  struct composition *comp;

  u_int32_t flow_seq;           /* flow sequence number of last packet  */
                                /* for this flow. used by FEC           */
    /* common FEC attributes.						*/
    //    u_int8_t fec_type;		/* current FEC type (k, h).		*/
    u_int8_t fec_k;		/* number of source packets in FEC	*/
				/* block.				*/
    u_int8_t fec_h;		/* number of parity packets in FEC	*/
				/* block.				*/
    u_int8_t fec_n;		/* total packets of FEC block.		*/

    /* red (source) side FEC attributes.				*/
    struct packetinfo *fecBlockHead;
				/* head of packet list for FEC block.	*/
    struct packetinfo *fecBlockTail;
    				/* tail of packet list for FEC block.	*/
    int fecPacketCount;		/* number of packets in packet list.	*/
    unsigned char **packetptrs;	/* buffers for core FEC code.		*/
				/* pointers to packet data for FEC	*/
				/* algorithm.				*/
    int *packetsizes;		/* sizes of buffers for core FEC code.	*/
				/* sizes of packet data for FEC		*/
				/* algorithm.				*/
    char *pstat;		/* status of buffers for core FEC code.	*/
				/* control/status bytes for FEC		*/
				/* algorithm.				*/

    /* black (destination) side FEC attributes.				*/
    struct fecBlock *blockListHead;
				/* head of block list.  Oldest block.	*/
    struct fecBlock *blockListTail;
				/* tail of block list.  Newest/current	*/
				/* block.				*/
    unsigned char **bpacketptrs;/* buffers for core FEC code.		*/
				/* pointers to packet data for FEC	*/
				/* algorithm.				*/
    int *bpacketsizes;		/* sizes of buffers for core FEC code.	*/
				/* sizes of packet data for FEC		*/
				/* algorithm.				*/
    char *bpstat;		/* status of buffers for core FEC code.	*/
				/* control/status bytes for FEC		*/
				/* algorithm.				*/
    u_int32_t time; //JOSH - for recording the current time
    
  struct flow* next;
  char tuplestr_buff[128];	/* written when flow_add() called,	*/
				/* read by multiple threads.		*/
};

struct flowtable_bucket_t  {
  pthread_mutex_t lock;
  struct flow *flows;
};


/************************************************************************/
/*									*/
/*	global variables.						*/
/*									*/
/************************************************************************/


/************************************************************************/
/*									*/
/*	flow_new() - create and initialize a new flow structure.	*/
/*									*/
/************************************************************************/

struct flow *flow_new(void);


/************************************************************************/
/*									*/
/*	flow_free() - free the given flow structure.		        */
/*									*/
/************************************************************************/

void flow_free(struct flow *flow_p);


/************************************************************************/
/*									*/
/*	flow_add() - add given flow structure to the	                */
/*		flow list.					        */
/*									*/
/************************************************************************/

void flow_add(struct flow *flow_p);


/************************************************************************/
/*									*/
/*	flow_remove() - remove the given flow structure from the flow	*/
/*		list.  Does not free the flow structure.		*/
/*									*/
/************************************************************************/

void flow_remove(struct flow *f);


/************************************************************************/
/*									*/
/*	flow_findByHash() - find the flow matching the given hash and	*/
/*		flow tuple.						*/
/*									*/
/*		Note: assume that flow table has already been		*/
/*		initialized.  Otherwise couldn't have a hash.		*/
/*									*/
/************************************************************************/

struct flow *flow_findByHash(struct flowTuple *tuple, u_int32_t hash);


/************************************************************************/
/*									*/
/*	flow_find() - find the flow matching the given flow tuple.	*/
/*									*/
/************************************************************************/

struct flow *flow_find(struct flowTuple *tuple);


#endif
