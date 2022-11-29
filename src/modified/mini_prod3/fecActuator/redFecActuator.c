/*
 * redFecActuator.c
 * Forward Erasure Correction actuator - red side
 *
 * Copyright 2022 Peraton Labs Inc.
 *
 * Originally developed by B. Siegell, Peraton Labs Inc.
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

#include "common.h"
#include "pipework.h"
#include "fecBlock.h"
#include "fecCommon.h"
#include "fecParams.h"
#include "fec.h"
#include "flow.h"
#include "packetinfo.h"
#include "redFecActuator.h"

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

extern zlog_category_t *zc_redFec;


/************************************************************************/
/*									*/
/*	redFecActuator_init() - initialize.				*/
/*									*/
/************************************************************************/

void redFecActuator_init()
{

    /* initialize the FEC algorithm.				*/
    rse_init();

    return;
}



/************************************************************************/
/*									*/
/*	redFecActuator_generateParity() - generate the parity packets	*/
/*		for the current FEC block.  If a packetinfo structure	*/
/*		is specified, use it's packetdata as the last source	*/
/*		packet.							*/
/*									*/
/*		k = source packets					*/
/*		h = parity packets					*/
/*		n = k + h						*/
/*									*/
/************************************************************************/

struct packetinfo *redFecActuator_generateParity(struct flow *f,
						 struct packetinfo *pinfo)
{
    //    static unsigned char **packetptrs = 0;
    //    static int *packetsizes = 0;
    //    static char *pstat = 0;
    int maxn = FECMAXBLOCKSIZE;	/* may not be constant in future.	*/

    struct packetinfo *pinfolist = pinfo;
    struct packetinfo *pinfotail = pinfo;

    int pindex;			/* index into packet arrays.		*/
    struct packetinfo *p;	/* pointer into list of packetinfos.	*/
    struct packetinfo *pnext;	/* p's next pointer.			*/
    struct packetinfo *base_pinfo;
				/* packetinfo structure on which parity	*/
    				/* packets are based.			*/
    u_int32_t maxlength;	/* maximum source packet length.	*/
    struct ip *ipheader;	/* pointer to ip header.		*/
    int iphl;			/* length of ip header.			*/
    unsigned char *bufptr;	/* pointer into packetdata buffer.	*/
    int paritySeq;		/* parity sequence number - set to same	*/
				/* value as first source packet		*/
				/* sequence number.			*/    

    zlog_debug(zc_redFec, "redFecActuator_generateParity(%p, %p)",
	       f, pinfo);

    /* make sure no stray pointer.		*/
    if (pinfo != 0) {
	pinfo->next = 0;
    }

    /* allocate initial arrays for storing packet pointers.		*/
    if (f->packetsizes == 0) {
	f->packetptrs
	    = (unsigned char **) calloc(sizeof(unsigned char *), maxn);
	f->packetsizes = (int *) calloc(sizeof(int), maxn);
	f->pstat = (char *) calloc(sizeof(char), maxn);
    }

    assert(f->fec_n <= maxn);

    /* increase array sizes if needed.  Not efficient, but rare.	*/
    /*    while (f->fec_n > maxn) {
	maxn *= 2;
	packetptrs = (unsigned char **) realloc(packetptrs,
						maxn * sizeof(unsigned char *));
	packetsizes = (int *) realloc(packetsizes,
				      maxn * sizeof(int));
	pstat = (char *) realloc(pstat, maxn * sizeof(char));
	}*/

    memset(f->packetptrs, 0, maxn * sizeof(unsigned char *));
    memset(f->packetsizes, 0, maxn * sizeof(int));
    memset(f->pstat, 0, maxn);

    /* construct the parameters for the fec algorithm.  If a block is	*/
    /* short, then the remaining source packets will have sizes of	*/
    /* zero and won't have allocated memory.				*/
    pindex = 0;
    maxlength = 0;

    /* for k = 1, pinfo is the first packet in the block.  Otherwise	*/
    /* the first packet is the first stored packet.			*/
    if (f->fec_k == 1) {
      paritySeq = pinfo->flow_seq;
    }
    else {
	/* save for parity packets.					*/
      paritySeq = f->fecBlockHead->flow_seq;
    }

    /* set up the source packet data.					*/
    for (p = f->fecBlockHead; p != 0; p = p->next) {
	p->blockIndex = pindex;
	p->isParity = 0;
	//	f->packetptrs[pindex] = p->packetdata;
	f->packetptrs[pindex]
	    = calloc(p->length, sizeof(unsigned char));
	memcpy(f->packetptrs[pindex], p->packetdata, p->length);
	f->packetsizes[pindex] = p->length;
	fecCommon_maskHeader((struct ip *) f->packetptrs[pindex]);
	if (p->length > maxlength) {
	    maxlength = p->length;
	}
	hex_dump(zc_redFec, ZLOG_LEVEL_DEBUG, f->packetptrs[pindex], f->packetsizes[pindex], "Length %u: Block NA, Source packet %d", f->packetsizes[pindex], pindex);
	pindex++;
    }

    zlog_debug( zc_redFec, "pindex = %d, fec parity (k) = %d", pindex, f->fec_k ) ;

    assert(pindex < f->fec_k);

    /* if present, the passed packet is the last of the source packets.	*/
    if (pinfo != 0) {
	//	f->packetptrs[pindex] = pinfo->packetdata;
	f->packetptrs[pindex]
	    = calloc(pinfo->length, sizeof(unsigned char));
	memcpy(f->packetptrs[pindex], pinfo->packetdata, pinfo->length);
	f->packetsizes[pindex] = pinfo->length;
	fecCommon_maskHeader((struct ip *) f->packetptrs[pindex]);
	if (pinfo->length > maxlength) {
	    maxlength = pinfo->length;
	}
	hex_dump(zc_redFec, ZLOG_LEVEL_DEBUG, f->packetptrs[pindex], f->packetsizes[pindex], "Length %u: Block NA, Source packet %d", f->packetsizes[pindex], pindex);
	pindex++;
    }

    /* at this point, any non-existent packets [pindex,k) have null	*/
    /* pointers for data and 0 lengths.					*/

    /* allocate memory for the parity packets.				*/
    for (pindex = f->fec_k; pindex < f->fec_n; pindex++) {
	f->packetptrs[pindex] = calloc(maxlength, sizeof(unsigned char));
	f->packetsizes[pindex] = maxlength;
    }

    /* generate the parity packets.					*/
    zlog_debug(zc_redFec, "Calling rse_code(%d, %d, %d, 0x%p, 0x%p, 0x%p)",
	       f->fec_k, f->fec_h, maxlength, f->packetptrs, f->packetsizes, f->pstat);
    rse_code(f->fec_k, f->fec_h, maxlength,
	     f->packetptrs, f->packetsizes, f->pstat);

    /* debugging... */
    for (pindex = 0; pindex < f->fec_n; pindex++) {
	if (pindex < f->fec_k) {
	    zlog_debug(zc_redFec, "Block %d Source packet %d: packetsize=%d, pstat=%d, first word=0x%08x",
		       paritySeq,
		       pindex, f->packetsizes[pindex], f->pstat[pindex],
		       f->packetptrs[pindex] != 0
		       ? *((unsigned int *) f->packetptrs[pindex])
		       : 0);
	}
	else {
	    zlog_debug(zc_redFec, "Block %d, Parity packet %d: packetsize=%d, pstat=%d, first word=0x%08x",
		       paritySeq, 
		       pindex, f->packetsizes[pindex], f->pstat[pindex],
		       f->packetptrs[pindex] != 0
		       ? *((unsigned int *) f->packetptrs[pindex])
		       : 0);
	}
	hex_dump(zc_redFec, ZLOG_LEVEL_DEBUG, f->packetptrs[pindex], f->packetsizes[pindex], "Length %u: Block %d, Source packet NA", f->packetsizes[pindex], pindex);
    }

    /* free the copies of the source packet data.			*/
    for (pindex = 0; pindex < f->fec_k; pindex++) {
	if (f->packetptrs[pindex] != 0) {
	    free(f->packetptrs[pindex]);
	    f->packetptrs[pindex] = 0;
	}
    }

    /* build the new structures for the parity packets.  They will be	*/
    /* based on the last source packetinfo structure in the block.	*/
    if (pinfo != 0) {
	base_pinfo = pinfo;
    }
    else {
	base_pinfo = f->fecBlockTail;
    }

    zlog_debug(zc_redFec, "base_pinfo=%p, base_pinfo->pflow=%p, base_pinfo->blockIndex=%d",
	       base_pinfo,
	       base_pinfo->pflow,
	       base_pinfo->blockIndex);

    for (pindex = f->fec_k; pindex < f->fec_n; pindex++) {
	struct udphdr *udph;
        struct packetinfo *new_pinfo;	/* new packetinfo structure.		*/

	/* note that this copy will copy the correct k and h parameters	*/
	/* into the new structure.					*/
	new_pinfo = packetinfo_copyWithData(base_pinfo);
	new_pinfo->flow_seq = paritySeq;
	new_pinfo->blockIndex = pindex;
	new_pinfo->isParity = 1;
	/* XXX should we mask off FROM_ENCLAVE here, or is it ok to	*/
	/* just set to zero?  For now, just setting to zero.		*/
	/* (bss 2/1/2017)						*/
	// new_pinfo->capturePointsVisited = 0;

	/* ipheader first points to the old packetdata.			*/
	ipheader = (struct ip *) new_pinfo->packetdata;
	iphl = ipheader->ip_hl << 2;

	/* allocate new packetdata.					*/
	new_pinfo->length = maxlength + iphl + sizeof(struct udphdr);
	new_pinfo->packetdata
	    = (unsigned char *) calloc(new_pinfo->length,
				       sizeof(unsigned char));

	/* temporarily save old packet data so can copy its IP header.	*/
	bufptr = new_pinfo->packetdata;
	memcpy(bufptr, (void *) ipheader, iphl);

	/* free old packetdata.						*/
	free(ipheader);

	/* fix length.  ipheader now points to the new packetdata.	*/
	ipheader = (struct ip *) new_pinfo->packetdata;
	ipheader->ip_len = htons(new_pinfo->length);

	bufptr += iphl;

	/* create udphdr */
	udph = (struct udphdr *) bufptr;
	udph->uh_sport = htons(base_pinfo->tuple->srcport);
	udph->uh_dport = htons(base_pinfo->tuple->dstport);
	/* length includes both header and payload.  (bss 3/11/2016)	*/
	udph->len = htons(f->packetsizes[pindex] + sizeof(struct udphdr));
	udph->check = 0;

	// fix size so that packetinfo_rebuild works
	new_pinfo->remaindersize = f->packetsizes[pindex] + sizeof(struct udphdr);

	bufptr += sizeof(struct udphdr);

	/* copy the generated parity payload into the packet.		*/
	zlog_debug(zc_redFec, "Copying %d byte parity into f->packetptrs[%d] (max parity size=%d).",
		  f->packetsizes[pindex], pindex, maxlength);
	memcpy(bufptr, f->packetptrs[pindex], f->packetsizes[pindex]);

	/* free memory allocated for parity data.			*/
	free(f->packetptrs[pindex]);
	f->packetptrs[pindex] = 0;
	f->packetsizes[pindex] = 0;
	zlog_debug(zc_redFec, "Generated parity packet %d:", pindex);
	hex_dump(zc_redFec, ZLOG_LEVEL_TRACE, new_pinfo->packetdata, new_pinfo->length, "Length %u: Generated parity packet %d: %p", new_pinfo->length, pindex, new_pinfo);
	/* add generated parity packet to returned packet list.		*/
	if (pinfotail == 0) {
	    pinfolist = new_pinfo;
	}
	else {
	    pinfotail->next = new_pinfo;
	}
	pinfotail = new_pinfo;
	zlog_debug(zc_redFec, "new_pinfo->pflow = %p", new_pinfo->pflow);
    }

    /* free the stored copies of source packets.			*/
    pnext = 0;
    for (p = f->fecBlockHead; p != 0; p = pnext) {
	pnext = p->next;
        // FREE
	packetinfo_free(p);
    }
    f->fecBlockHead = 0;
    f->fecBlockTail = 0;

    /* debugging... */
    zlog_debug(zc_redFec, "generateParity returning...");
    for (p = pinfolist; p != 0; p = p->next) {
	zlog_debug(zc_redFec, "\tpinfo=%p, pflow=%p flowSeq=%d blockIndex=%d, isParity=%d",
		   p,
		   p->pflow,
		   p->flow_seq,
		   p->blockIndex,
		   p->isParity);
	packetinfo_log(zc_redFec, ZLOG_LEVEL_DEBUG, p);
    }

    return pinfolist;
}


/************************************************************************/
/*									*/
/*	redFecActuator() - applies packet FEC to a packet in the red	*/
/*		pipeline (i.e., originating from the red network).	*/
/*		Takes a packetinfo structure describing a packet,	*/
/*		saves copies of the structures until an FEC block	*/
/*		can be created, returning the original structures,	*/
/*		and with the last source packet also appending the	*/
/*		parity packets and freeing the saved copies.		*/
/*									*/
/************************************************************************/
u_int32_t redFecActuator(struct packetinfo *pinfo,
			 struct packetinfo **pbeg,
			 struct packetinfo **pend)
{
    struct fecParams fecparams;	/* FEC parameters from packet.		*/
    struct flow *f;		/* flow structure for packet.		*/
    // struct deducehdr *shim;
    struct packetinfo *prepend_pinfo;
    struct packetinfo *pcopy;	/* copy of pinfo to be stored in flow.	*/
    struct packetinfo *p;	/* packets to prepend to list.		*/
    struct packetinfo *plisttail = 0;
				/* tail of returned packet list.	*/
    int k;			/* number of source packets in block.	*/
    int h;			/* number of parity packets in block.	*/
    // u_int32_t actuatorbits;

    /* mark the packet as using the FEC actuator.			*/
    // shim = packetinfo_get_deducehdrFromExternal(pinfo);
    //    actuatorbits = deducehdr_getActuatorbits(shim);
    // actuatorbits |= A_PACKETFEC;
    // deducehdr_setActuatorbits(shim, actuatorbits);

    /* state is stored in the flow structure associated with the	*/
    /* packet.								*/
    f = pinfo->pflow;
    zlog_debug(zc_redFec, "*** redFecActuator() - %s",
	       f->tuplestr_buff);

    zlog_debug(zc_redFec, "Stored packets at start:");
    for (p = f->fecBlockHead; p != 0; p = p->next) {
	zlog_debug(zc_redFec, "\tpinfo=%p, pflow=%p flow_seq=%u, blockIndex=%d, isParity=%d",
		   p,
		   p->pflow,
		   p->flow_seq,
		   p->blockIndex,
		   p->isParity);
    }

    /* get the FEC parameters from the composition.			*/
    k = pinfo->comp->fec_k;
    h = pinfo->comp->fec_h;

    /* store the packet's FEC parameters so that they can be put into	*/
    /* the actuator parameter list correctly.  This will be propagate	*/
    /* to any saved copies of packets.					*/
    pinfo->fec_k = k;
    pinfo->fec_h = h;

    /* if the FEC level has changed, then close out the current FEC	*/
    /* block - generate parity packets.  They are stored to be		*/
    /* prepended to the packetinfo structure that will be emitted.	*/
    /* The first time, the flow's fec_type should be 0, but the		*/
    /* fecPacketCount should also be zero, so the flow's fec_type	*/
    /* should be initialized without any parity generation.		*/
    zlog_debug(zc_redFec,
	       "f->fec_k=%d, f->fec_h=%d, comp->fec_k=%d, comp->fec_h=%d",
	       f->fec_k, f->fec_h,
	       pinfo->comp->fec_k, pinfo->comp->fec_n);
    prepend_pinfo = 0;
    if ((pinfo->comp->fec_k != f->fec_k)
	|| (pinfo->comp->fec_h != f->fec_h)) {
	/*    if (pinfo->comp->fec_type != f->fec_type) {*/
	if (f->fecPacketCount > 0) {
	    zlog_debug(zc_redFec, "generating parity for previous FEC block (fec_k=%d, fec_h=%d)",
		       f->fec_k, f->fec_h);
	    prepend_pinfo = redFecActuator_generateParity(f, 0);
	}

	//	f->fec_type = pinfo->comp->fec_type;
	f->fec_k = k;
	f->fec_h = h;
	f->fec_n = k + h;
	f->fecPacketCount = 0;
	zlog_debug(zc_redFec, "changed FEC type to k=%d, h=%d\n",
		   f->fec_k, f->fec_n);
    }

    /* debugging. */
    zlog_debug(zc_redFec, "Checked for changed FEC.  If so generated parity...");
    for (p = prepend_pinfo; p != 0; p = p->next) {
	zlog_debug(zc_redFec, "\tpinfo=%p, pflow=%p, flow_seq=%u, blockIndex=%d, isParity=%d",
		   p,
		   p->pflow,
		   p->flow_seq,
		   p->blockIndex,
		   p->isParity);
    }

    pinfo->blockIndex = f->fecPacketCount;
    zlog_debug(zc_redFec, "Checking for complete block.  Current blockIndex=%d.\n",
	       f->fecPacketCount);


    /* if the new packet completes a block then generate parity packets	*/
    if (++(f->fecPacketCount) >= k) {
	zlog_debug(zc_redFec, "Block is complete (%d packets).  Generating parity.",
		   f->fecPacketCount);
	pinfo = redFecActuator_generateParity(f, pinfo);
	f->fecPacketCount = 0;
    }

    /* otherwise, save a copy of the new packet and add it to the	*/
    /* list for the block.  The packet count has already been updated	*/
    /* above.								*/
    else {
	zlog_debug(zc_redFec, "Block is not complete (%d packets).  Saving copy of packet.\n",
		   f->fecPacketCount);
	pcopy = packetinfo_copyWithData(pinfo);
	if (f->fecBlockHead == 0) {
	    f->fecBlockHead = pcopy;
	}
	else {
	    f->fecBlockTail->next = pcopy;
	}
	f->fecBlockTail =  pcopy;
    }

    /* debugging. */
    zlog_debug(zc_redFec, "Checked for completed block.  If so generated parity...");
    for (p = pinfo; p != 0; p = p->next) {
	zlog_debug(zc_redFec, "\tpinfo=%p, pflow=%p, flow_seq=%u, blockIndex=%d, isParity=%d",
		   p,
		   p->pflow,
		   p->flow_seq,
		   p->blockIndex,
		   p->isParity);
    }

    /* prepend packets from a preceding FEC block.			*/
    if (prepend_pinfo != 0) {
	zlog_debug(zc_redFec, "Prepending packets from preceding block.");
	for (p = prepend_pinfo; p != 0; p = p->next) {
	    if (p->next == 0) {
		p->next = pinfo;
		break;
	    }
	}
	pinfo = prepend_pinfo;
    }

    zlog_debug(zc_redFec, "Stored packets at end:");
    for (p = f->fecBlockHead; p != 0; p = p->next) {
	zlog_debug(zc_redFec, "\tpinfo=%p, pflow=%p, flow_seq=%u, blockIndex=%d, isParity=%d",
		   p,
		   p->pflow,
		   p->flow_seq,
		   p->blockIndex,
		   p->isParity);
    }

    zlog_debug(zc_redFec, "Final pinfo list:");
    for (p = pinfo; p != 0; p = p->next) {
	zlog_debug(zc_redFec, "\tpinfo=%p, pflow=%p, flow_seq=%u, blockIndex=%d, isParity=%d",
		   p,
		   p->pflow,
		   p->flow_seq,
		   p->blockIndex,
		   p->isParity);
    }

    /* add the FEC parameters to the packets, and determine the		*/
    /* tail of the packet list.						*/
    zlog_debug(zc_redFec, "Adding FEC parameters:");
    
    plisttail = pinfo;		/* in case pinfo is null.		*/
    for (p = pinfo; p != 0; p = p->next) {
	zlog_debug(zc_redFec, "\tpinfo=%p, pflow=%p, flow_seq=%u, blockIndex=%d, isParity=%d",
		   p,
		   p->pflow,
		   p->flow_seq,
		   p->blockIndex,
		   p->isParity);
	plisttail = p;		/* the last time through the loop, this	*/
				/* will be the tail of the list.	*/
	fecparams.fec_k = p->fec_k;
	fecparams.fec_h = p->fec_h;
	fecparams.fec_seq = p->blockIndex;
	fecparams.reserved = 0;
	fecparams.block_seq = htonl(p->flow_seq);
	zlog_debug(zc_redFec, "Adding parameters to %p: fec_k=%d, fec_h=%d, fec_seq=%d",
		   p, fecparams.fec_k, fecparams.fec_h, fecparams.fec_seq);
	packetinfo_addAParam(p, &fecparams, sizeof(struct fecParams));
    }

    *pbeg = pinfo;
    *pend = plisttail;

    zlog_debug(zc_redFec, "*pbeg = %p, *pend = %p", *pbeg, *pend);
    for (p = pinfo; p != 0; p = p->next) {
	hex_dump(zc_redFec, ZLOG_LEVEL_TRACE, p->packetdata, p->length, "Length %u: End of %s: %p", p->length, __func__, p);
	packetinfo_log(zc_redFec, ZLOG_LEVEL_DEBUG, p);
	deducehdr_logAll(zc_redFec, ZLOG_LEVEL_DEBUG, packetinfo_get_deducehdrFromPacket(p), p->actuatorParams, p->deduceparamsizeWithPad);
    }

    if (*pbeg == 0) {
	return STATE_NOSEND;
    }
    else {
	return STATE_CONTINUE;
    }
}


