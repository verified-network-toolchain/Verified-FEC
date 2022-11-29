/*
 * blackFecActuator.c
 * Forward Erasure Correction actuator - black side
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
#include "fecCommon.h"
#include "fecParams.h"
#include "fecBlock.h"
#include "fec.h"
#include "flowTuple.h"
#include "flow.h"
#include "overlayhdr.h"
#include "util.h"
#include "blackFecActuator.h"

#define FECTIMEOUT	10.0	/* 10 seconds.				*/
#define MAXPACKETLENGTH	65536
#define MAXSTRING	1024

// XXX: will this work ok with multiple threads?
char outstring[MAXSTRING];

// fistq_handle *pinfo_qh;	/* fistq on which we send pinfo to Xlator */
// Should no longer be reported based on discussions with Andrei -- due to
// reverting to immediate reporting; these packet
// are supposed to be consumed by the actuators
// fistq_handle *sender2aggregator;	/* fistq on which we send pinfo to Xlator */

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

extern zlog_category_t *zc_blackFec;


/************************************************************************/
/*									*/
/*	blackFecActuator_init() - initialize.				*/
/*									*/
/************************************************************************/

void blackFecActuator_init()
{
    // sender2aggregator = fistq_getHandle("sender", "aggregator", FISTQ_FREE, NULL);

    /* initialize the FEC algorithm.				*/
    rse_init();

    return;
}


/************************************************************************/
/*									*/
/*	blackFecActuator_unDeduce() - remove the Deduce header from	*/
/*		the given packet data.  Make the necessary adjustments	*/
/*		to the IP header.					*/
/*									*/
/************************************************************************/
unsigned char *blackFecActuator_unDeduce(unsigned char *packetdata, int length)
{
    struct deducehdr *dhdr;
    unsigned char *newpacket;
    u_int16_t newlength;		/* length of new packet.		*/
    struct ip *ipheader;	/* ipheader, used for original.		*/
    struct udphdr *udph;
    unsigned char *bufptr;	/* pointer into original packet.	*/
    unsigned char *nbufptr;	/* pointer into new packet.		*/
   
    u_int32_t iphl;			/* ip header length.			*/
    u_int32_t size;
    // u_int32_t srcaddr, dstaddr;
    u_int16_t srcport, dstport;
    u_int16_t iplen, udplen;

    hex_dump(zc_blackFec, ZLOG_LEVEL_DEBUG,
	       packetdata, length, "Length %u: unDeduce input", length);

    bufptr = packetdata;

    ipheader = (struct ip *) bufptr;

    if (ipheader->ip_p != IPPROTO_UDP)
	goto no_deducehdr;

    // srcaddr = ipheader->ip_src.s_addr;
    // dstaddr = ipheader->ip_dst.s_addr;
 
    iphl = ipheader->ip_hl << 2 ;
    bufptr += iphl;
    udph = (struct udphdr *) bufptr;

    srcport = ntohs(udph->uh_sport);
    if (srcport != DEDUCE_SPORT)
	goto no_deducehdr;

    dstport = ntohs(udph->uh_dport);
    if (dstport != DEDUCE_DPORT)
	goto no_deducehdr;

    iplen = ntohs(ipheader->ip_len);
    udplen = ntohs(udph->uh_ulen);
    if (bufptr + udplen != packetdata + iplen)
	goto no_deducehdr;

    if (udplen < sizeof(struct udphdr) + sizeof(struct deducehdr))
	goto no_deducehdr;

    // get deduce hdr (after udp header), and find length of params
    bufptr += sizeof(struct udphdr);
    dhdr = (struct deducehdr *)bufptr;
    size = dhdr->paramSize;
    size = (size + 3) & 0xfffc;

    // new length is old length without udp hdr, deduce header and params
    newlength = length - (sizeof(struct udphdr) + sizeof(struct deducehdr) + size);
    nbufptr = newpacket = calloc(newlength, sizeof(unsigned char));

    // copy old ip header to new packet
    memcpy(newpacket, packetdata, iphl);

    // restore ip addrs and protocol and length
    ipheader = (struct ip *) newpacket;
    ipheader->ip_src.s_addr = dhdr->origSrcIpAddr;
    ipheader->ip_dst.s_addr = dhdr->origDstIpAddr;
    ipheader->ip_p = dhdr->origIpProtocol;
    ipheader->ip_len = htons(newlength);

    // move past iphdr in new packet
    nbufptr += iphl;

    // move past deduce info in old packet
    bufptr += sizeof(struct deducehdr) + size;

    // copy packet remainder to new packet
    memcpy(nbufptr, bufptr, length - (bufptr - packetdata));

    hex_dump(zc_blackFec, ZLOG_LEVEL_DEBUG,
	       newpacket, newlength, "Length %u: unDeduce output", newlength);

    return newpacket;

no_deducehdr:
    newpacket = calloc(length, sizeof(unsigned char));
    memcpy(newpacket, packetdata, length);
    return newpacket;
}


/************************************************************************/
/*									*/
/*	blackFecActuator_removeHeaders() - remove headers to get to	*/
/*		payload for parity packets.				*/
/*									*/
/************************************************************************/

unsigned char *blackFecActuator_removeHeaders(unsigned char *packetdata,
				    int *length)
{
    unsigned char *tempBuffer;	/* temporary buffer for packet.		*/
    int tempLength;		/* length of temporary buffer.		*/
    struct ip *ipheader;	/* pointer to ip header.		*/
    int iphl;			/* IP header length.			*/
    unsigned char *newBuffer;	/* new buffer.				*/

    /* remove the deduce header.					*/
    zlog_debug(zc_blackFec, "before removing headers: length = %d",
	       *length);
    tempBuffer = blackFecActuator_unDeduce(packetdata, *length);
    ipheader = (struct ip *) tempBuffer;
    tempLength = ntohs(ipheader->ip_len);
    zlog_debug(zc_blackFec, "after removing deduce header: templength = %d",
	       tempLength);

    /* remove the IP header.						*/
    iphl = ipheader->ip_hl << 2;
    tempLength -= iphl;

    // remove the udp header
    tempLength -= sizeof(struct udphdr);

    zlog_debug(zc_blackFec, "after removing IP and UDP header: templength = %d",
	       tempLength);

    // XXX: can save a calloc by using the same memory and memmove()
    newBuffer = calloc(tempLength, sizeof(unsigned char *));
    memcpy(newBuffer, tempBuffer + iphl + sizeof(struct udphdr), tempLength);
    free(tempBuffer);
    *length = tempLength;

    // hex_dump(zc_blackFec, ZLOG_LEVEL_TRACE, newBuffer, tempLength, "After removeHeaders");

    return newBuffer;
}


/************************************************************************/
/*									*/
/*	blackFecActuator_regenerateMissingPackets() - call the core	*/
/*		FEC code to regenerate the missing packets.		*/
/*									*/
/************************************************************************/

struct packetinfo *blackFecActuator_regenerateMissingPackets(
	struct flow *f,
	struct fecBlock *fecblock,
	struct packetinfo *pinfo)
{
    int i;			/* loop counter.			*/
    // XXX: How does this work with multiple threads?
    /*    static unsigned char **packetptrs = 0;*/
				/* pointers to packet data for FEC	*/
				/* algorithm.				*/
    // XXX: How does this work with multiple threads?
    /*    static int *packetsizes = 0;*/
				/* sizes of packet data for FEC		*/
				/* algorithm.				*/
    /*    static char *pstat = 0;*/
				/* control/status bytes for FEC		*/
				/* algorithm.				*/
    int maxn = FECMAXBLOCKSIZE;	/* maximum block size supported.	*/
    int k;			/* number of source packets in block.	*/
    int h; 			/* number of parity packets in block.	*/
    int n;			/* total number of packets in the block.*/
    int blockIndex;		/* sequence number for given packet in	*/
				/* given block.				*/
    int maxpacketsize;		/* maximum packet size = size of parity	*/
    				/* packet.				*/
    struct packetinfo *newpinfo;/* packetinfo structure for regenerated	*/
				/* packet.				*/
    struct packetinfo *plist = 0;
				/* list of output packets.		*/
    struct packetinfo *plisttail = 0;
				/* tail of output list.			*/
    struct ip *ipheader;	/* pointer to ip header.		*/
    struct ip *newipheader;	/* pointer to ip header.		*/
    int length;			/* temporary storage for length.	*/

    if (!pinfo->isParity) {
      zlog_error(zc_blackFec, "Expected parity packet, but got source packet.  About to abort.");
    }
    assert(pinfo->isParity);

    /* allocate initial arrays for storing packet pointers.		*/
    if (f->bpacketsizes == 0) {
	f->bpacketptrs = calloc(sizeof(unsigned char *), maxn);
	f->bpacketsizes = calloc(sizeof(int), maxn);
	f->bpstat = calloc(sizeof(char), maxn);
    }
    else {
	// XXX: memory leak? we calloc f->bpacketptrs[i] but hardly ever free
	memset(f->bpacketptrs, 0, maxn * sizeof(unsigned char *));
	memset(f->bpacketsizes, 0, maxn * sizeof(int));
	memset(f->bpstat, 0, maxn);
    }

    zlog_debug(zc_blackFec, "regenerateMissingPackets()");

    k = fecblock->k;
    h = fecblock->h;
    n = k + h;

    assert(n <= maxn);

    /* the passed packet should be a parity packet, so its length	*/
    /* should equal the maximum in the block.				*/
    maxpacketsize = pinfo->length;

    /* get the packet sequence number (within the block) for the	*/
    /* provided parity packet.						*/
    blockIndex = pinfo->blockIndex;

    /* initialize the structures needed by the fec algorithm.		*/
    /* handle the source packets.					*/
    for (i = 0; i < k; i++) {
	/* allocate space for missing packet and mark it as wanted.	*/
	if (fecblock->packets[i] == 0) {
	    zlog_debug(zc_blackFec, "calloc for missing regular packet: %d", i);
	    f->bpstat[i] = FEC_FLAG_WANTED;
	    f->bpacketptrs[i] = calloc(maxpacketsize, sizeof(unsigned char));
	    f->bpacketsizes[i] = maxpacketsize;
	}
	/* for present packet, copy information to structures.		*/
	else {
	    zlog_debug(zc_blackFec, "unDeduce for regular packet: %d", i);
	    //	    f->bpacketptrs[i] = fecblock->packets[i]->packetdata;
	    f->bpacketptrs[i] = blackFecActuator_unDeduce(fecblock->packets[i]->packetdata,
						      fecblock->packets[i]->length);
	    ipheader = (struct ip *) f->bpacketptrs[i];
	    f->bpacketsizes[i] =  ntohs(ipheader->ip_len);
	    fecCommon_maskHeader((struct ip *) f->bpacketptrs[i]);
	}
    }
    /* handle the parity packets.					*/
    /* Could have set upper bound to blockIndex, but setting it to n	*/
    /* allows packets to have arrived out of order.			*/
    for (i = k; i < n; i++) {
	if (i == blockIndex) {
	    zlog_debug(zc_blackFec, "match on blockIndex for parity packet: %d", i);
	    continue;
	}
	/* for present packet, copy information to structures.		*/
	if (fecblock->packets[i] != 0) {
	    zlog_debug(zc_blackFec, "removeHeaders for parity packet: %d", i);
	    /* remove headers.						*/
	    length = fecblock->packets[i]->length;
	    f->bpacketptrs[i] = blackFecActuator_removeHeaders(fecblock->packets[i]->packetdata,
							   &length);
	    f->bpacketsizes[i] = length;
	}
    }
    /* copy the information from the given packetinfo structure.	*/
    /* remove the headers.						*/
    // XXX: TODO: This assumes this packet (blockindex) is parity packet.
    zlog_debug(zc_blackFec, "removeHeaders for parity packet blockindex: %d", blockIndex);
    length = pinfo->length;
    f->bpacketptrs[blockIndex] = blackFecActuator_removeHeaders(pinfo->packetdata,
							    &length);
    f->bpacketsizes[blockIndex] = length;

    /* call the packet regeneration code.				*/
    zlog_debug(zc_blackFec, "Calling rse_code(%d, %d, %d, 0x%p, 0x%p, 0x%p)",
	       k, 0, maxpacketsize, f->bpacketptrs, f->bpacketsizes, f->bpstat);
    for (i = 0; i < n; i++)
	zlog_trace(zc_blackFec, "[%d]: f->bpacketptrs = %p, f->bpacketsizes = %u, f->bpstat = 0x%02x", i, f->bpacketptrs[i], f->bpacketsizes[i], f->bpstat[i]);
    rse_code(k, 0, maxpacketsize, f->bpacketptrs, f->bpacketsizes, f->bpstat);

    /* debugging... */
    for (i = 0; i < n; i++) {
	if (i < k) {
	    zlog_debug(zc_blackFec, "Block %d, Source packet %d: packetsize=%d, f->bpstat=%d, first word=0x%08x",
		       fecblock->blockSeq,    
		       i, f->bpacketsizes[i], f->bpstat[i],
		       f->bpacketptrs[i] != 0
		       ? *((unsigned int *) f->bpacketptrs[i])
		       : 0);
	}
	else {
	    zlog_debug(zc_blackFec, "Block %d, Parity packet %d: packetsize=%d, pstat=%d, first word=0x%08x",
		       fecblock->blockSeq,
		       i, f->bpacketsizes[i], f->bpstat[i],
		       f->bpacketptrs[i] != 0
		       ? *((unsigned int *) f->bpacketptrs[i])
		       : 0);
	}
	hex_dump(zc_blackFec, ZLOG_LEVEL_DEBUG, f->bpacketptrs[i], f->bpacketsizes[i], "Length %u: Block %d, Source packet %d", length, fecblock->blockSeq, i);
    }

    /* create the packetinfo structures for the regenerated packets.	*/
    for (i = 0; i < k; i++) {
	/* only generate structure for packet that was missing.		*/
	if (fecblock->packets[i] == 0) {
	    zlog_debug(zc_blackFec, "Regenerating source packet %d of %d.",
		       i, k);
	    /* expect non-zero first byte of IP header.  If zero,	*/
	    /* the regenerated packet never existed.			*/
	    if (f->bpacketptrs[i][0] == 0) {
		zlog_debug(zc_blackFec, "Regenerated null packet %d ptr %p.  Not forwarding.", i, f->bpacketptrs[i]);
		hex_dump(zc_blackFec, ZLOG_LEVEL_TRACE, f->bpacketptrs[i], f->bpacketsizes[i], "Length %u: null packet", length);
		free(f->bpacketptrs[i]);
		continue;
	    }
	    /* allocate and initialize a new packetinfo structure.	*/
	    newpinfo = packetinfo_copyNoData(pinfo);

	    /* add the copy to the list to return.			*/
	    if (plist == 0) {
		plist = newpinfo;
	    }
	    else {
		plisttail->next = newpinfo;
	    }
	    plisttail = newpinfo;

	    /* thought we could use the data as is since we allocated	*/
	    /* the space earlier, but causes problems.			*/
	    /*	    newpinfo->packetdata = f->bpacketptrs[i]; 
		    newpinfo->length = f->bpacketsizes[i];*/
	    newpinfo->packetdata = calloc(f->bpacketsizes[i], sizeof(unsigned char));
	    memcpy(newpinfo->packetdata, f->bpacketptrs[i], f->bpacketsizes[i]); 
	    // newpinfo->length = f->bpacketsizes[i];

	    /* adjust the IP header.					*/
	    /* copy information from given parity packet.		*/
	    ipheader = (struct ip *) pinfo->packetdata;
	    newipheader = (struct ip *) newpinfo->packetdata;
	    // newipheader->ip_len = htons(newpinfo->length);
	    newipheader->ip_ttl = ipheader->ip_ttl;
	    //	    newipheader->ip_sum = ?

	    newpinfo->length = ntohs(newipheader->ip_len);

	    // regenerated packet has no deduce header
	    // iphdrsize should be the same as old.
	    newpinfo->udphdrsize = 0;
	    newpinfo->deducehdrsize = 0;
	    newpinfo->deduceparamsizeWithPad = 0;
	    newpinfo->deduceparamsizeWithoutPad = 0;
	    newpinfo->remaindersize = newpinfo->length - newpinfo->iphdrsize;

	    /* adjust parameters.					*/
	    // newpinfo->flowSeq = fecblock->blockSeq + i;
	    newpinfo->blockIndex = i;
	    newpinfo->isParity = 0;

	    zlog_notice(zc_blackFec, "Regenerated packet (source packet %d of %d).  Data=%p",
		        i, k, newpinfo->packetdata);
	    //hex_dump(zc_blackFec, ZLOG_LEVEL_TRACE, newpinfo->packetdata, 20, "Length %u: Regenerated packet %d (source packet %d of %d)", newpinfo->length, newpinfo->flowSeq, i, k);
	    hex_dump(zc_blackFec, ZLOG_LEVEL_DEBUG, newpinfo->packetdata, newpinfo->length, "Length %u: Regenerated packet <NA> (source packet %d of %d)", newpinfo->length, i, k);
	}
    }	

    return plist;
}


/************************************************************************/
/*									*/
/*	blackFecActuator_initBlockWithPacket() - initialize the given	*/
/*		block structure with information from a packet.  If the	*/
/*		packet is a source packet, a copy will be stored and	*/
/*		the original will be returned.  If it is a parity	*/
/*		packet then it will be saved and a null pointer (0)	*/
/*		will be returned.					*/
/*									*/
/************************************************************************/

struct packetinfo *blackFecActuator_initBlockWithPacket(
	struct flow *f,							
	struct fecBlock *fecblock,
	struct packetinfo *pinfo,
	int blockSeq,		/* sequence number for block.		*/
	int k,			/* number of source packets.		*/
	int h,			/* number of parity packets.		*/
	int pindex,		/* packet index in block.		*/
	BOOLEAN isParity,	/* 1 if parity packet.			*/
	double timeout)		/* timeout for block.			*/
{
    struct packetinfo *newpinfo;
				/* regenerated packet list.		*/

    zlog_debug(zc_blackFec, "blackFecActuator_initBlockWithPacket().");

    /* initilize the block.						*/
    fecblock->blockSeq = blockSeq;
    fecblock->k = k;
    fecblock->h = h;
    fecblock->packetCount++;
    fecblock->timeout = timeout;

    /* add the packet to the new block.					*/
    /* parity packets are not to be released to the pipeline, so their	*/
    /* information can just be saved.					*/
    if (isParity) {
	fecblock->packets[pindex] = pinfo;
	if (fecblock->packetCount == fecblock->k) {
	    zlog_debug(zc_blackFec, "initBlock: parity packet completes block.  Regenerating missing packets.");
	    fecblock->complete = 1;
	    newpinfo
		= blackFecActuator_regenerateMissingPackets(f,
							    fecblock,
							    pinfo);
	    // FREE: We still need to free this since a new packet info is created
	    // packetinfo_free(pinfo);

	    // zlog_info(zc_blackFec, "Sending parity packet packetinfo %p to aggregator: %d/%d", pinfo, pinfo->inLinkSeq, pinfo->outLinkSeq);

	    // if(pinfo->srcEnclaveId == 0 || pinfo->dstEnclaveId == 0)
	    // {
	    //	zlog_warn(zc_blackFec,
	    //		  "%s:%d srcEnclaveId=%d, dstEnclaveId=%d, capturePoints=%d, tuple=%s",
	    //		  __FILE__, __LINE__,
	    //		  pinfo->srcEnclaveId, pinfo->dstEnclaveId,
	    //		  pinfo->capturePointsVisited,
	    //		  pinfo->pflow->tuplestr_buff);
	    // } 
	    // packetinfo_auditAdd(pinfo);
			// in immediate capture reporting, we're suppressing this sender 2 aggregator, but
			// we then have to free the pinfo memory
			packetinfo_free(pinfo);

	    // fistq_enqueue_pinfo(sender2aggregator, pinfo, FISTQ_FLUSH);

	    return newpinfo;
	}
	else {
	    return 0;
	}
    }
    /* source packets are released to the pipeline, so a copy needs	*/
    /* to be made in case it is needed to regenerate a missing packet.	*/
    else {
	if (fecblock->packets[pindex] != 0) {
	    zlog_error(zc_blackFec,
		      "Saving packet %p to pindex %d, already occupied with %p.  RARE CASE",
		      pinfo, pindex, fecblock->packets[pindex]);
	    /* don't know which should have been the valid packet,	*/
	    /* but can't let this index be counted twice - otherwise	*/
	    /* will result in some other index having null pointer when	*/
	    /* packetCount reaches k.  Hopefully, prevents core dump at	*/
	    /* line 395 in fec.c.  (bss 7/25/2018)			*/
	    fecblock->packetCount--;
	}
	if (fecblock->packetCount == fecblock->k) {
	    zlog_debug(zc_blackFec, "initBlock: source packet completes block.  Emitting.");  
	    fecblock->complete = 1;
	    fecblock->packets[pindex] = 0;
	}
	else {
	    fecblock->packets[pindex] = packetinfo_copyWithData(pinfo);
	}

	return pinfo;
    }
}


/************************************************************************/
/*									*/
/*	blackFecActuator_addPacketToBlock() - add a new packet to the	*/
/*		given block.  Returns 0 if parity packet (either	*/
/*		because stored, or because block is already complete).	*/
/*		Returns the packet if source packet.			*/
/*									*/
/************************************************************************/

struct packetinfo *blackFecActuator_addPacketToBlock(struct flow *f,
						     struct fecBlock *fecblock,
						     struct packetinfo *pinfo)
{
    struct packetinfo *newpinfo;	/* copy of original packetinfo	*/
			    		/* structure.			*/

    zlog_debug(zc_blackFec, "addPacketToBlock... complete=%d, parity=%d",
	       fecblock->complete, pinfo->isParity);
    fecBlock_log(zc_blackFec, fecblock);

    /* if the block is already complete, drop the packet		*/
    /* (which must be a parity packet).					*/
    if (fecblock->complete == 1) {
	zlog_debug(zc_blackFec, "Already complete.  Freeing packet %p.", pinfo);

	// FREE: Still needs to be freed
	// packetinfo_free(pinfo);

	zlog_info(zc_blackFec, "Sending packetinfo %p to aggregator:", pinfo);

	packetinfo_free(pinfo);

	// fistq_enqueue_pinfo(sender2aggregator, pinfo, FISTQ_FLUSH);

	return 0;
    }

    fecblock->packetCount++;
    zlog_debug(zc_blackFec, "packetcount=%d, k=%d.",
	       fecblock->packetCount, fecblock->k);
    
    /* packet completes block.						*/
    if (fecblock->packetCount == fecblock->k) {
	zlog_debug(zc_blackFec, "Packet completes block.");
	/* mark the block as complete.					*/
	fecblock->complete = 1;
	/* if it's a parity packet, then recompute missing packets.	*/
	if (pinfo->isParity) {
	    newpinfo
		= blackFecActuator_regenerateMissingPackets(f,
							    fecblock,
							    pinfo);
	    zlog_debug(zc_blackFec, "Freeing parity packet %p used to regenerate missing packets.", pinfo);
	    // FREE:
	    // packetinfo_free(pinfo);	/* no longer need it.		*/

	    // zlog_info(zc_blackFec, "Sending packetinfo %p to aggregator:", pinfo);
	    // packetinfo_auditAdd(pinfo);
	    // in immediate capture reporting, we're suppressing this sender 2 aggregator, but
	    // we then have to free the pinfo memory
	    packetinfo_free(pinfo);

	    // fistq_enqueue_pinfo(sender2aggregator, pinfo, FISTQ_FLUSH);

	    /* return the list of regenerated packets.			*/
	    zlog_debug(zc_blackFec, "Complete: Parity packet - returning regenerated packets.");
	    return newpinfo;
	}
	/* if it's a source packet, just emit the packet.		*/
	else {
	    zlog_debug(zc_blackFec, "Complete: Source packet - returning original packet.");
	    return pinfo;
	}
    }
    
    /* block not yet complete.  Store the new packet.  If it's		*/
    /* a source packet, save a copy and return the original.		*/
    /* If it's a parity packet, save it, and return nothing.		*/
    else {
	zlog_debug(zc_blackFec, "Packet does not complete block.");
	if (fecblock->packets[pinfo->blockIndex] != 0) {
	    zlog_error(zc_blackFec,
		      "Saving packet %p to pinfo->blockIndex %d, already occupied with %p.",
		      pinfo, pinfo->blockIndex, fecblock->packets[pinfo->blockIndex]);
	    /* don't know which should have been the valid packet,	*/
	    /* but can't let this index be counted twice - otherwise	*/
	    /* will result in some other index having null pointer when	*/
	    /* packetCount reaches k.  Hopefully, prevents core dump at	*/
	    /* line 395 in fec.c.  (bss 7/27/2018)			*/
	    fecblock->packetCount--;
	}
	if (pinfo->isParity) {
	    fecblock->packets[pinfo->blockIndex] = pinfo;
	    zlog_debug(zc_blackFec, "Incomplete: Stored parity packet.  Returning 0.");
	    return 0;
	}
	else {
	    fecblock->packets[pinfo->blockIndex] = packetinfo_copyWithData(pinfo);

	    zlog_debug(zc_blackFec, "Incomplete: Stored copy of source packet.  Returning original.");
	    return pinfo;
	}
    }

    /* should not be reached.						*/
    return pinfo;
}


/************************************************************************/
/*									*/
/*	blackFecActuator() - processes incoming source and FEC parity	*/
/*		packets to regenerate missing source packets.		*/
/*		Takes a packetinfo structure describing a packet,	*/
/*		saves copies of the structures for both source and	*/
/*		parity packets until the required number of packets has	*/
/*		been received, returning the original source packet	*/
/*		structures as they arrive, and regenerating and		*/
/*		returning structures for missing source packets once	*/
/*		the required number of packets has been received.	*/
/*		If the required number of packets is not received and	*/
/*		a new FEC block starts, all stored structures are	*/
/*		freed.							*/
/*									*/
/************************************************************************/

DECLARE(blackFecActuator)
//struct packetinfo *blackFecActuator(struct packetinfo *pinfo)
{
    struct fecParams fecparams;	/* FEC parameters from packet.		*/
    struct flow *f;		/* flow structure for packet.		*/
    int k;			/* number of source packets in block.	*/
    int h;			/* number of parity packets in block.	*/
    // struct deducehdr *dheader;	/* deduce header.			*/
    int flowSeq;		/* flow sequence number for packet.	*/
    int pindex;			/* packet index within block.		*/
    BOOLEAN isParity;		/* flag indicating packet is parity	*/
				/* packet.				*/
    int blockSeq;		/* block sequence number: flow sequence	*/
				/* number of first packet in FEC block.	*/
    double currTime;		/* current time (Unix time with		*/	
				/* microseconds).			*/
    struct fecBlock *currblock;	/* current (most recent) FEC block.	*/
    struct fecBlock *fecblock;	/* packet's fec block if not current.	*/
    struct fecBlock *oldblock;	/* previous fec block in list.		*/
    struct fecBlock *newblock;	/* newly created fec block.		*/
    struct fecBlock *fecblocknext;
				/* next fec block in list.		*/
    struct packetinfo *returnlist;
				/* list of packet structures to return.	*/

    zlog_debug(zc_blackFec, "*** blackFecActuator() %s",
	       // pinfo->srcEnclave->id, pinfo->dstEnclave->id,
	       pinfo->pflow->tuplestr_buff);

    /* get the FEC parameters from the packet.				*/
    packetinfo_getAParam(pinfo, &fecparams, sizeof(struct fecParams));
    k = fecparams.fec_k;
    h = fecparams.fec_h;
    pindex = fecparams.fec_seq;
    flowSeq = ntohl(fecparams.block_seq);
    blockSeq = 0;
    pinfo->blockIndex = pindex;
    zlog_debug(zc_blackFec, "Got FEC parameters from %p, fec_k=%d, fec_h=%d, fec_seq=%d block_seq=%d",
	       pinfo, k, h, pindex, blockSeq);
    
    flowTuple_log(zc_blackFec, ZLOG_LEVEL_DEBUG, pinfo->tuple);

    /* get the needed information from the deduce header.		*/
    // dheader = packetinfo_get_deducehdrFromExternal(pinfo);
    // flowSeq = deducehdr_getFlowSequence(dheader);

    deducehdr_logAll(zc_blackFec, ZLOG_LEVEL_DEBUG, packetinfo_get_deducehdrFromPacket(pinfo), pinfo->actuatorParams, pinfo->deduceparamsizeWithPad);

    /* determine whether source or parity packet and determine the	*/
    /* block number for the packet.  The block is identified by the flow*/
    /* sequence number of first packet in block.  Parity packets have	*/
    /* the same flow sequence number as the first packet in the block.	*/
    if (pindex < k) {		/* source packet.			*/
	isParity = 0;
	pinfo->isParity = 0;
	blockSeq = flowSeq - pindex;
	// blockSeq = 0 ;              // TO DO: Add it to deduce header, or make it a parameter
    }
    else {			/* parity packet.			*/
	isParity = 1;
	pinfo->isParity = 1;
	blockSeq = flowSeq;
	// blockSeq = 0 ;            // TO DO: Add it to deduce header, or make it a parameter
    }

    zlog_debug(zc_blackFec, "%s pinfo=%p, k=%d, h=%d,  blockseq=%d pindex=%d isParity=%d",
	       pinfo->pflow->tuplestr_buff,
	       pinfo, k, h, blockSeq, pindex, isParity);

    /* FEC state is stored in the flow structure associated with the	*/
    /* packet.								*/
    f = pinfo->pflow;

    /* get the current time to use for setting and checking timeouts.	*/
    currTime = util_getCurrentTime();

    /* the current block is the last block in the flow's block list.	*/
    currblock = f->blockListTail;

    /* handle case of empty block list.  Create a new block for the	*/
    /* packet and initialize the list.					*/
    if (currblock == 0) {
	zlog_debug(zc_blackFec, "Empty block list.  Initializing.");
	
	/* initialize the block list with a new block structure.	*/
	currblock = fecBlock_new();
	f->blockListHead = currblock;
	f->blockListTail = currblock;
	/* initialize the new block structure with the information	*/
	/* from the current packet.					*/
	zlog_debug(zc_blackFec,
		   "Before blackFecActuator_initBlockWithPacket()");
	fecBlock_log(zc_blackFec, currblock);
	returnlist = blackFecActuator_initBlockWithPacket(
					     f,
					     currblock,
					     pinfo,
					     blockSeq,      // block seq
					     k,
					     h,
					     pindex,
					     isParity,
					     currTime + FECTIMEOUT);
	zlog_debug(zc_blackFec, "After blackFecActuator_initBlockWithPacket()");
	fecBlock_log(zc_blackFec, currblock);
	goto RETURN;
    }

    zlog_debug(zc_blackFec, "Current block.  Packet's blockSeq=%d", blockSeq);
    fecBlock_log(zc_blackFec, currblock);

    /* packet is for current block.  This implies that the packet's	*/
    /* FEC type is the same as that of the current block.  Add the	*/
    /* packet to the block and use it to regenerate missing packets	*/
    /* if it completes the block.  A list of source and regenerated	*/
    /* packets will be returned.  Parity packets will just be stored	*/
    /* or deleted.							*/
    if (blockSeq == currblock->blockSeq) {
	zlog_debug(zc_blackFec, "Adding packet to current block.");
	
	returnlist = blackFecActuator_addPacketToBlock(f,
						       currblock,
						       pinfo);
	zlog_debug(zc_blackFec, "After addPacketToBlock()");
	fecBlock_log(zc_blackFec, currblock);
	
	goto RETURN;
    }

    /* packet is for a newer block (i.e. a block following the current	*/
    /* block).  Since it's a new block, it doesn't matter if the packet	*/
    /* has the same FEC type as the current block.  Create the new	*/
    /* block.  If the previous block hasn't completed it will		*/
    /* eventually complete and/or expire.				*/
    else if (blockSeq > currblock->blockSeq) {
	zlog_debug(zc_blackFec, "Adding packet to later block.");

	/* insert a new block structure into the block list.		*/
	oldblock = currblock;
	currblock = fecBlock_new();
	oldblock->next = currblock;
	currblock->prev = oldblock;
	pinfo->pflow->blockListTail = currblock;
	/* initialize the new block structure with the information	*/
	/* from the current packet.					*/
	zlog_debug(zc_blackFec, "Before blackFecActuator_initBlockWithPacket()");
	fecBlock_log(zc_blackFec, currblock);
	returnlist = blackFecActuator_initBlockWithPacket(
		f,
		currblock,
		pinfo,
		blockSeq,
		k,
		h,
		pindex,
		isParity,
		currTime + FECTIMEOUT);
	zlog_debug(zc_blackFec, "After blackFecActuator_initBlockWithPacket()");
	fecBlock_log(zc_blackFec, currblock);
	
	goto RETURN;
    }

    /* packet belongs to a previous block.  The block could be of the	*/
    /* same FEC type as the current block or a different FEC type.	*/
    else {	/* blockSeq < fecblock->blockSeq			*/
	zlog_debug(zc_blackFec, "Adding packet to earlier block.");

	/* find the block.  While searching, delete expired blocks	*/
	/* if convenient.  (If the packet belongs to an expired block,	*/
	/* the later expired blocks won't be deleted in this round.)	*/
	fecblocknext = 0;
	for (fecblock = f->blockListHead; fecblock != currblock;
	     fecblock = fecblocknext) {
	    /* save the next pointer in case block is deleted.		*/
	    fecblocknext = fecblock->next;
	    
	    /* delete expired blocks.					*/
	    if (currTime > fecblock->timeout) {
		zlog_debug(zc_blackFec, "Deleting expired block.");
		/* packet is from earlier block than block that is	*/
		/* timed out.  There's no information about it's	*/
		/* block so just release it (if a source packet)	*/
		/* or drop it (if a parity packet).			*/
		if (blockSeq <= fecblock->blockSeq) {
		    /* drop/free expired parity packet.			*/
		    if (isParity) {
			zlog_debug(zc_blackFec, "Discarding (freeing) expired parity packet %p.", pinfo);
			// FREE:
			//			packetinfo_free(pinfo);
			// zlog_info(zc_blackFec, "Sending packetinfo %p to aggregator: %d/%d", pinfo, pinfo->inLinkSeq, pinfo->outLinkSeq);

			// if(pinfo->srcEnclaveId == 0 || pinfo->dstEnclaveId == 0)
			// {
			//    zlog_warn(zc_blackFec,
			//	      "%s:%d srcEnclaveId=%d, dstEnclaveId=%d, capturePoints=%d, tuple=%s",
			//	      __FILE__, __LINE__,
			//	      pinfo->srcEnclaveId, pinfo->dstEnclaveId,
			//	      pinfo->capturePointsVisited,
			//	      pinfo->pflow->tuplestr_buff);
			// }
			// packetinfo_auditAdd(pinfo);
	    // in immediate capture reporting, we're suppressing this sender 2 aggregator, but
	    // we then have to free the pinfo memory
	    packetinfo_free(pinfo);

			// fistq_enqueue_pinfo(sender2aggregator, pinfo, FISTQ_FLUSH);

			pinfo = 0;
		    }
		    /* remove the block from the flow's block list.	*/
		    if (fecblock->prev == 0) {
			f->blockListHead = fecblock->next;
			if (fecblock->next == 0) {
			    f->blockListTail = 0;
			}
		    }
		    else {
			fecblock->prev->next = fecblock->next;
			if (fecblock->next == 0) {
			    f->blockListTail = fecblock->prev;
			}
		    }
		    if (fecblock->next != 0) {
			fecblock->next->prev = fecblock->prev;
		    }
		    /* delete the block and any saved packets.		*/
		    zlog_debug(zc_blackFec, "About to free fecBlock %p.", fecblock);
		    fecBlock_free(fecblock);
		    zlog_debug(zc_blackFec, "Successfully freed.");
		    /* release source packet even if expired.  This	*/
		    /* will be a duplicate if the packet was		*/
		    /* regenerated earlier.  This should be a rare	*/
		    /* case.						*/
		    zlog_debug(zc_blackFec, "Returning expired source packet %p.", pinfo);
		    returnlist = pinfo;
		    goto RETURN;
		}
	    }
	    
	    /* packet is for missing block.  Create the block.		*/
	    /* Since the loop walks from earlier blocks to later ones,	*/
	    /* if the current block is has a sequence number greater	*/
	    /* than that of the packet, the packet's block has		*/
	    /* either not been created or has expired (possible		*/
	    /* only if the prev pointer is 0).  In the expired case,	*/
	    /* a new block will be created and will have to expire	*/
	    /* again.  This is an unlikely case, but shouldn't		*/
	    /* cause problems except for an occasional duplicated	*/
	    /* source packet.						*/
	    if (fecblock->blockSeq > blockSeq) {
		zlog_warn(zc_blackFec, "Packet for missing block.  Creating block.  UNCOMMON CASE.");
		/* insert a new block structure into the block list.	*/
		newblock = fecBlock_new();
		newblock->next = fecblock;
		newblock->prev = fecblock->prev;
		fecblock->prev = newblock;
		if (newblock->prev == 0) {
		    f->blockListHead = newblock;
		}
		else {
		    newblock->prev->next = newblock;
		}
		/* initialize the new block structure with the		*/
		/* information from the current packet.			*/
		zlog_debug(zc_blackFec, "Before blackFecActuator_initBlockWithPacket()");
		fecBlock_log(zc_blackFec, fecblock);
		/* Note: had been initializing fecblock rather than	*/
		/* newblock, and was getting rare core dumps.  With	*/
		/* this fix, shouldn't have the core dumps.		*/
		/* (bss 11/28/2017)					*/
		returnlist = blackFecActuator_initBlockWithPacket(
			f,
			newblock,	/* had been fecblock */
			pinfo,
			blockSeq,
			k,
			h,
			pindex,
			isParity,
			currTime + FECTIMEOUT);
		zlog_debug(zc_blackFec, "After blackFecActuator_initBlockWithPacket()");
		fecBlock_log(zc_blackFec, fecblock);
		goto RETURN;
	    }
	    
	    /* packet is in the block.  Add the packet to the block.	*/
	    else if (fecblock->blockSeq == blockSeq) {
		zlog_debug(zc_blackFec, "Packet is in block %d.  Adding packet to block.", blockSeq);
		returnlist = blackFecActuator_addPacketToBlock(f,
							       fecblock,
							       pinfo);
		zlog_debug(zc_blackFec, "After addPacketToBlock()");
		fecBlock_log(zc_blackFec, fecblock);
		goto RETURN;
	    }
	    else {
		zlog_debug(zc_blackFec, "Packet doesn't match fecblock.  Checking next block.");
	    }
	}
	zlog_debug(zc_blackFec, "Dropped out of earlier block loop.");
	/* all earlier blocks must have expired.			*/
	/* discard parity packet.  Release source packet.		*/
	if (isParity) {
	    zlog_debug(zc_blackFec, "Reporting expired parity packet %p.", pinfo);

	    // FREE:
	    // packetinfo_free(pinfo);
	    // zlog_debug(zc_blackFec, "Successfully freed.");

	    //zlog_info(zc_blackFec, "Sending packetinfo %p to aggregator: %d/%d", pinfo, pinfo->inLinkSeq, pinfo->outLinkSeq);
	    //if(pinfo->srcEnclaveId == 0 || pinfo->dstEnclaveId == 0)
	    //{
	    //	zlog_warn(zc_blackFec,
	    //		  "%s:%d srcEnclaveId=%d, dstEnclaveId=%d, capturePoints=%d, tuple=%s",
	    //		  __FILE__, __LINE__,
	    //		  pinfo->srcEnclaveId, pinfo->dstEnclaveId,
	    //		  pinfo->capturePointsVisited,
	    //		  pinfo->pflow->tuplestr_buff);
	    //}
	    // packetinfo_auditAdd(pinfo);
	    // in immediate capture reporting, we're suppressing this sender 2 aggregator, but
	    // we then have to free the pinfo memory
	    packetinfo_free(pinfo);

	    // fistq_enqueue_pinfo(sender2aggregator, pinfo, FISTQ_FLUSH);

	    pinfo = 0;
	    returnlist = 0;
	}
	else {
	    zlog_debug(zc_blackFec, "Releasing expired source packet %p.", pinfo);
	    returnlist = pinfo;
	}
    }

 RETURN:
    zlog_debug(zc_blackFec, "Returning...  returnlist=%p", returnlist);
    struct packetinfo *p;
    for (p = returnlist; p != 0; p = p->next) {
	zlog_debug(zc_blackFec, "\tpinfo=%p, pflow=%p blockSeq=<NA> blockIndex=%d, isParity=%d",
		   p,
		   p->pflow,
		   // p->flowSeq,
		   // p->isParity ? p->flowSeq : (p->flowSeq - p->blockIndex),
		   p->blockIndex,
		   p->isParity);
    }

    /* the beginning of the list.					*/
    *pbeg = returnlist;
    /* find the end of the list.					*/
    for (pinfo = returnlist;
	 pinfo != 0 && pinfo->next != 0;
	 pinfo = pinfo->next) {
	/* do nothing.							*/
    }
    *pend = pinfo;

    if (*pbeg == 0) {
	return STATE_NOSEND;
    }
    else {
	return STATE_CONTINUE;
    }
}



