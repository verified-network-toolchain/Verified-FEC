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

//#define FECTIMEOUT  10.0  /* 10 seconds.        */
#define FECTIMEOUT 500 //JOSH - timeout after 500 unique packets have arrived
#define MAXPACKETLENGTH 65536
#define MAXSTRING 1024

// XXX: will this work ok with multiple threads?
char outstring[MAXSTRING];

//Sequence numbers
BOOLEAN seqNum_eq(struct seqNum s1, struct seqNum s2) {
  return ((u_int64_t) s1 == (u_int64_t) s2);
}

//Works as long as s1 and s2 are within 2^63-1 of each other, incorporates
//wraparound
BOOLEAN seqNum_lt(struct seqNum s1, struct seqNum s2) {
  u_int64_t i1 = (u_int64_t) s1;
  u_int64_t i2 = (u_int64_t) s2;
  return ((int64_t) (i1 - i2) < 0);
}

BOOLEAN seqNum_leq(struct seqNum s1, struct seqNum s2) {
  u_int64_t i1 = (u_int64_t) s1;
  u_int64_t i2 = (u_int64_t) s2;
  return ((int64_t) (i1 - i2) <= 0);
}

struct seqNum seqNum_sub(struct seqNum s1, int n) {
  u_int64_t i1 = (u_int64_t) s1;
  return (seqNum) (i1 - n);
} 

//Compare times, also with wraparound
BOOLEAN time_leq(u_int32_t t1, u_int32_t t2) {
  return ((int32_t) (t1 - t2) <= 0);
}

/************************************************************************/
/*                  */
/*  global variables.           */
/*                  */
/************************************************************************/


/************************************************************************/
/*                  */
/*  module-wide variables - global variables used only in the */
/*    current file.           */
/*                  */
/************************************************************************/

//JOSH - removed
//extern zlog_category_t *zc_blackFec;


/************************************************************************/
/*                  */
/*  blackFecActuator_init() - initialize.       */
/*                  */
/************************************************************************/

void blackFecActuator_init()
{
  // sender2aggregator = fistq_getHandle("sender", "aggregator", FISTQ_FREE, NULL);

  /* initialize the FEC algorithm.        */
  rse_init();

  return;
}


/************************************************************************/
/*                  */
/*  blackFecActuator_unDeduce() - remove the Deduce header from */
/*    the given packet data.  Make the necessary adjustments  */
/*    to the IP header.         */
/*                  */
/************************************************************************/
//Eliminate goto in blackFECActuator_unDeduce
unsigned char *blackFecActuator_no_deducehdr(unsigned char *packetdata, int length)
{
  unsigned char *newpacket;
  newpacket = calloc(length, sizeof(unsigned char));
  memcpy(newpacket, packetdata, length);
  return newpacket;
}

unsigned char *blackFecActuator_unDeduce(unsigned char *packetdata, int length)
{
  struct deducehdr *dhdr;
  unsigned char *newpacket;
  u_int16_t newlength;    /* length of new packet.    */
  struct ip *ipheader;  /* ipheader, used for original.   */
  struct udphdr *udph;
  unsigned char *bufptr;  /* pointer into original packet.  */
  unsigned char *nbufptr; /* pointer into new packet.   */

  u_int32_t iphl;     /* ip header length.      */
  u_int32_t size;
  u_int16_t srcport, dstport;
  u_int16_t iplen, udplen;

  bufptr = packetdata;

  ipheader = (struct ip *) bufptr;

  if (ipheader->ip_p != IPPROTO_UDP)
    return blackFecActuator_no_deducehdr(packetdata, length);

  //iphl = ipheader->ip_hl << 2 ;
  iphl = (ipheader->ip_hl_v >> 4) << 2; //JOSH - because no bitfields, we need to manually shift
  bufptr += iphl;
  udph = (struct udphdr *) bufptr;

  srcport = ntohs(udph->uh_sport);
  if (srcport != DEDUCE_SPORT)
    return blackFecActuator_no_deducehdr(packetdata, length);

  dstport = ntohs(udph->uh_dport);
  if (dstport != DEDUCE_DPORT)
    return blackFecActuator_no_deducehdr(packetdata, length);

  iplen = ntohs(ipheader->ip_len);
  udplen = ntohs(udph->uh_ulen);
  if (bufptr + udplen != packetdata + iplen)
    return blackFecActuator_no_deducehdr(packetdata, length);

  if (udplen < sizeof(struct udphdr) + sizeof(struct deducehdr))
    return blackFecActuator_no_deducehdr(packetdata, length);

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

  return newpacket;
}


/************************************************************************/
/*                  */
/*  blackFecActuator_removeHeaders() - remove headers to get to */
/*    payload for parity packets.       */
/*                  */
/************************************************************************/

unsigned char *blackFecActuator_removeHeaders(unsigned char *packetdata,
    int *length)
{
  unsigned char *tempBuffer;  /* temporary buffer for packet.   */
  int tempLength;   /* length of temporary buffer.    */
  struct ip *ipheader;  /* pointer to ip header.    */
  int iphl;     /* IP header length.      */
  unsigned char *newBuffer; /* new buffer.        */

  /* remove the deduce header.          */
  tempBuffer = blackFecActuator_unDeduce(packetdata, *length);
  ipheader = (struct ip *) tempBuffer;
  tempLength = ntohs(ipheader->ip_len);

  /* remove the IP header.            */
  //iphl = ipheader->ip_hl << 2;
  iphl = (ipheader->ip_hl_v >> 4) << 2; //JOSH - because no bitfields, we need to manually shift
  tempLength -= iphl;

  // remove the udp header
  tempLength -= sizeof(struct udphdr);

  // XXX: can save a calloc by using the same memory and memmove()
  newBuffer = calloc(tempLength, sizeof(unsigned char *));
  memcpy(newBuffer, tempBuffer + iphl + sizeof(struct udphdr), tempLength);
  free(tempBuffer);
  *length = tempLength;

  return newBuffer;
}

//Find c (the max length of a packet) in the given block
int find_c (struct fecBlock *fecblock) {
  int k = fecblock->k;
  int h = fecblock->h;
  //First, try to find a parity packet, whose length must be c
  for(int i = 0; i < h; i++) {
    struct packetinfo *pinfo = fecblock->packets[k + i];
    if (pinfo != 0) {
      return pinfo->length;
    }
  }
  //Otherwise, take the maximum of the data packets
  int maxlen = 0;
  for(int i = 0; i < k; i++) {
    fecblock->packets[k + i]
    if(fecblock->packets[i]->length > maxlen) {
      maxlen = fecblock->packets[i]->length;
    }
  }
  return maxlen;
}


struct fecBlock {
    BOOLEAN complete;   /* 1 if all needed packets received.  */
    int blockSeq;   /* flow sequence number of first packet */
        /* and all parity packets in block. */
    int k;      /* number of source packets.    */
    int h;      /* number of parity packets.    */
    struct packetinfo *packets[FECMAXBLOCKSIZE];
        /* storage for packetinfo structures. */    
    int packetCount;    /* number of packets in packet list.  */
    //double timeout;   /* last arrival time plus fixed timeout.*/
    unsigned int timeout; //JOSH - last arrival time plus fixed timeout

    struct fecBlock *prev;
    struct fecBlock *next;
};



/************************************************************************/
/*                  */
/*  blackFecActuator_regenerateMissingPackets() - call the core */
/*    FEC code to regenerate the missing packets.   */
/*                  */
/************************************************************************/

/*
JOSH - Changes
1. Remove check for isParity - any packet can be the last in the block
2. Because of this, add calculation of c
*/

struct packetinfo *blackFecActuator_regenerateMissingPackets(
  struct flow *f,
  struct fecBlock *fecblock,
  struct packetinfo *pinfo)
{
  int i;      /* loop counter.      */
  int maxn = FECMAXBLOCKSIZE; /* maximum block size supported.  */
  int k;      /* number of source packets in block. */
  int h;      /* number of parity packets in block. */
  int n;      /* total number of packets in the block.*/
  int blockIndex;   /* sequence number for given packet in  */
  /* given block.       */
  int maxpacketsize;    /* maximum packet size = size of parity */
  /* packet.        */
  struct packetinfo *newpinfo;/* packetinfo structure for regenerated */
  /* packet.        */
  struct packetinfo *plist = 0;
  /* list of output packets.    */
  struct packetinfo *plisttail = 0;
  /* tail of output list.     */
  struct ip *ipheader;  /* pointer to ip header.    */
  struct ip *newipheader; /* pointer to ip header.    */
  int length;     /* temporary storage for length.  */

  /* allocate initial arrays for storing packet pointers.   */
  if (f->bpacketsizes == 0) {
    f->bpacketptrs = calloc(sizeof(unsigned char *), maxn);
    f->bpacketsizes = calloc(sizeof(int), maxn);
    f->bpstat = calloc(sizeof(char), maxn);
  }
  else {
    // XXX: memory leak? we calloc f->bpacketptrs[i] but hardly ever free
    //JOSH - fixed below
    memset(f->bpacketptrs, 0, maxn * sizeof(unsigned char *));
    memset(f->bpacketsizes, 0, maxn * sizeof(int));
    memset(f->bpstat, 0, maxn);
  }

  k = fecblock->k;
  h = fecblock->h;
  n = k + h;

  assert(n <= maxn);

  /* the passed packet should be a parity packet, so its length */
  /* should equal the maximum in the block.       */
  if(pinfo->isParity) {
    maxpacketsize = pinfo->length;
  }
  else {
    maxpacketsize = find_c(fecblock);
  }
  

  /* get the packet sequence number (within the block) for the  */
  /* provided parity packet.            */
  blockIndex = pinfo->blockIndex;

  /* initialize the structures needed by the fec algorithm.   */
  /* handle the source packets.         */
  for (i = 0; i < k; i++) {
    /* allocate space for missing packet and mark it as wanted. */
    if (fecblock->packets[i] == 0) {
      f->bpstat[i] = FEC_FLAG_WANTED;
      f->bpacketptrs[i] = calloc(maxpacketsize, sizeof(unsigned char));
      f->bpacketsizes[i] = maxpacketsize;
    }
    /* for present packet, copy information to structures.    */
    else {
      //      f->bpacketptrs[i] = fecblock->packets[i]->packetdata;
      f->bpacketptrs[i] = blackFecActuator_unDeduce(fecblock->packets[i]->packetdata,
                          fecblock->packets[i]->length);
      ipheader = (struct ip *) f->bpacketptrs[i];
      f->bpacketsizes[i] =  ntohs(ipheader->ip_len);
      fecCommon_maskHeader((struct ip *) f->bpacketptrs[i]);
    }
  }
  /* handle the parity packets.         */
  /* Could have set upper bound to blockIndex, but setting it to n  */
  /* allows packets to have arrived out of order.     */
  for (i = k; i < n; i++) {
    if (i == blockIndex) {
      continue;
    }
    /* for present packet, copy information to structures.    */
    if (fecblock->packets[i] != 0) {
      /* remove headers.            */
      length = fecblock->packets[i]->length;
      f->bpacketptrs[i] = blackFecActuator_removeHeaders(fecblock->packets[i]->packetdata,
                          &length);
      f->bpacketsizes[i] = length;
    }
  }
  /* copy the information from the given packetinfo structure.  */
  /* remove the headers.            */
  // XXX: TODO: This assumes this packet (blockindex) is parity packet.
  length = pinfo->length;
  f->bpacketptrs[blockIndex] = blackFecActuator_removeHeaders(pinfo->packetdata,
                               &length);
  f->bpacketsizes[blockIndex] = length;

  /* call the packet regeneration code.       */
  for (i = 0; i < n; i++)
    rse_code(k, 0, maxpacketsize, f->bpacketptrs, f->bpacketsizes, f->bpstat);

  /* create the packetinfo structures for the regenerated packets.  */
  for (i = 0; i < k; i++) {
    /* only generate structure for packet that was missing.   */
    if (fecblock->packets[i] == 0) {
      /* expect non-zero first byte of IP header.  If zero, */
      /* the regenerated packet never existed.      */
      if (f->bpacketptrs[i][0] == 0) {
        free(f->bpacketptrs[i]);
        continue;
      }
      /* allocate and initialize a new packetinfo structure.  */
      newpinfo = packetinfo_copyNoData(pinfo);

      /* add the copy to the list to return.      */
      if (plist == 0) {
        plist = newpinfo;
      }
      else {
        plisttail->next = newpinfo;
      }
      plisttail = newpinfo;

      /* thought we could use the data as is since we allocated */
      /* the space earlier, but causes problems.      */
      newpinfo->packetdata = calloc(f->bpacketsizes[i], sizeof(unsigned char));
      memcpy(newpinfo->packetdata, f->bpacketptrs[i], f->bpacketsizes[i]);

      /* adjust the IP header.          */
      /* copy information from given parity packet.   */
      ipheader = (struct ip *) pinfo->packetdata;
      newipheader = (struct ip *) newpinfo->packetdata;
      newipheader->ip_ttl = ipheader->ip_ttl;

      newpinfo->length = ntohs(newipheader->ip_len);

      // regenerated packet has no deduce header
      // iphdrsize should be the same as old.
      newpinfo->udphdrsize = 0;
      newpinfo->deducehdrsize = 0;
      newpinfo->deduceparamsizeWithPad = 0;
      newpinfo->deduceparamsizeWithoutPad = 0;
      newpinfo->remaindersize = newpinfo->length - newpinfo->iphdrsize;

      /* adjust parameters.         */
      newpinfo->blockIndex = i;
      newpinfo->isParity = 0;

      //JOSH - here, need to free f->bpacketptrs[i], or else memory leak
      //We only freed the data for nonexistent packets, not packets that
      //existed but were lost
      free(f->bpacketptrs[i]);
    }
  }

  return plist;
}


/************************************************************************/
/*                  */
/*  blackFecActuator_initBlockWithPacket() - initialize the given */
/*    block structure with information from a packet.  If the */
/*    packet is a source packet, a copy will be stored and  */
/*    the original will be returned.  If it is a parity */
/*    packet then it will be saved and a null pointer (0) */
/*    will be returned.         */
/*                  */
/************************************************************************/

/*
JOSH: Changes to this function:
1. Remove check for duplicate packet - this is a new block
2. Store packet in block no matter what
*/

struct packetinfo *blackFecActuator_initBlockWithPacket(
  struct flow *f,
  struct fecBlock *fecblock,
  struct packetinfo *pinfo,
  int blockSeq,   /* sequence number for block.   */
  int k,      /* number of source packets.    */
  int h,      /* number of parity packets.    */
  int pindex,   /* packet index in block.   */
  BOOLEAN isParity, /* 1 if parity packet.      */
  unsigned int timeout /* timeout for block.     */
  )   
{
  struct packetinfo *newpinfo;
  /* regenerated packet list.   */

  /* initilize the block.           */
  fecblock->blockSeq = blockSeq;
  fecblock->k = k;
  fecblock->h = h;
  fecblock->packetCount++;
  fecblock->timeout = timeout;

  /* add the packet to the new block.         */
  /* parity packets are not to be released to the pipeline, so their  */
  /* information can just be saved.         */


  if (isParity) {
    fecblock->packets[pindex] = pinfo;
    if (fecblock->packetCount == fecblock->k) {
      fecblock->complete = 1;
      //newpinfo
      //  = blackFecActuator_regenerateMissingPackets(f,
      //      fecblock,
      //      pinfo);
      // FREE: We still need to free this since a new packet info is created
      //JOSH - why do they free this packet? We still want it in the structure to
      // check for duplicates 
      //packetinfo_free(pinfo);

      return newpinfo;
    }
    return 0;
    //else {
    //  return 0;
   //}
  }
  /* source packets are released to the pipeline, so a copy needs */
  /* to be made in case it is needed to regenerate a missing packet.  */
  else {
    fecblock->packets[pindex] = packetinfo_copyWithData(pinfo);
    if (fecblock->packetCount == fecblock->k) {
      fecblock->complete = 1;
      //JOSH - don't need to decode because only 1 data packet, which we found

      //fecblock->packets[pindex] = 0;
    }
    return pinfo;
  }
}


/************************************************************************/
/*                  */
/*  blackFecActuator_addPacketToBlock() - add a new packet to the */
/*    given block.  Returns 0 if parity packet (either  */
/*    because stored, or because block is already complete).  */
/*    Returns the packet if source packet.      */
/*                  */
/************************************************************************/

/*
JOSH - Changes
1. Still release data packet if complete
2. Still store packets if complete (to detect duplicates)
3. Do not free parity packet, keep stored in block
4. Decode even if parity packet (data packet may be kth)
*/
struct packetinfo *blackFecActuator_addPacketToBlock(struct flow *f,
    struct fecBlock *fecblock,
    struct packetinfo *pinfo)
{
  struct packetinfo *newpinfo;  /* copy of original packetinfo  */
  /* structure.     */

  //JOSH - first, check if the packet is there to know whether to update the time
  if (fecblock->packets[pinfo->blockIndex] == 0) {
    fecblock->packetCount++;
    flow->time++; //increase time because new packet

    //store packet
    if (pinfo->isParity) {
      fecblock->packets[pinfo->blockIndex] = pinfo;
    }
    else {
      fecblock->packets[pinfo->blockIndex] = packetinfo_copyWithData(pinfo);
    }

    //if complete, done
    //TODO: refactor this out?
    if(fecblock->complete == 1) {
      if(!pinfo->isParity) {
        return pinfo;
      }
      else {
        //JOSH - TODO: why do they free pinfo, still in structure?
        return 0;
      }
    }

    //Otherwise, see if we need to decode
    /* packet completes block.            */
    if (fecblock->packetCount == fecblock->k) {
      /* mark the block as complete.          */
      fecblock->complete = 1;
      /* if it's a parity packet, then recompute missing packets. */
      newpinfo
          = blackFecActuator_regenerateMissingPackets(f,
              fecblock,
              pinfo);
        // FREE:
      //packetinfo_free(pinfo);
      if(!pinfo->isParity) {
        pinfo->next = newpinfo;
        newpinfo = pinfo;
      }
      //Return original packet if data + regenerated packets
      return newpinfo;
    }

    //Otherwise, just release data packet
    if(!pinfo->isParity) {
      return pinfo;
    }
    else {
      return 0;
    }

  }
}


/************************************************************************/
/*                  */
/*  blackFecActuator() - processes incoming source and FEC parity */
/*    packets to regenerate missing source packets.   */
/*    Takes a packetinfo structure describing a packet, */
/*    saves copies of the structures for both source and  */
/*    parity packets until the required number of packets has */
/*    been received, returning the original source packet */
/*    structures as they arrive, and regenerating and   */
/*    returning structures for missing source packets once  */
/*    the required number of packets has been received. */
/*    If the required number of packets is not received and */
/*    a new FEC block starts, all stored structures are */
/*    freed.              */
/*                  */
/************************************************************************/

//Eliminate GOTO
u_int32_t blackFecActuator_return(struct packetinfo **pbeg,
                                  struct packetinfo **pend, struct packetinfo *returnlist) {
  struct packetinfo *p;
  struct packetinfo *pinfo;

  /* the beginning of the list.         */
  *pbeg = returnlist;
  /* find the end of the list.          */
  for (pinfo = returnlist; pinfo != 0 && pinfo->next != 0; pinfo = pinfo->next) {
    /* do nothing.              */
  }
  *pend = pinfo;

  if (*pbeg == 0) {
    return STATE_NOSEND;
  }
  else {
    return STATE_CONTINUE;
  }
}

DECLARE(blackFecActuator)
//struct packetinfo *blackFecActuator(struct packetinfo *pinfo)
{
  struct fecParams fecparams; /* FEC parameters from packet.    */
  struct flow *f;   /* flow structure for packet.   */
  int k;      /* number of source packets in block. */
  int h;      /* number of parity packets in block. */
  // struct deducehdr *dheader; /* deduce header.     */
  struct seqNum flowSeq;
  //int flowSeq;    /* flow sequence number for packet. */
  int pindex;     /* packet index within block.   */
  BOOLEAN isParity;   /* flag indicating packet is parity */
  /* packet.        */
  struct seqNum blockSeq;
  //int blockSeq;   /* block sequence number: flow sequence */
  /* number of first packet in FEC block. */
  u_int32_t currTime;    /* current time (Unix time with   */
  /* microseconds).     */
  struct fecBlock *currblock; /* current (most recent) FEC block. */
  struct fecBlock *fecblock;  /* packet's fec block if not current. */
  struct fecBlock *oldblock;  /* previous fec block in list.    */
  struct fecBlock *newblock;  /* newly created fec block.   */
  struct fecBlock *fecblocknext;
  /* next fec block in list.    */
  struct packetinfo *returnlist;
  /* list of packet structures to return. */

  /* get the FEC parameters from the packet.        */
  packetinfo_getAParam(pinfo, &fecparams, sizeof(struct fecParams));
  k = fecparams.fec_k;
  h = fecparams.fec_h;
  pindex = fecparams.fec_seq;
  flowSeq.seq_high = ntohl(fecparams.block_seq1);
  flowSeq.seq_low = ntohl(fecparams.block_seq2);
  //flowSeq = ntohl(fecparams.block_seq);
  blockSeq = 0;
  pinfo->blockIndex = pindex;

  /* determine whether source or parity packet and determine the  */
  /* block number for the packet.  The block is identified by the flow*/
  /* sequence number of first packet in block.  Parity packets have */
  /* the same flow sequence number as the first packet in the block.  */
  if (pindex < k) {   /* source packet.     */
    isParity = 0;
    pinfo->isParity = 0;
    blockSeq = seqNum_sub(flowSeq, pindex);
    //blockSeq = flowSeq - pindex;
    // blockSeq = 0 ;              // TO DO: Add it to deduce header, or make it a parameter
  }
  else {      /* parity packet.     */
    isParity = 1;
    pinfo->isParity = 1;
    blockSeq = flowSeq;
    //blockSeq = flowSeq;
    // blockSeq = 0 ;            // TO DO: Add it to deduce header, or make it a parameter
  }

  /* FEC state is stored in the flow structure associated with the  */
  /* packet.                */
  f = pinfo->pflow;

  /* get the current time to use for setting and checking timeouts. */
  currTime = f->time;

  /* the current block is the last block in the flow's block list.  */
  currblock = f->blockListTail;

  /* handle case of empty block list.  Create a new block for the */
  /* packet and initialize the list.          */
  // JOSH - in this case, it is safe to not timeout anything
  if (currblock == 0) {

    /* initialize the block list with a new block structure.  */
    currblock = fecBlock_new();
    f->blockListHead = currblock;
    f->blockListTail = currblock;
    /* initialize the new block structure with the information  */
    /* from the current packet.         */
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
    return blackFecActuator_return(pbeg, pend, returnlist);
  }

  // JOSH - part 1: find the block corresponding to the packet, 
  // or create it if no block exists. Generate the packets to
  // return and update the time appropriately.
  // We will process timeouts later

  /* packet is for current block.  This implies that the packet's */
  /* FEC type is the same as that of the current block.  Add the  */
  /* packet to the block and use it to regenerate missing packets */
  /* if it completes the block.  A list of source and regenerated */
  /* packets will be returned.  Parity packets will just be stored  */
  /* or deleted.
                */
  if(seqNum_eq(blockSeq, currblock->blockSeq)) {

    returnlist = blackFecActuator_addPacketToBlock(f,
                 currblock,
                 pinfo);
    //return blackFecActuator_return(pbeg, pend, returnlist);
  }

  /* packet is for a newer block (i.e. a block following the current  */
  /* block).  Since it's a new block, it doesn't matter if the packet */
  /* has the same FEC type as the current block.  Create the new  */
  /* block.  If the previous block hasn't completed it will   */
  /* eventually complete and/or expire.       */
  else if (seqNum_lt(currblock->blockSeq, blockSeq)) {
  //else if (blockSeq > currblock->blockSeq) {

    /* insert a new block structure into the block list.    */
    oldblock = currblock;
    currblock = fecBlock_new();
    oldblock->next = currblock;
    currblock->prev = oldblock;
    pinfo->pflow->blockListTail = currblock;
    /* initialize the new block structure with the information  */
    /* from the current packet.         */
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

    //return blackFecActuator_return(pbeg, pend, returnlist);
  }

  /* packet belongs to a previous block.  The block could be of the */
  /* same FEC type as the current block or a different FEC type.  */

  //TODO: 


  else {  /* blockSeq < fecblock->blockSeq      */

    /* find the block.  While searching, delete expired blocks  */
    /* if convenient.  (If the packet belongs to an expired block,  */
    /* the later expired blocks won't be deleted in this round.)  */
    
    for (fecblock = f->blockListHead; fecblock != currblock;
         fecblock = fecblock->next) {
      //Found block
      if(seqNum_eq(blockSeq, fecblock->blockSeq)) {
        returnlist =  blackFecActuator_addPacketToBlock(f,
                     fecblock,
                     pinfo);
      }
      //No block for this packet, add it
      else if(seqNum_lt(blockSeq, fecblock->blockSeq)) {
        /* insert a new block structure into the block list.  */
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
        /* initialize the new block structure with the    */
        /* information from the current packet.     */
        /* Note: had been initializing fecblock rather than */
        /* newblock, and was getting rare core dumps.  With */
        /* this fix, shouldn't have the core dumps.   */
        /* (bss 11/28/2017)         */
        returnlist = blackFecActuator_initBlockWithPacket(
                       f,
                       newblock, /* had been fecblock */
                       pinfo,
                       blockSeq,
                       k,
                       h,
                       pindex,
                       isParity,
                       currTime + FECTIMEOUT);
      }
    }
  }

  //JOSH: part 2: process timeouts, if time changed
  u_int32_t newTime = f->time;
  if(currTime != newTime) {
    fecblocknext = 0;
    for (fecblock = f->blockListHead; fecblock != 0;
      fecblock = fecblocknext) {

      /* save the next pointer in case block is deleted.    */
      fecblocknext = fecblock->next;

      if(!(time_leq(newTime, fecblock->timeout))) {
        //delete expired block
        /* remove the block from the flow's block list. */
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
        fecBlock_free(fecblock);
      }

    }
  }

  //Now return the packets
  return blackFecActuator_return(pbeg, pend, returnlist);
}



