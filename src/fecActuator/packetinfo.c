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
 

#include "packetinfo.h"
#include "flow.h"


/* -------------------------------------------------------------------------------------------------
 *	global variables.			
 * -------------------------------------------------------------------------------------------------
 */


/* -------------------------------------------------------------------------------------------------
 *	module variables  - global variables used only in the current file		
 * -------------------------------------------------------------------------------------------------
 */


/* -------------------------------------------------------------------------------------------------
 *  packetinfo_new() - create and initialize a new packetinfo structure.
 * -------------------------------------------------------------------------------------------------
 */
struct packetinfo *packetinfo_new()
{
  struct packetinfo *packetinfo_p;

  packetinfo_p = (struct packetinfo *) calloc(1, sizeof(struct packetinfo));

  return packetinfo_p;
}


/* ---------------------------------------------------------------------------------------
 * packetinfo_free() - free the given packetinfo structure.	
 * ---------------------------------------------------------------------------------------
 */
void packetinfo_free(struct packetinfo *packetinfo_p)
{
  if (packetinfo_p->packetdata != (unsigned char*) NULL) 
    {
      free(packetinfo_p->packetdata);
    }

  /* clear in case referenced after freed.  (bss 8/1/2016)		*/
  memset(packetinfo_p, 0, sizeof(struct packetinfo));

  free(packetinfo_p);

  return;
}


/* ---------------------------------------------------------------------------------------
 * packetinfo_copyNoData() - return a copy of the given packetinfo structure.  
 *                           Do not copy the packetdata.	
 * ---------------------------------------------------------------------------------------
 */
struct packetinfo *packetinfo_copyNoData(struct packetinfo *pinfo)
{
  struct packetinfo *pcopy;

  pcopy = packetinfo_new();
  memcpy(pcopy, pinfo, sizeof(struct packetinfo));

  pcopy->packetdata = 0;
  pcopy->length = 0;

  pcopy->next = 0;
    
  return pcopy;
}


/* ---------------------------------------------------------------------------------------
 * packetinfo_copyWithData() - return a copy of the given packetinfo.  
 *                             Also copy the packetdata.		
 * ---------------------------------------------------------------------------------------
 */
struct packetinfo *packetinfo_copyWithData(struct packetinfo *pinfo)
{
  struct packetinfo *pcopy;

  pcopy = packetinfo_new();
  memcpy(pcopy, pinfo, sizeof(struct packetinfo));

  /* packetdata needs to be copied.					*/
  pcopy->packetdata = calloc(1, pinfo->length);
  memcpy(pcopy->packetdata, pinfo->packetdata, pinfo->length);

  pcopy->next = 0;
  return pcopy;
}


// return iphdr in the pinfo->packetdata.
struct ip *packetinfo_get_iphdr(struct packetinfo *pinfo)
{
  return ((struct ip *) pinfo->packetdata);
}


// return deducehdr in the pinfo->packetdata.
struct deducehdr *packetinfo_get_deducehdrFromPacket(struct packetinfo *pinfo)
{
  unsigned char *bufptr;

  if (pinfo->deducehdrsize == 0)
    return NULL;

  bufptr = pinfo->packetdata;
  bufptr += pinfo->iphdrsize + pinfo->udphdrsize;

  return (struct deducehdr *) bufptr;
}


struct deducehdr *packetinfo_get_deducehdrFromExternal(struct packetinfo *pinfo)
{
  return &pinfo->shim;
}


/* ---------------------------------------------------------------------------------------
 * packetinfo_addAParam() - add to Actuator Parameters in packetinfo structure.					
 * ---------------------------------------------------------------------------------------
 */
void packetinfo_addAParam(struct packetinfo *pinfo, void *data, size_t len)
{
    // assume actuatorIndex is set properly
    // push on like a stack
    memcpy(pinfo->actuatorParams+pinfo->actuatorIndex, data, len);
    pinfo->actuatorIndex += len;
}


/* ---------------------------------------------------------------------------------------
 * packetinfo_getAParam() - get Actuator Parameters from packetinfo structure.	
 * ---------------------------------------------------------------------------------------
 */
void packetinfo_getAParam(struct packetinfo *pinfo, void *data, size_t len)
{
    // assume actuatorIndex is set properly
    // pop off like a stack
    pinfo->actuatorIndex -= len;
    memcpy(data, pinfo->actuatorParams+pinfo->actuatorIndex, len);
}


// return remainder in the pinfo->packetdata.
void *packetinfo_get_remainder(struct packetinfo *pinfo)
{
    unsigned char *bufptr;

    bufptr = pinfo->packetdata;
    bufptr += pinfo->iphdrsize + pinfo->udphdrsize + pinfo->deducehdrsize + pinfo->deduceparamsizeWithPad;

    return bufptr;
}


void packetinfo_remove_deducehdr(zlog_category_t* zc, struct packetinfo *pinfo)
{
    struct ip *iph;
    unsigned char *endIp, *startRemainder;

    if (pinfo->deducehdrsize == 0)
    {
	zlog_trace(zc, "No shim, so no change to packet");
	return;
    }

    zlog_trace(zc, "Removing shim from packet");

    // restore ip addrs, proto, length
    iph = packetinfo_get_iphdr(pinfo);
    iph->ip_src.s_addr = pinfo->shim.origSrcIpAddr;
    iph->ip_dst.s_addr = pinfo->shim.origDstIpAddr;
    iph->ip_p = pinfo->shim.origIpProtocol;
    iph->ip_len = htons(pinfo->iphdrsize + pinfo->remaindersize);

    // move original remainder of packet to end of iphdr.
    endIp = startRemainder = pinfo->packetdata;
    endIp += pinfo->iphdrsize;
    startRemainder += pinfo->iphdrsize + pinfo->udphdrsize + pinfo->deducehdrsize + pinfo->deduceparamsizeWithPad;
    memmove(endIp, startRemainder, pinfo->remaindersize);

    // zero out indicators of a black packet.
    pinfo->udphdrsize = 0;
    pinfo->deducehdrsize = 0;
    pinfo->deduceparamsizeWithPad = 0;
    pinfo->deduceparamsizeWithoutPad = 0;
    // May need this after removing deduce hdrs pinfo->actuatorIndex = 0;

    pinfo->length = pinfo->iphdrsize + pinfo->remaindersize;
}


void packetinfo_rebuild(struct packetinfo *pinfo)
{
    struct ip *iph;
    size_t nlen;
    u_int32_t slen, aslen, len;
    unsigned char *npacketdata;
    unsigned char *pktstart, *pkt, *npkt;
    int isNew;

    // get size of actuator params
    slen = pinfo->actuatorIndex;

    // get aligned length, extended to next word bundary
    aslen = (slen + 3) & 0xfffc;

    isNew = pinfo->deduceparamsizeWithPad < aslen;

    // new length is old length + new param size - old param size
    nlen = pinfo->length + aslen - pinfo->deduceparamsizeWithPad;
    if (isNew)
	// rebuilt packet larger, so use new storage.
	npacketdata = malloc(nlen);
    else
	// rebuilt packet may be same size or smaller os use same storage.
	npacketdata = pinfo->packetdata;

    pktstart = pinfo->packetdata;
    pkt = pktstart;
    npkt = npacketdata;

    // first copy ip header and transport header
    len = pinfo->iphdrsize + pinfo->udphdrsize;
    if (isNew)
	memcpy(npkt, pkt, len);

    // adjust pointers to past the headers
    npkt += len;
    pkt += len;

    // copy shim (working storage for the new packet deduce hdr)
    pinfo->shim.paramSize = pinfo->actuatorIndex;
    memcpy(npkt, &pinfo->shim, sizeof(struct deducehdr));

    // move past deduce hdr
    npkt += sizeof(struct deducehdr);
    pkt += sizeof(struct deducehdr);

    // copy params
    if (aslen > 0)
	memcpy(npkt, &pinfo->actuatorParams, aslen);

    // move past params
    npkt += aslen;
    pkt += pinfo->deduceparamsizeWithPad;

    // copy remainder of packet
    // if same size, then remainder does not need to be moved.
    if (npkt != pkt)
    {
	memmove(npkt, pkt, pinfo->remaindersize);

	if (isNew)
	{
	    // swap in new packetdata
	    free(pinfo->packetdata);
	}
	pinfo->packetdata = npacketdata;
	pinfo->length = nlen;

	// fix up sizes
	pinfo->deduceparamsizeWithPad = aslen;
	pinfo->deduceparamsizeWithoutPad = slen;

	iph = (struct ip *) pinfo->packetdata;
	iph->ip_len = htons(pinfo->length);
    }
}


struct packetinfo *packetinfo_insert_deducehdr(struct packetinfo *pinfo)
{
    struct ip *iph;
    struct udphdr *uhdr;
    u_int32_t slen, aslen, len;
    size_t nlen;
    u_int8_t *npacketdata, *pktstart, *pkt, *npkt;

    // get size of actuator params
    slen = pinfo->actuatorIndex;

    // get aligned length, extended to next word bundary
    aslen = (slen + 3) & 0xfffc;

    // fix up sizes
    pinfo->udphdrsize = sizeof(struct udphdr);
    pinfo->deducehdrsize = sizeof(struct deducehdr);
    pinfo->deduceparamsizeWithPad = aslen;
    pinfo->deduceparamsizeWithoutPad = slen;

    // get size of new packet with deduce header and params
    nlen = pinfo->iphdrsize + pinfo->udphdrsize + pinfo->deducehdrsize + pinfo->deduceparamsizeWithPad + pinfo->remaindersize;
    npacketdata = malloc(nlen);

    pktstart = pinfo->packetdata;

    npkt = npacketdata;
    pkt = pktstart;

    // first copy ip header
    len = pinfo->iphdrsize;
    memcpy(npkt, pkt, len);

    // move past ip hdr
    npkt += len;
    pkt += len;

    // put in new udphdr
    uhdr = (struct udphdr *)npkt;
    uhdr->uh_sport = ntohs(DEDUCE_SPORT);
    uhdr->uh_dport = ntohs(DEDUCE_DPORT);
    uhdr->uh_sum = 0;
    uhdr->uh_ulen = htons(pinfo->udphdrsize + pinfo->deducehdrsize + pinfo->deduceparamsizeWithPad + pinfo->remaindersize);

    // move past udphdr
    npkt += pinfo->udphdrsize;

    // put in new deducehdr
    pinfo->shim.paramSize = pinfo->actuatorIndex;
    memcpy(npkt, &pinfo->shim, pinfo->deducehdrsize);

    // move past deduce hdr
    npkt += pinfo->deducehdrsize;

    // copy in params
    if (pinfo->deduceparamsizeWithPad > 0)
    {
	memcpy(npkt, &pinfo->actuatorParams, pinfo->deduceparamsizeWithPad);

	// move past params
	npkt += pinfo->deduceparamsizeWithPad;
    }

    // copy remainder of packet
    memcpy(npkt, pkt, pinfo->remaindersize);

    // swap in new packetdata
    free(pinfo->packetdata);
    pinfo->packetdata = npacketdata;
    pinfo->length = nlen;

    // fix iphdr addrs, len, protocol
    // addresses were set in redActuatorRouting
    iph = (struct ip *) pinfo->packetdata;
    iph->ip_len = htons(pinfo->length);
    iph->ip_p = IPPROTO_UDP;

    struct packetinfo *pnext = pinfo->next;
    pinfo->next = NULL;

    return pnext;
}


/* ---------------------------------------------------------------------------------------
 * packetinfo_print() - print out a summary of the contents of the given packetinfo 
 *                      structure.			
 * ---------------------------------------------------------------------------------------
 */
void packetinfo_print(FILE *ofp, struct packetinfo *pinfo)
{
    char srcaddrString[128];
    char dstaddrString[128];
    struct sockaddr_in sa;
    int addressfamily = AF_INET;
    struct flowTuple *ft = pinfo->tuple;

    if (ft->ipversion == 6) {
	addressfamily = AF_INET6;
    }
    sa.sin_addr.s_addr = htonl(ft->srcaddr);
    inet_ntop(addressfamily,
		   &(sa.sin_addr),
		   srcaddrString, 128);
    sa.sin_addr.s_addr = htonl(ft->dstaddr);
    inet_ntop(addressfamily,
		   &(sa.sin_addr),
		   dstaddrString, 128);

    fprintf(ofp, "Flow %d: %s:%d->%s:%d, proto %d, hash=%d, new=%d\n",
	    ((pinfo->pflow != 0) ? pinfo->pflow->flowid : (u_int32_t)-1),
	    srcaddrString, ft->srcport,
	    dstaddrString, ft->dstport,
	    ft->protocol,
	    pinfo->flowhash,
	    pinfo->newFlow);
    fprintf(ofp, "\t Composition %d\n", pinfo->compId);
    fprintf(ofp, "\tpacketdata=%p, length=%d, deducehdrsize=%d\n",
	    pinfo->packetdata, pinfo->length, pinfo->deducehdrsize);

    return;
}

/* ---------------------------------------------------------------------------------------
 *  packetinfo_log() - log a summary of the contents of the given packetinfo structure, at 
 *                     the given category and log     
 * ---------------------------------------------------------------------------------------
 */
void packetinfo_log(zlog_category_t* zc, zlog_level zl, struct packetinfo *pinfo)
{
    char srcaddrString[128];
    char dstaddrString[128];
    struct sockaddr_in sa;
    int addressfamily = AF_INET;
    struct flowTuple *ft = pinfo->tuple;

    /* ------------------------------------------------------
     * Don't build the message if it won't be actually logged
     * ------------------------------------------------------
     */
    if( !isUsefulLevel(zc,zl))
      return;

    /* if( getDcpsLogstyle() == DCPS_LOGSTYLE_GREP )  */
    /*   { */
    /*   packetinfo_logOneLine( zc, zl, pinfo ) ; */
    /*   return ; */
    /*   } */

    if (ft->ipversion == 6) {
	addressfamily = AF_INET6;
    }
    sa.sin_addr.s_addr = htonl(ft->srcaddr);
    inet_ntop(addressfamily,
		   &(sa.sin_addr),
		   srcaddrString, 128);
    sa.sin_addr.s_addr = htonl(ft->dstaddr);
    inet_ntop(addressfamily,
		   &(sa.sin_addr),
		   dstaddrString, 128);

    zlog_gen(zc, zl, "Packetinfo Flow %d: %s:%d->%s:%d, proto %d, hash=%d, new=%d",
	    ((pinfo->pflow != 0) ? pinfo->pflow->flowid : (u_int32_t)-1),
	    srcaddrString, ft->srcport,
	    dstaddrString, ft->dstport,
	    ft->protocol,
	    pinfo->flowhash,
	     pinfo->newFlow);
    zlog_gen(zc, zl, "\t\tComposition %d", pinfo->compId);
    zlog_gen(zc, zl, "\t\tpacketdata=%p, length=%d, deducehdrsize=%d",
	    pinfo->packetdata, pinfo->length, pinfo->deducehdrsize);

    return;
}

/* ---------------------------------------------------------------------------------------
 *	packetinfo_logOneLine() - log a summary of the contents of the packet info 
 *                                 structure as a single line message with key value pairs 
 *                                 for each field, at the given category and log level.
 * ---------------------------------------------------------------------------------------
 */
void packetinfo_logOneLine(zlog_category_t* zc, zlog_level zl, struct packetinfo *pinfo)
{
  char logbuf[8192] ;
  size_t dummy ;
  
  packetinfo_log2str( logbuf, 8192, pinfo, &dummy ) ;
  zlog_gen(zc, zl, "%s", logbuf); 

  return ;
}

/*************************************************************************/
/*                                                                       */
/*     packetinfo_log2str() - log a summary of the contents of the       */
/*             packet info structure to a string with key value pairs    */
/*             for each field.                                           */
/*                                                                       */
/*************************************************************************/

void packetinfo_log2str( char* logbuf, 
			 size_t logbuflen, 
			 struct packetinfo* pinfo, 
			 size_t* outlen ) {

  char srcaddrString[128];
  char dstaddrString[128];
  struct sockaddr_in sa;
  int addressfamily = AF_INET;
  struct flowTuple *ft = pinfo->tuple;

  char* cp = logbuf ;
  size_t bytes_left = logbuflen ;
  size_t b = 0 ;

  if (ft->ipversion == 6) {
    addressfamily = AF_INET6;
  }
  sa.sin_addr.s_addr = htonl(ft->srcaddr);
  inet_ntop(addressfamily,
	    &(sa.sin_addr),
	    srcaddrString, 128);
  sa.sin_addr.s_addr = htonl(ft->dstaddr);
  inet_ntop(addressfamily,
	    &(sa.sin_addr),
	    dstaddrString, 128);

  b = snprintf( cp, bytes_left, "pi.flow %d  pi.mini %s:%d->%s:%d  pi.proto %d  pi.hash %d  pi.new %d",
		((pinfo->pflow != 0) ? pinfo->pflow->flowid : (u_int32_t)-1),
		srcaddrString, ft->srcport,
		dstaddrString, ft->dstport,
		ft->protocol,
		pinfo->flowhash,
		pinfo->newFlow);
  cp += b ;
  bytes_left -= b ;

  b = snprintf( cp, bytes_left, "pi.comp %d ",
		pinfo->compId );
  cp += b ;
  bytes_left -= b ;

  b = snprintf( cp, bytes_left, "pi.pkt %p  pi.len %d  pi.dhsz %d  ",
		pinfo->packetdata, pinfo->length, pinfo->deducehdrsize);
  bytes_left -= b ;

  *outlen = logbuflen - bytes_left ;
  return;
}
