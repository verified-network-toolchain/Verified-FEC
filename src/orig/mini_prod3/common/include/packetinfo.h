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

#ifndef _PACKETINFO_H_
#define _PACKETINFO_H_

#include "common.h"
#include "composition.h"
#include "overlayhdr.h"



// values for packetinfo.origin
#define FROM_BLACK_IFACE 1
#define FROM_RED_IFACE   2

// values for packetinfo.destination
#define TO_BLACK_IFACE 1
#define TO_RED_IFACE   2

#define QUEUE_RED		"redqueue"
#define QUEUE_BLACK		"blackqueue"


/************************************************************************/
/*									*/
/*	data structures.						*/
/*									*/
/************************************************************************/


struct packetinfo {
    char *queue;		/* queue that structure was created for.*/
    int number;			/* packetinfo number for queue.		*/
    
    /* identifying information.						*/

    struct flowTuple *tuple;	/* information uniquely identifying	*/
				/* flow.				*/
    u_int32_t flowhash;		/* hash value for flow (not unique, but	*/
				/* for quicker lookup in combination	*/
				/* with flow tuple.).			*/
    struct flow *pflow;		/* flow that packet belongs to.		*/

    BOOLEAN newFlow;		/* flag for first packet in flow.	*/
  u_int32_t flow_seq;           

    /* packet metadata.							*/
    struct nfq_q_handle *qh;	/* queue handle.			*/
    u_int32_t nfPacketId;	/* packet ID from netfilter.		*/

    int compId;			/* composition ID assigned to packet.	*/
    struct composition *comp;	/* composition assigned to packet.	*/

    /* packet data.							*/
    unsigned char *packetdata;
    u_int32_t origLength;	/* original length of packetdata.	*/
    u_int32_t length;		/* current length of packetdata.	*/

    /* parts of the packetdata                                          */
    u_int32_t iphdrsize;
    u_int32_t udphdrsize;
    u_int32_t deducehdrsize;
    u_int32_t deduceparamsizeWithPad;
    u_int32_t deduceparamsizeWithoutPad;
    u_int32_t remaindersize;

    // the actuator params "stack" for this packet when traveling the black
    struct deducehdr shim; // contents are in host byte order
    u_int8_t actuatorParams[256];
    u_int32_t actuatorIndex;

    // where this packet came from and is going to internally
    // (red iface, black iface)
    int origin, destination;

    /* FEC information for packet.					*/
    int fec_k;			/* FEC used for packet.			*/
    int fec_h;
    
    /* actuator information that must be put in / extracted from	*/
    /* deduce header.							*/
    //    int fecType;		/* FEC type.				*/
    int isParity;		/* flag to identify FEC parity packet.	*/
    int blockIndex;		/* sequence number within FEC block.	*/

    struct packetinfo *next;
};


/************************************************************************/
/*									*/
/*	global variables.						*/
/*									*/
/************************************************************************/


/************************************************************************/
/*									*/
/*	packetinfo_new() - create and initialize a new packetinfo structure.	*/
/*									*/
/************************************************************************/

struct packetinfo *packetinfo_new();


/************************************************************************/
/*									*/
/*	packetinfo_free() - free the given packetinfo structure.		*/
/*									*/
/************************************************************************/

void packetinfo_free(struct packetinfo *packetinfo_p);


/************************************************************************/
/*									*/
/*	packetinfo_copyNoData() - return a copy of the given packetinfo	*/
/*		structure.  Do not copy the packetdata.			*/
/*									*/
/************************************************************************/

struct packetinfo *packetinfo_copyNoData(struct packetinfo *pinfo);


/************************************************************************/
/*									*/
/*	packetinfo_copyWithData() - return a copy of the given		*/
/*		packetinfo.  Also copy the packetdata.			*/
/*									*/
/************************************************************************/

struct packetinfo *packetinfo_copyWithData(struct packetinfo *pinfo);


extern struct ip *packetinfo_get_iphdr(struct packetinfo *pinfo);
// return deducehdr in the pinfo->packetdata.
extern struct deducehdr *packetinfo_get_deducehdrFromPacket(struct packetinfo *pinfo);
extern struct deducehdr *packetinfo_get_deducehdrFromExternal(struct packetinfo *pinfo);
extern void *packetinfo_get_remainder(struct packetinfo *pinfo);
extern void packetinfo_remove_deducehdr(zlog_category_t* zc, struct packetinfo *pinfo);
extern void packetinfo_rebuild(struct packetinfo *pinfo);
extern struct packetinfo *packetinfo_insert_deducehdr(struct packetinfo *pinfo);


/************************************************************************/
/*									*/
/*	packetinfo_addAParam() - add to Actuator Parameters in         */
/*		packetinfo structure.					*/
/*									*/
/************************************************************************/

void packetinfo_addAParam(struct packetinfo *pinfo, void *data, size_t len);


/************************************************************************/
/*									*/
/*	packetinfo_getAParam() - get Actuator Parameters from		*/
/*		packetinfo structure.					*/
/*									*/
/************************************************************************/

void packetinfo_getAParam(struct packetinfo *pinfo, void *data, size_t len);


/************************************************************************/
/*									*/
/*	packetinfo_print() - print out a summary of the contents of	*/
/*		the given packetinfo structure.				*/
/*									*/
/************************************************************************/

void packetinfo_print(FILE *ofp, struct packetinfo *pinfo);

/************************************************************************/
/*									*/
/*	packetinfo_log() - log a summary of the contents of the given	*/
/*		packetinfo structure, at the given category and log     */
/*              level 				                        */
/*									*/
/************************************************************************/

void packetinfo_log(zlog_category_t* zc, zlog_level zl, struct packetinfo *pinfo);

/************************************************************************/
/*									*/
/*	packetinfo_logOneLine() - log a summary of the contents of the  */
/*              packet info structure as a single line message with key */
/*              value pairs for each field, at the given category and   */
/*              log level.                                              */
/*									*/
/************************************************************************/

void packetinfo_logOneLine(zlog_category_t* zc, zlog_level zl, struct packetinfo *pinfo);

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
			 size_t* outlen );
#endif
