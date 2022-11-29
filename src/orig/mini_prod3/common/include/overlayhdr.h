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

#ifndef DEDUCEHDR_H
#define DEDUCEHDR_H

#include "common.h"
// #include "util.h"

/**
 * Packet in the black:
 * Normal packet wth two wrinkles:
 * a shim of N bytes after the transport (e.g., TCP,UDP) header and before app data.
 * an ip option to give shim size
 **/



// use these ports to signify presence of deduce header
#define DEDUCE_SPORT 0xAABB
#define DEDUCE_DPORT 0xCCDD

struct deducehdr
{
    // number of params in bytes
    u_int8_t paramSize;
    // original IP protocol
    u_int8_t origIpProtocol;

  // reserved
  u_int16_t reserved;

    // original src and dst ip
    u_int32_t origSrcIpAddr, origDstIpAddr;

};


/************************************************************************/
/*									*/
/*	deducehdr_log() - log the contents of the given deducehdr	*/
/*		structure, to the given log category and level          */
/*									*/
/************************************************************************/

extern void deducehdr_log(  zlog_category_t* zc, 
		     zlog_level zl,
		     struct deducehdr *dhdr) ;


/************************************************************************/
/*									*/
/*	deducehdr_logAll() - Log the deduce header and the actuator	*/
/*		options.  Takes the ip header to get the total length	*/
/*		of header plus options.					*/
/*									*/
/************************************************************************/

extern void deducehdr_logAll(zlog_category_t *zc,
		      zlog_level zl,
		      struct deducehdr *dhdr,
		      unsigned char *params, u_int32_t size);



#endif
