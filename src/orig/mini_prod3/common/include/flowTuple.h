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

#ifndef _FLOWTUPLE_H_
#define _FLOWTUPLE_H_

#include "common.h"


/************************************************************************/
/*									*/
/*	data structures.						*/
/*									*/
/************************************************************************/

struct flowTuple {
    u_int8_t ipversion;		/* IP version number (should be 4).	*/

    u_int8_t protocol;		/* transport protocol in host format.	*/

    u_int32_t srcaddr;		/* source address in host format.	*/
    u_int32_t dstaddr;		/* destination address in host format.	*/
    u_int16_t srcport;		/* source port in host format.		*/
    u_int16_t dstport;		/* destination port in host format.	*/
};


/************************************************************************/
/*									*/
/*	global variables.						*/
/*									*/
/************************************************************************/


/************************************************************************/
/*									*/
/*	flowTuple_new() - create and initialize a new flowTuple		*/
/*		 structure.						*/
/*									*/
/************************************************************************/

struct flowTuple *flowTuple_new();


/************************************************************************/
/*                                                                      */
/*     flowTuple_copy() - create and initialize a new flowTuple         */
/*              structure from the given flowTuple structure            */
/*                                                                      */
/************************************************************************/

struct flowTuple *flowTuple_copy(struct flowTuple* flowTuple_c);


/************************************************************************/
/*									*/
/*	flowTuple_free() - free the given flowTuple structure.		*/
/*									*/
/************************************************************************/

void flowTuple_free(struct flowTuple *flowTuple_p);


/************************************************************************/
/*									*/
/*	flowTuple_print() - print out the contents of a flowTuple	*/
/*		structure.						*/
/*									*/
/************************************************************************/

void flowTuple_print(FILE *ofp, struct flowTuple *ft);


/************************************************************************/
/*									*/
/*	flowTuple_log() - log the contents of a flowTuple structure	*/
/*		to the given log category and level			*/
/*									*/
/************************************************************************/

void flowTuple_log(  zlog_category_t* zc, 
		     zlog_level zl,
		     struct flowTuple* ft ) ;


/************************************************************************/
/*									*/
/*	flowTuple_sprint() - print out the contents of a flowTuple	*/
/*		structure into a string.				*/
/*									*/
/************************************************************************/

char *flowTuple_sprint(char *string, size_t length, struct flowTuple *ft) ;


/************************************************************************/
/*                                                                      */
/*     flowTuple_log2str() - log the contents of a flowTuple            */
/*             structure into a buffer, and post the number of bytes    */
/*             written.                                                 */
/*                                                                      */
/************************************************************************/

void flowTuple_log2str( char* logbuf, size_t logbuflen, struct flowTuple *ft, 
			size_t* outlen) ;


/************************************************************************/
/*									*/
/*	flowTuple_compare() - returns 0 if tuples are identical, -1	*/
/*		if f1 < f2, 1 if f1 > f2.				*/
/*									*/
/************************************************************************/

int flowTuple_compare(struct flowTuple *f1, struct flowTuple *f2);

#endif
