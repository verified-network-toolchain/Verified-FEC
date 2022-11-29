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
 
#include "flow.h"
#include "flowHash.h"
#include "fistq.h"
#include "util.h"


/************************************************************************/
/*									*/
/*	global variables.						*/
/*									*/
/************************************************************************/
extern zlog_category_t* zc_main ;


/************************************************************************/
/*									*/
/*	module-wide variables - global variables used only in the	*/
/*		current file.						*/
/*									*/
/************************************************************************/



/* flow table                                                           */
/*                                                                      */
/* currently, we only add flows to the beginning of the list for each   */
/* bucket so it is OK to only lock access to the pointer to the first   */
/* first node in the list (only one that can change)                    */
/* otherwise functions can walk thru the list without a lock            */
/*                                                                      */
/* TO DO: See if flow_remove() is called from anywhere, because it      */
/*        will break if actually called                                 */
struct flowtable_bucket_t flowtable[HASHSIZE];



/************************************************************************/
/*									*/
/*	flow_new() - create and initialize a new flow structure.	*/
/*									*/
/************************************************************************/

struct flow *flow_new(void)
{
    struct flow *f;

    f = (struct flow *) calloc(1, sizeof(struct flow));
   
    return f;
}


/************************************************************************/
/*									*/
/*	flow_free() - free the given flow structure.			*/
/*									*/
/************************************************************************/

void flow_free(struct flow *f)
{

  /* red side FEC parameters.						*/
  if (f->packetptrs != 0) 
    {
      /* ToDo: may also need to free the pointers in the array.	*/
      free(f->packetptrs);
    }
  if (f->packetsizes != 0) 
    {
      free(f->packetsizes);
    }
  if (f->pstat != 0) 
    {
      free(f->pstat);
    }

  /* black side FEC parameters.					*/
  if (f->bpacketptrs != 0) 
    {
      /* ToDo: may also need to free the pointers in the array.	*/
      free(f->bpacketptrs);
    }
  if (f->bpacketsizes != 0) 
    {
      free(f->bpacketsizes);
    }
  if (f->bpstat != 0) 
    {
      free(f->bpstat);
    }

  free(f);

  return;
}


/************************************************************************/
/*									*/
/*	flow_add() - add given flow structure to the flow list.		*/
/*									*/
/************************************************************************/

void flow_add(struct flow *f)
{
  struct flow *curr;		/* current flow in list.		*/

  f->flowhash
    = flowHash_hash(HASHSIZE,
		    f->flowtuple, sizeof(struct flowTuple));

  flowTuple_sprint( f->tuplestr_buff, sizeof(f->tuplestr_buff), f->flowtuple);

  zlog_info( zc_main, "%s(): Tuple %s hashes to %d.", 
	     __func__,f->tuplestr_buff, f->flowhash);

  /* lock the flow table.						*/
  pthread_mutex_lock(&flowtable[f->flowhash].lock);
  for (curr = flowtable[f->flowhash].flows; curr != 0; curr = curr->next) {
    if (flowTuple_compare(f->flowtuple, curr->flowtuple) == 0) {
	    zlog_notice(zc_main, "Adding existing flow %s to flow table: %s",
		       f->tuplestr_buff, curr->tuplestr_buff) ;
	    break;
	}
    }
    f->next = flowtable[f->flowhash].flows;
    flowtable[f->flowhash].flows = f;
    pthread_mutex_unlock(&flowtable[f->flowhash].lock);

    return;
}


/************************************************************************/
/*									*/
/*	flow_remove() - remove the given flow structure from the flow	*/
/*		list.  Does not free the flow structure.		*/
/*									*/
/************************************************************************/

void flow_remove(struct flow *f)
{
  struct flow *prevf;		/* previous flow in list.		*/
  struct flow *currf;		/* current flow in list.		*/

  if (f->flowhash == 0) {
    f->flowhash
      = flowHash_hash(HASHSIZE,
		      f->flowtuple, sizeof(struct flowTuple));
  }

  zlog_info( zc_main, "%s(): Tuple %s hashes to %d.", 
	     __func__, f->tuplestr_buff, f->flowhash);

  /* lock the flow table entry.					*/
  pthread_mutex_lock(&flowtable[f->flowhash].lock);

  /* remove the flow from the list of flows that match the hash.	*/
  prevf = 0;
  for (currf = flowtable[f->flowhash].flows; currf != 0; currf = currf->next) {
    if (f == currf) {
      if (prevf == 0) {
	flowtable[f->flowhash].flows = f->next;
      }
      else {
	prevf->next = f->next;
      }
      prevf = currf;
    }
  }
  
  /* unlock the flow table entry.					*/
  pthread_mutex_unlock(&flowtable[f->flowhash].lock);

  return;
}


/************************************************************************/
/*									*/
/*	flow_findByHash() - find the flow matching the given hash and	*/
/*		flow tuple.						*/
/*									*/
/*		Note: assume that flow table has already been		*/
/*		initialized.  Otherwise couldn't have a hash.		*/
/*									*/
/************************************************************************/

struct flow *flow_findByHash(struct flowTuple *tuple, u_int32_t hash)
{
  struct flow *f;		/* current flow.			*/

  pthread_mutex_lock(&flowtable[hash].lock);
  f = flowtable[hash].flows;
  pthread_mutex_unlock(&flowtable[hash].lock);

  for (; f != 0; f = f->next) {
    if (flowTuple_compare(tuple, f->flowtuple) == 0) {
      break;
    }
  }

  /* if no match, will be null.					*/
  return f;
}


/************************************************************************/
/*									*/
/*	flow_find() - find the flow matching the given flow tuple.	*/
/*									*/
/************************************************************************/

struct flow *flow_find(struct flowTuple *tuple)
{
  u_int32_t hash;
  struct flow *f;

  char outbuffer[1024];
  int outbufsize = 1024;

  hash = flowHash_hash(HASHSIZE, tuple, sizeof(struct flowTuple));

  if( isUsefulLevel(zc_main, ZLOG_LEVEL_DEBUG))
    {
      zlog_debug(zc_main, "%s(): Tuple %s hashes to %d.",
		 __func__, flowTuple_sprint(outbuffer, outbufsize, tuple),
		 hash);
    }

    /* lock the flow table.						*/
// #define LOCKTIME  
#ifdef LOCKTIME
    double t1 = util_getCurrentTime();
#endif
    pthread_mutex_lock(&flowtable[hash].lock);
#ifdef LOCKTIME
    double tdelta = util_getCurrentTime() - t1;
    zlog_fatal(zc_main, "lock time = %.06f", tdelta);
#endif
    f = flowtable[hash].flows;
    pthread_mutex_unlock(&flowtable[hash].lock);
    for (; f != 0; f = f->next) {
	if (flowTuple_compare(tuple, f->flowtuple) == 0) {
	    break;
	}
    }

    /* if no match, will be null.					*/
    return f;
}
