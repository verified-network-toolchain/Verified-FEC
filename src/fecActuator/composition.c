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
 
#include "composition.h"

#define MAXCOMPOSITIONS		65536	/* 16 bits.			*/

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

/* composition array indexed by composition ID.				*/
static struct composition *compositions[MAXCOMPOSITIONS];


/************************************************************************/
/*									*/
/*	composition_new() - create and initialize a new composition     */
/*                          structure.	                                */
/*									*/
/************************************************************************/

struct composition *composition_new()
{
  struct composition *composition_p;

  composition_p = (struct composition *) calloc(1, sizeof(struct composition));
  return composition_p;
}


/************************************************************************/
/*									*/
/*	composition_free() - free the given composition structure and	*/
/*		make its ID available.					*/
/*									*/
/************************************************************************/

void composition_free(struct composition *composition_p)
{
  assert((composition_p->compId >= 0) && (composition_p->compId < MAXCOMPOSITIONS));

  compositions[composition_p->compId] = (struct composition*) NULL;
  free(composition_p);

  return;
}


/************************************************************************/
/*									*/
/*	composition_add() - add given composition structure to the	*/
/*		composition list.					*/
/*									*/
/************************************************************************/

void composition_add(struct composition *composition_p)
{
  static int firsttime = 1;	/* flag for first call so can		*/
				/* initialize.				*/
  int i;			/* loop counter.			*/
  int compId;			/* composition ID - index into table.	*/

  if (firsttime) 
    {
      firsttime = 0;
      for (i = 0; i < MAXCOMPOSITIONS; i++) 
	{
	  compositions[i] = (struct composition*) NULL;
	}
    }

  compId = composition_p->compId;
  assert((compId >= 0) && (compId < MAXCOMPOSITIONS));

  if (compositions[compId] != (struct composition*) NULL) 
    {
      fprintf(stderr, "Warning: overwriting composition %d.\n", compId);
      composition_free(compositions[compId]);
    }

  compositions[compId] = composition_p;
	
  return;
}


/************************************************************************/
/*									*/
/*	composition_getComposition() - return the composition structure	*/
/*		for the given composition ID.				*/
/*									*/
/************************************************************************/

struct composition *composition_getComposition(int id)
{
  if (id < 0 || id > 65535) 
    {
      return 0;
    }

  return compositions[id];
}


/************************************************************************/
/*									*/
/*	composition_log() - log the contents of the given	        */
/*		composition structure, with the given category and log  */
/*              level.                                                  */
/*									*/
/************************************************************************/

void composition_log(zlog_category_t *zc, zlog_level zl, struct composition *c)
{

  if (c == (struct composition*) NULL) 
    {
      zlog_gen(zc, zl, "WARNING: Composition is null.  Can't print contents.");
      return;
    }

  zlog_gen(zc, zl, "Composition %d", c->compId);
  zlog_gen(zc, zl, "\t\t\tfec_k = %d, fec_h = %d, fec_n = %d",
	   c->fec_k, c->fec_h, c->fec_n);
  return;
}


/************************************************************************/
/*									*/
/*	composition_logOneLine() - log the contents of the given	*/
/*		composition structure on a single line.			*/
/*									*/
/************************************************************************/

void composition_logOneLine(zlog_category_t *zc, zlog_level zl, struct composition *c)
{
  if (c == (struct composition*) NULL) 
    {
      zlog_gen(zc, zl, "WARNING: Composition is null.  Can't print contents.");
      return;
    }

  zlog_gen(zc, zl,
	   "Composition %d: fec_k %d fec_h %d fec_n %d", c->compId, c->fec_k, c->fec_h, c->fec_n);

  return;
}


/************************************************************************/
/*									*/
/*	composition_logAll() - output the definitions of all defined	*/
/*		compositions to the log file.				*/
/*									*/
/************************************************************************/

void composition_logAll(zlog_category_t *zc, zlog_level zl)
{
  int i;			/* loop counter.			*/
  int count = 0;		/* number of defined compostions.	*/

  zlog_gen(zc, zl, "All defined compositions:");

  for (i = 0; i < MAXCOMPOSITIONS; i++) 
    {
      if (compositions[i] != (struct composition*) NULL) 
	{
	  count++;
	  composition_log(zc, zl, compositions[i]);
	}
    }

  zlog_gen(zc, zl, "End of composition array. %d defined compositions.", count);
    
  return;
}
