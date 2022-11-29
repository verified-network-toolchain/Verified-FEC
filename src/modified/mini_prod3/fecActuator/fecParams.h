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
 
#ifndef _FECPARAMS_H_
#define _FECPARAMS_H_

/************************************************************************/
/*									*/
/*				fecParams				*/
/*									*/
/* Author:	 (bss@nash.appcomsci.com)		*/
/* File:	fecParams.h						*/
/* Date:	Wed Nov  4 17:19:16 EST 2015				*/
/*									*/
/* Description:								*/
/*	Definitions and function prototypes for fecParams.		*/
/*									*/
/* Copyright (c) 2015 .			*/
/* All rights reserved.							*/
/*									*/
/************************************************************************/


/************************************************************************/
/*									*/
/*	data structures.						*/
/*									*/
/************************************************************************/

struct fecParams {
  u_int8_t fec_k;
  u_int8_t fec_h;
  u_int8_t fec_seq;
  u_int8_t reserved;
  u_int32_t block_seq;
};


/************************************************************************/
/*									*/
/*	global variables.						*/
/*									*/
/************************************************************************/

#endif
