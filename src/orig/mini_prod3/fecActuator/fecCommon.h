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
 
#ifndef _FECCOMMON_H_
#define _FECCOMMON_H_

/************************************************************************/
/*									*/
/*				fecCommon				*/
/*									*/
/* Author:	 (bss@nash.appcomsci.com)		*/
/* File:	fecCommon.h						*/
/* Date:	Tue Nov 10 10:40:18 EST 2015				*/
/*									*/
/* Description:								*/
/*	Definitions and function prototypes for fecCommon.		*/
/*									*/
/* Copyright (c) 2015 .			*/
/* All rights reserved.							*/
/*									*/
/************************************************************************/

#include "common.h"

/************************************************************************/
/*									*/
/*	data structures.						*/
/*									*/
/************************************************************************/


/************************************************************************/
/*									*/
/*	global variables.						*/
/*									*/
/************************************************************************/


/************************************************************************/
/*									*/
/*	fecCommon_maskHeader() - mask the IP header bits for	*/
/*		FEC.							*/
/*									*/
/************************************************************************/

void fecCommon_maskHeader(struct ip *ipheader);


#endif
