#ifndef _REDFECACTUATOR_H_
#define _REDFECACTUATOR_H_

/*
 * redFecActuator.h
 * Forward Erasure Correction actuator - red side
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

#include "pipework.h"

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
/*	redFecActuator_init() - initialize.				*/
/*									*/
/************************************************************************/

void redFecActuator_init();


/************************************************************************/
/*									*/
/*	redFecActuator() - applies packet FEC to a packet in the red	*/
/*		pipeline (i.e., originating from the red network).	*/
/*		Takes a packetinfo structure describing a packet,	*/
/*		saves copies of the structures until an FEC block	*/
/*		can be created, returning the original structures,	*/
/*		and with the last source packet also appending the	*/
/*		parity packets and freeing the saved copies.		*/
/*									*/
/************************************************************************/

DECLARE(redFecActuator);


#endif
