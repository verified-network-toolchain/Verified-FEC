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
 
#ifndef PIPEWORK_H
#define PIPEWORK_H

#include "common.h"

#include "packetinfo.h"


// allow for a state machine to change how the actuators find next state.
// the actuator function returns next state, which typically would be CONTINUE.
#define STATE_PENDING		-1
#define STATE_CONTINUE  	0
#define STATE_NOSEND		1
#define STATE_SEND_BLACK_IFACE	2

// Make sure all actuator declarations follow same template.
// This allows for later turning these into a list of function calls.
#define DECLARE(func) u_int32_t func(struct packetinfo *pinfo __attribute__((unused)), struct packetinfo **pbeg __attribute__((unused)), struct packetinfo **pend __attribute__((unused)))
typedef DECLARE(actuator_t);

#endif
