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

#ifndef _UTIL_H_
#define _UTIL_H_

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
/*	util_getCurrentTime() - return the current time as seconds	*/
/*		since 1/1/1970 and fractional seconds with microsecond	*/
/*		resolution.						*/
/*									*/
/************************************************************************/

double util_getCurrentTime();


/************************************************************************/
/*									*/
/*	util_getCurrentTimeval() - returns current time as timeval	*/
/*		structure.						*/
/*									*/
/************************************************************************/

struct timeval util_getCurrentTimeval();


/************************************************************************/
/*									*/
/*	util_dottedDecimalToNetwork() - convert dotted decimal IP	*/
/*		address string into network format address.		*/
/*									*/
/************************************************************************/

u_int32_t util_dottedDecimalToNetwork(char *addrString);


/************************************************************************/
/*									*/
/*	util_networkToDottedDecimal() - converted network format IP	*/
/*		address to dotted decimal IP address string.		*/
/*									*/
/************************************************************************/

char *util_networkToDottedDecimal(u_int32_t address);


/************************************************************************/
/*									*/
/*	util_getIfName() - return the interface name associated		*/
/*		 with the given interface IP address (network format).	*/
/*									*/
/************************************************************************/

char *util_getIfName(u_int32_t address);


/************************************************************************/
/*									*/
/*	util_getIfMTU() - return the configured MTU for the specified	*/
/*		interface.						*/
/*									*/
/************************************************************************/

int util_getIfMTU(const char *device);


// define units for ease of use
#define MSECS_PER_SEC (1000)
#define USECS_PER_SEC (1000000)
#define NSECS_PER_SEC (1000000000)

// init timespec given int millisecs
static inline void timeInit(struct timespec *t, int32_t ms)
{
    t->tv_sec = ms / MSECS_PER_SEC;
    t->tv_nsec = (ms % MSECS_PER_SEC) * (NSECS_PER_SEC / MSECS_PER_SEC);
}

// init timespec given int millisecs
static inline void timeInitUsecs(struct timespec *t, int32_t us)
{
    t->tv_sec = us / USECS_PER_SEC;
    t->tv_nsec = (us % USECS_PER_SEC) * (NSECS_PER_SEC / USECS_PER_SEC);
}

// compare two times
static inline int timeCmp(struct timespec *lhs, struct timespec *rhs)
{
    if (lhs->tv_sec > rhs->tv_sec)
        return 1;
    if (lhs->tv_sec < rhs->tv_sec)
        return -1;

    // seconds compare equal

    if (lhs->tv_nsec > rhs->tv_nsec)
        return 1;
    if (lhs->tv_nsec < rhs->tv_nsec)
        return -1;

    // nanoseconds compare equal
    return 0;
}

// add two timespec's together.
// pass result so no local storage.
// return result so we can chain routines together
static inline struct timespec *timeAdd(struct timespec *result, struct timespec *a, struct timespec *b)
{
    result->tv_sec = a->tv_sec + b->tv_sec;
    result->tv_nsec = a->tv_nsec + b->tv_nsec;
    while (result->tv_nsec >= NSECS_PER_SEC)
    {
        result->tv_nsec -= NSECS_PER_SEC;
        result->tv_sec += 1;
    }

    return result;
}

static inline struct timespec *timeSub(struct timespec *result, struct timespec *a, struct timespec *b)
{
    result->tv_sec = a->tv_sec - b->tv_sec;
    result->tv_nsec = a->tv_nsec - b->tv_nsec;
    while (result->tv_nsec < 0)
    {
        result->tv_nsec += NSECS_PER_SEC;
        result->tv_sec -= 1;
    }

    return result;
}

extern pid_t gettid(void);

#endif
