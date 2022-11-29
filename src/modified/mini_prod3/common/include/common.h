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

#ifndef _COMMON_H_
#define _COMMON_H_

/************************************************************************/
/*									*/
/*				common				        */
/*									*/
/* Author:	Bruce S. Siegell (bsiegell@appcomsci.com)		*/
/* File:	common.h						*/
/* Date:	Wed Jul 29 17:25:07 EDT 2015				*/
/*									*/
/* Description:								*/
/*	Definitions and function prototypes for common.	        	*/
/*									*/
/* Copyright (c) 2015 Applied Communication Sciences.			*/
/* All rights reserved.							*/
/*									*/
/************************************************************************/
#ifndef __USE_BSD
#define __USE_BSD
#endif

#include <sys/types.h>		/* .			                */
#include <stdio.h>		/* for FILE, perror(), etc.		*/
#include <stdlib.h>		/* for calloc(), etc.			*/
#include <assert.h>		/* for assert(), etc.			*/
#include <stdarg.h>
#include <string.h>             /* for memset, memcpy                   */
#include <strings.h>
#include <time.h>               /* for mutex and condition variables    */
#include <errno.h>		/* for errno, etc.			*/
#include <pthread.h>            /* for pthread_mutex_init(), etc.	*/
#include <sys/un.h>
#include <sys/stat.h>
#include <sys/time.h>		/* for gettimeofday(), etc.		*/
#include <sched.h>
#include <signal.h>

#define __FAVOR_BSD		/* for uh_* versions of attributes.	*/
#include <netinet/ip.h>		/* for struct iphdr, etc.		*/
#include <netinet/udp.h>
#include <netinet/tcp.h>
#include <netinet/in.h>		/* for struct sockaddr, etc.		*/

#include <sys/socket.h>
#include <arpa/inet.h>		/* for ntohl(), etc.			*/
#include <ifaddrs.h>		/* for getifaddrs(), etc.		*/
#include <sys/ioctl.h>		/* for ioctl(), etc.			*/
#include <net/if.h>		/* for struct ifreq, etc.		*/
#include <netdb.h>

#define _GNU_SOURCE
#include <unistd.h>
#include <sys/syscall.h>

#include "zlog_prod3.h"


#define BOOLEAN	int

#ifndef TRUE
#define TRUE	1
#endif

#ifndef FALSE
#define FALSE	0
#endif

#ifndef MAX_PACKET_SIZE
#define MAX_PACKET_SIZE 65536
#endif

#define MAX_IFACE_LEN 108
#define SUN_PATH_LEN 108

/* Macros */
#define IPF "%d.%d.%d.%d"
#define IP1(a)   ( (int) ( ( (a) >> 24 ) & 0xFF ) )
#define IP2(a)   ( (int) ( ( (a) >> 16 ) & 0xFF ) )
#define IP3(a)   ( (int) ( ( (a) >>  8 ) & 0xFF ) )
#define IP4(a)   ( (int) ( ( (a) >>  0 ) & 0xFF ) )
#define IP(a) IP1(a), IP2(a), IP3(a), IP4(a)
#define UNUSED(x) void(x)

#endif
