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

#include "util.h"

extern zlog_category_t* zc_main;


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


/************************************************************************/
/*									*/
/*	util_getCurrentTime() - return the current time as seconds	*/
/*		since 1/1/1970 and fractional seconds with microsecond	*/
/*		resolution.						*/
/*									*/
/************************************************************************/

double util_getCurrentTime()
{
    struct timeval tv;
    double dtime;

    if (gettimeofday(&tv, NULL)) {
	perror("gettimeofday");
    }

    dtime = ((double) tv.tv_sec) + (((double) tv.tv_usec) / 1000000.0);
    
    return dtime;
}


/************************************************************************/
/*									*/
/*	util_getCurrentTimeval() - returns current time as timeval	*/
/*		structure.						*/
/*									*/
/************************************************************************/

struct timeval util_getCurrentTimeval()
{
    struct timeval tv;

    if (gettimeofday(&tv, NULL)) {
	perror("gettimeofday");
    }

    return tv;
}


#define MAX_BYTES_TOTAL 1500
#define MAX_BYTES_PER_LINE 16

// There are three bytes of output for each byte of input: " %02x"
// So: MAX_BYTES_TOTAL*3
// There is a "HEX DUMP: %4u:" at the beginning of each line and new-line at end of each.
// Max number of lines is MAX_BYTES_TOTAL/MAX_BYTES_PER_LINE, rounded up.
// So: (MAX_BYTES_TOTAL+MAX_BYTES_PER_LINE-1)/MAX_BYTES_PER_LINE is number of lines
// So: ((MAX_BYTES_TOTAL+MAX_BYTES_PER_LINE-1)/MAX_BYTES_PER_LINE) * 16
// There is a "HEX DUMP: BEGIN (%s)\n" at the beginning and "... END ..." at end.
// Allow about 100 bytes for user's comment about the dump.
// So: 128*2
// There is a preamble to all of this to print out the pointer and length.
// So: 64
#define BUF_LEN   MAX_BYTES_TOTAL*3 + ((MAX_BYTES_TOTAL+MAX_BYTES_PER_LINE-1)/MAX_BYTES_PER_LINE)*16 + 128*2 + 64

/* TODO: Should use snprintf into hbuf to ensure no buffer overflow.	*/
/* (bss 4/25/2017)							*/
/* void hex_dump(zlog_category_t* zc, zlog_level zl, */
/* 		 unsigned char *p, unsigned int length, char *format, ...) */
/* { */
/*     va_list aptr; */
/*     char hbuf[BUF_LEN], *hp = hbuf; */
/*     char cbuf[100]; */
/*     unsigned int i; */

/*     if( ! isUsefulLevel(zc,zl)) */
/*       return ; */

/*     va_start(aptr, format); */
/*     vsnprintf(cbuf, sizeof(cbuf), format, aptr); */
/*     va_end(aptr); */

/*     if (length > 1500) */
/*     { */
/* 	sprintf(hp, "hex_dump(%p, %d) (truncated from %d)\n", p, MAX_BYTES_TOTAL, length); */
/* 	length = MAX_BYTES_TOTAL; */
/*     } */
/*     else */
/* 	sprintf(hp, "hex_dump(%p, %d)\n", p, length); */
/*     hp += strlen(hp); */

/*     sprintf(hp, "HEX DUMP: BEGIN (%s)\n", cbuf); */
/*     hp += strlen(hp); */

/*     i = 0; */
/*     while (i < length) */
/*     { */
/* 	unsigned int j; */

/* 	sprintf(hp, "HEX DUMP: %4u:", i); */
/* 	hp += strlen(hp); */

/* 	for (j = 0; j < MAX_BYTES_PER_LINE && i < length; j++) */
/* 	{ */
/* 	    sprintf(hp, " %02x", p[i++]); */
/* 	    hp += 3; */
/* 	} */

/* 	sprintf(hp, "\n"); */
/* 	hp += 1; */
/*     } */

/*     sprintf(hp, "HEX DUMP:   END (%s)", cbuf); */
/*     zlog_gen(zc, zl, "%s", hbuf); */
/* } */

/************************************************************************/
/*									*/
/*	util_dottedDecimalToNetwork() - convert dotted decimal IP	*/
/*		address string into network format address.		*/
/*									*/
/************************************************************************/

u_int32_t util_dottedDecimalToNetwork(char *addrString)
{
    int rc;			/* return code from function call.	*/
    u_int32_t address;		/* network format IPv4 address.		*/

    rc = inet_pton(AF_INET, addrString, (unsigned char *) &address);
    if (rc <= 0) {
	perror("inet_pton");
	return 0;
    }
    else {
	return address;
    }
}


/************************************************************************/
/*									*/
/*	util_networkToDottedDecimal() - converted network format IP	*/
/*		address to dotted decimal IP address string.		*/
/*									*/
/************************************************************************/

char *util_networkToDottedDecimal(u_int32_t address)
{
    struct in_addr addr;

    addr.s_addr = address;

    return inet_ntoa(addr);
}


/************************************************************************/
/*									*/
/*	util_getIfName() - return the interface name associated		*/
/*		 with the given interface IP address (network format).	*/
/*									*/
/************************************************************************/

char *util_getIfName(u_int32_t address)
{
    struct ifaddrs *ifap;	/* list of interfaces.			*/
    struct ifaddrs *ifa;	/* current interface in list.		*/
    u_int32_t addr;		/* address for current interface.	*/

    if (getifaddrs(&ifap) < 0) {
	zlog_error(zc_main, "Can't get interface information.");
	return 0;
    }

    /* loop through interfaces looking for a matching address.		*/
    for (ifa = ifap; ifa != 0; ifa = ifa->ifa_next) {
	/* just handling ipv4 addresses.				*/
	if (ifa->ifa_addr->sa_family != AF_INET) {
	    continue;
	}
	struct sockaddr_in *sa = (struct sockaddr_in *) ifa->ifa_addr;
	addr = sa->sin_addr.s_addr;
	if (addr == address) {
	    return ifa->ifa_name;
	}
    }

    return 0;
}


/************************************************************************/
/*									*/
/*	util_getIfMTU() - return the configured MTU for the specified	*/
/*		interface.						*/
/*									*/
/************************************************************************/

int util_getIfMTU(const char *device)
{
    int fd;
    struct ifreq ifr;

    if (!device) {
	return 65535;
    }

    /* open a socket.  Any type will do.				*/
    fd = socket(AF_INET, SOCK_DGRAM, 0);

    memset(&ifr, 0, sizeof(ifr));
    strncpy(ifr.ifr_name, device, sizeof(ifr.ifr_name));

    if (ioctl(fd, SIOCGIFMTU, &ifr) == -1) {
	zlog_error(zc_main, "ioctl for socket %d, interface %s returned error %d: %s.",
		   fd, device,
		   errno, strerror(errno));
	close(fd);
	return 0;
    }

    close(fd);
    return ifr.ifr_mtu;
}




pid_t gettid(void)
{
    return syscall(SYS_gettid);
}
