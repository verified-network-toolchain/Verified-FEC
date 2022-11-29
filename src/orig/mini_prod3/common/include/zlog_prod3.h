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
 */  /* -----------------------------------------------------------------------
 * This file contains additional zlog macros for dcps. Specifically, we
 * define two additional log levels:  DEBUG_LO and TRACE  which are used
 * for finer grained debuggging (i.e. more output than DEBUG)
 * -----------------------------------------------------------------------
 * We also provide the API for getting and setting the log style, which
 * covers multi-line vs. single-line output for packets and messages.
 * -----------------------------------------------------------------------
 */
#ifndef ZLOG_DCPS
#define ZLOG_DCPS

#include <zlog.h>

/* -----------------------------------------------------------------------
 * TERRIBLE HACK !!  Fix zlog source to expose the zlog_category_s 
 * structure, so we can query the level of a given category. 
 * -----------------------------------------------------------------------
 */
#define DCPS_ZLOG_MAXLEN_PATH 1024
typedef struct dcps_zlog_category_s {
	char name[DCPS_ZLOG_MAXLEN_PATH + 1];
	size_t name_len;
	unsigned char level_bitmap[32];
	unsigned char level_bitmap_backup[32];
	void *fit_rules;
	void *fit_rules_backup;
} dcps_zlog_category_t;

enum {
	ZLOG_LEVEL_TMI = 5,     // must equals conf file
	ZLOG_LEVEL_TRACE = 10,     // must equals conf file
	ZLOG_LEVEL_DEBLO = 15,   // must equals conf file
};

// assume we build in dcps/build and file names are "../xxx/yyy.c",
// so strip off first 3 bytes.
#define zlog_gen(cat, level, format, args...) \
  	zlog(cat, __FILE__+3, sizeof(__FILE__)-(1+3), __func__, sizeof(__func__)-1, __LINE__, \
	level, format, ##args)

#undef zlog_fatal
#undef zlog_error
#undef zlog_warn
#undef zlog_notice
#undef zlog_info
#undef zlog_debug

#define zlog_fatal(cat, format, args...) zlog_gen(cat, ZLOG_LEVEL_FATAL, format, ##args)
#define zlog_error(cat, format, args...) zlog_gen(cat, ZLOG_LEVEL_ERROR, format, ##args)
#define zlog_warn(cat, format, args...) zlog_gen(cat, ZLOG_LEVEL_WARN, format, ##args)
#define zlog_notice(cat, format, args...) zlog_gen(cat, ZLOG_LEVEL_NOTICE, format, ##args)
#define zlog_info(cat, format, args...) zlog_gen(cat, ZLOG_LEVEL_INFO, format, ##args)
#define zlog_debug(cat, format, args...) zlog_gen(cat, ZLOG_LEVEL_DEBUG, format, ##args)
#define zlog_debuglo(cat, format, args...) zlog_gen(cat, ZLOG_LEVEL_DEBLO, format, ##args)
#define zlog_trace(cat, format, args...) zlog_gen(cat, ZLOG_LEVEL_TRACE, format, ##args)
#define zlog_tmi(cat, format, args...) zlog_gen(cat, ZLOG_LEVEL_TMI, format, ##args)

#define hex_dump(cat, level, data, data_len, format, args...) do {    \
    if(isUsefulLevel(cat, level))                                     \
    {                                                                 \
	char *buf = privateHexDump(data, data_len, format, ##args);   \
	zlog_gen(cat, level, "%s", buf);                              \
	free(buf);                                                    \
    }                                                                 \
} while (0)


#define DCPS_LOGSTYLE_PRETTY 0
#define DCPS_LOGSTYLE_GREP 1

extern char *privateHexDump(const unsigned char *p, const unsigned int length, const char *format, ...);

int  isUsefulLevel( zlog_category_t* zc, zlog_level zl ) ;

unsigned int getDcpsLogstyle() ;
void setDcpsLogstyle( unsigned int ls ) ;

unsigned int getDcpsLoguknown() ;
void setDcpsLogunknown( unsigned int lu ) ;

#endif

/* ---------------
 * End - of - file
 * ---------------
 */
