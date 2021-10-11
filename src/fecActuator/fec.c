/*
 * FEC.C
 * Forward Erasure Correction encoder and decoder
 *
 * Copyright 2021 Peraton Labs Inc.
 *
 * Originally developed by A. McAuley, Peraton Labs Inc.
 * 
 * This software was developed in work supported by the following U.S.
 * Government contracts:
 *
 * W15P7T-05-C-R402
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
 * Revision history:
 *
 * Developed circa 1996 for DARPA (#DABT63-95-C) by 
 * A. McAuley, Bellcore (mcauley@bellcore.com)
 * 
 * Modifications:
 * 	9/1997   Vinh Lam (for NRL)   High speed version
 *	7/2005   Harshad Tanna	Integration with SAPIENT PCNM code
 *  2020     Josh Cohen (Princeton)  fec_gf_mult function instead of macro and remove undefined behavior
 */

#ifdef TRACE_FEC_MALLOCS
#define TRACEMALLOCS
#endif

#include <stdio.h>		/* for fprintf(), etc.			*/
#include <assert.h>

#include "fec.h"
//#include "fecHandler.h"
//#include "packetinfo.h"
//#include "stddefs.h"
//#include "saphdr.h"

int trace = 0;

// These typedefs, defines & local functions were moved from fec.h -- they do not need to be global

/***************************************************************************/
/* Options                                                                 */
/***************************************************************************/

//#define  FEC_MAC_LOOKUP            /* use gf lookup table in FEC_MAC */

/** debug options **/

#define  FEC_DBG_EVENTS	    /* enables funcs that print major events */
#define  FEC_DBG_TABLES           /* enables func that prints packets */

// FEC_DBG_EVENTS must be on for these options to work
#define  FEC_DBG_PRINT_WEIGHTS    /* print fec_weights */
//#define  FEC_DBG_PRINT_EVENTS	    /* print major events */
//#define  FEC_DBG_PRINT_TRANS      /* print dbg statements in matrix transform function */
#define  FEC_DEBUG_PRINT



/***************************************************************************/
/* Typedefs                                                                */
/***************************************************************************/
typedef unsigned char	fec_sym;		/* m bit symbol */
typedef fec_sym fec_pac[FEC_N-1];		/* packet structure */
typedef fec_sym (*fec_blk)[FEC_MAX_COLS];	/* packet structure */

/***************************************************************************/
/* Error codes                                                             */
/***************************************************************************/

#define FEC_ERR_INVALID_PARAMS        (-1)
#define FEC_ERR_ENC_MISSING_DATA      (-20)
#define FEC_ERR_MOD_NOT_FOUND         (4)
#define FEC_ERR_TRANS_FAILED          (82)
#define FEC_ERR_TRANS_SWAP_NOT_DONE   (83)

int fec_blk_encode(int k, int h, int c, unsigned char **pdata, int *plen, char *pstat);
int fec_blk_decode(int k, int c, unsigned char **pdata, int *plen, char *pstat);

void rse_init(void);
void fec_generate_weights(void);

int fec_matrix_transform(fec_sym *p, fec_sym i_max, fec_sym j_max);

//void fec_gf_mult(fec_sym multiplier, fec_sym multiplicand, fec_sym *product); JOSH - not used in original code
void fec_generate_math_tables(void);
int fec_find_mod(void);
#ifdef MAC_LOOKUP
void gen_gf_mult_table(fec_sym gf_table[FEC_N][FEC_N]);
#ifdef FEC_DBG_EVENTS
void print_gf_mult_table(fec_sym gf_table[FEC_N][FEC_N]);
#endif
#endif

#ifdef FEC_DBG_EVENTS
void fec_matrix_display(fec_sym *p, fec_sym i_max, fec_sym j_max);
void fec_display_tables(void);
#endif

#define IF_DEBUG_FEC  if (0)
//#define IF_DEBUG_FEC if (config.debug_fec)

/***************************************************************************/
/* Pre-computed GF Tables (Global variables ... ugly but easy)             */
/***************************************************************************/
fec_sym fec_2_power[FEC_N];	/* index->power table */
fec_sym fec_2_index[FEC_N];	/* power->index table */
fec_sym fec_invefec[FEC_N];	/* multiplicative inverse */
fec_sym fec_weights[FEC_MAX_H][FEC_N - 1];	/* FEC weight table */

#ifdef FEC_MAC_LOOKUP

/* putting lookup table on heap instead may speed up access */
fec_sym gf_mult_table[FEC_N][FEC_N];	/* Multiplication table */

#endif

/***************************************************************************/
/* GF MULTIPLY & ACCUMULATE (p = p + a.b) (heart of coder, so fast macro)  */
/***************************************************************************/

#ifdef FEC_MAC_LOOKUP		/* do 1 lookup in a size n.n table */

#define FEC_MAC(a,b,p)\
{\
  if (a && b) \
    p ^= (fec_sym)(*((fec_sym *)gf_mult_table + (a << FEC_M) + b));\
}

#else /* do 3 lookups into a size n table */

#define FEC_MAC(a,b,p) p = p ^fec_gf_mult(a,b);
// {\
//   p = p ^ fec_gf_mult(a, b)
//   if (a && b) \
//      {\
//      if ((fec_2_power[a]+fec_2_power[b]) > FEC_N-1) \
//         p ^= fec_2_index[((fec_2_power[a]+fec_2_power[b])-(FEC_N-1))];\
//      else \
//         p ^= fec_2_index[(fec_2_power[a]+fec_2_power[b])];\
//      }
//}

#endif

/* GF multiply only (no accumulate) */

//#define FEC_GF_MULT(a,b) ((a && b) ? (((fec_2_power[a]+fec_2_power[b]) > FEC_N-1) ? (fec_2_index[((fec_2_power[a]+fec_2_power[b])-(FEC_N-1))]) : (fec_2_index[(fec_2_power[a]+fec_2_power[b])])) : 0)

//JOSH - Made into function for ease of verification (does not make runtime worse at gcc O2 and O3 - inlined at O3)
fec_sym fec_gf_mult(fec_sym a, fec_sym b) {
  if (a && b) {
    if ((fec_2_power[a]+fec_2_power[b]) > FEC_N-1) {
      return (fec_2_index[((fec_2_power[a]+fec_2_power[b])-(FEC_N-1))]);
    }
    else {
      return ((fec_2_index[(fec_2_power[a]+fec_2_power[b])]));
    }
  }
  else {
    return 0;
  }
}


/***************************************************************************/
/* Encoding and Decoding                                                   */
/***************************************************************************/
/*
 * Check bounds are reasonable and pass to encode or decode
 */
int
rse_code (int k, int h, int c, unsigned char **pdata, int *plen, char *pstat)
{
  IF_DEBUG_FEC fprintf (stderr, "FEC: rse_code: k=%d, h=%d, c=%d\n", k, h, c);
  if ((k >= FEC_N - FEC_MAX_H) || (h > FEC_MAX_H) || (c > FEC_MAX_COLS) ||
      (k < 1) || (h < 0) || (c < 1))
    {
      fprintf (stderr, "FEC: FEC code parameters out of bound: ");
      fprintf (stderr, "FEC: k=%d (0 < k < %d (FEC_N-FEC_MAX_H)) ", k,
	       FEC_N - FEC_MAX_H);
      fprintf (stderr, "FEC: h=%d (0 <= h < %d (FEC_MAX_H))\n", h, FEC_MAX_H);
      fprintf (stderr, "FEC: c=%d (0 < c < %d (FEC_MAX_COLS)) ", c,
	       FEC_MAX_COLS);
      /* need to know if this case occurs.  (bss 4/26/2017)		*/
      assert(0);
      return (FEC_ERR_INVALID_PARAMS);
    }

  if (h == 0)
    return (fec_blk_decode (k, c, pdata, plen, pstat));
  else
    return (fec_blk_encode (k, h, c, pdata, plen, pstat));
}

/*
 * Encode 
 */
int
fec_blk_encode (int k, int h, int c, unsigned char **pdata, int *plen,
		char *pstat)
{

  int j, n;
  fec_sym data, i, y, z = -1;
  fec_sym *p;
  unsigned char **pparity = pdata + k;

  for (i = 0; i < k; i++)
    {				/* add data lost/found list */
      if (pstat[i] == FEC_FLAG_WANTED)
	{
	  IF_DEBUG_FEC fprintf (stderr,
		   "FEC: Before encoding, recover missing data packets\n");
	  return (FEC_ERR_ENC_MISSING_DATA);
	}
    }
  IF_DEBUG_FEC fprintf (stderr, "FEC: >>>fec_blk_encode\n");
  /*
   * O(h.k.c) Matric multiplication  f[h][c]= w'[h][k] * d[k][c]
   * (where w' are h rows of w selected by variable z)
   */
  for (i = 0; i < h; i++)
    {

      while (!pparity[++z]);	/* allow append extra fec */
      IF_DEBUG_FEC fprintf (stderr, "FEC: z=%d\n", z);

      assert (z < FEC_MAX_H);	/* weak bound (h valid parity pointers still expected) */

      for (j = 0; j < c; j++)
	{

	  y = 0;
	  p = fec_weights[z];	/* start of w row */

	  for (n = 0; n < k; n++)
	    {

	      /* handle variable length packets */
	      if (plen[n] > j)
		{

		  /* data used so that the fec macro doesn't redundantly compute */
		  data = *((fec_sym *) (pdata[n] + j));

		  FEC_MAC (*p, data, y);
		}

	      p++;
	    }

	  *(pparity[z] + j) = y;	/* write fec into buffer */
	}
    }

  IF_DEBUG_FEC fprintf (stderr, "FEC: <<<fec_blk_encode\n");
  return (0);

}

/*
 * Decode
 */
int
fec_blk_decode (int k, int c, unsigned char **pdata, int *plen, char *pstat)
{

  fec_sym i, q, x, y, z;
  fec_sym weight, data;
  fec_sym v[FEC_MAX_H][FEC_MAX_H * 2];
  fec_sym s[FEC_MAX_H][FEC_MAX_COLS];
  fec_sym *p, *r, *t, *u;
  fec_sym *n, *m;
  int j, data_lost_row, err = 0;
  //  fec_sym h_max;
  fec_sym xh = 0, xk = 0, xr = 0;
  fec_sym lost[FEC_N - FEC_MAX_H], found[FEC_N - FEC_MAX_H], row[FEC_MAX_H];
  unsigned char **pparity = pdata + k;


  IF_DEBUG_FEC fprintf (stderr, "FEC: >>>fec_blk_decode: k=%d, c=%d\n", k, c);
  IF_DEBUG_FEC fflush (stderr);
  for (i = 0; i < k; i++)
    {				/* add data lost/found list */
      if (pstat[i] == FEC_FLAG_WANTED)
	lost[xh++] = i;
      else
	found[xk++] = i;
    }

  if (!xh)
    return (0);			/* know all data */

  q = FEC_N - 2;

  /* find xh parity packets */
  for (i = 0; xr < xh; i++)
    {
      if (pparity[i])
	{			/* skip WANTED or IGNORE packets */
	  found[xk++] = q;
	  row[xr++] = i;
	}

      q--;

      /* xh valid pointers should exist, thus we should never check more than FEC_MAX_H pointers. */
      assert (i < FEC_MAX_H);

    }

  //  h_max = i;

  //  if (trace > 1 && config.debug_fec)
  if (trace > 1)
    {
      IF_DEBUG_FEC fprintf (stderr, "FEC: xh=");
      for (i = 0; i < xh; i++)
	{
	  IF_DEBUG_FEC fprintf (stderr, " %d ", lost[i]);
	}
      IF_DEBUG_FEC fprintf (stderr, "\nFEC: xk=");
      for (i = 0; i < xk; i++)
	{
	  IF_DEBUG_FEC fprintf (stderr, "%d ", found[i]);
	}
      IF_DEBUG_FEC fprintf (stderr, "\nFEC: r=");
      for (i = 0; i < xr; i++)
	{
	  IF_DEBUG_FEC fprintf (stderr, "%d ", row[i]);
	}
      IF_DEBUG_FEC fprintf (stderr, "\n");
      IF_DEBUG_FEC fflush (stderr);
    }

  /*
   * 1. Decode Matrix (Time = O(h.h.h))
   *     v[xh][xh] = Inverse of w'[xh][xh]    
   *       xh rows of w' selected by row[i]  (found parities)
   *       xh cols of w' selected by lost[i] (missing data)
   * NB 
   */

#ifdef FEC_DBG_PRINT_EVENTS
  if (trace > 1 && config.debug_fec)
    {
      printf ("FEC: Weight table:\n");
      fec_matrix_display ((fec_sym *) fec_weights, FEC_MAX_H, FEC_N - 1);	/* debug */
    }
#endif

  for (j = 0; j < xh; j++)
    {
      n = (fec_sym *) fec_weights[row[j]];
      r = (*v) + (j * xh * 2);	/* v is stored in [xh][xh*2] memory */

      for (i = 0; i < xh; i++)
	{
	  if (i + j + 1 == xh)
	    *(r + i) = 1;
	  else
	    *(r + i) = 0;

	  *(r + i + xh) = *(n + lost[i]);
	}

    }

  if ((err = fec_matrix_transform ((fec_sym *) v, xh, xh * 2)))
    {
      fprintf (stderr, "FEC: fec_matrix_transform failed. Error =%d\n", err);
      return (err);
    }

#ifdef FEC_DBG_PRINT_EVENTS
  if (trace > 1 && config.debug_fec)
    {
      printf ("FEC: Decode Matrix v\n");
      fec_matrix_display ((fec_sym *) v, xh, xh * 2);	/* */
    }
#endif

  /*
   * 2. Syndrom matrix (Time = O(h.k.c))
   *    s[xh][c] = w"[xh][k] * d/f[k][c]
   *       xh rows of w" selected by row[i] 
   *        k cols of w" selected by found[p]
   */
  for (i = 0; i < xh; i++)
    {
      p = fec_weights[row[i]];
      t = s[i];
      for (j = 0; j < c; j++)
	{
	  y = 0;
	  for (q = 0; q < k; q++)
	    {

	      z = found[q];

	      /* weight and data used so that the fec macro doesn't redundantly compute */
	      weight = *(p + z);

	      if (z < k)
		{
		  /* handle var length data packets */
		  if (plen[z] > j)
		    {
		      data = pdata[z][j];
		      FEC_MAC (weight, data, y);
		    }
		}
	      else
		{
		  /* parity packets should all be same length */
		  /* ERRORS appear at this line at high rate. (bss 5/16/2017) */
		  data = pparity[FEC_N - 2 - z][j];
		  FEC_MAC (weight, data, y);
		}
	    }
#ifdef FEC_DBG_PRINT_EVENTS
	  printf ("s=%d\n", y);
#endif
	  *(t + j) = y;		/* s[i][j] = y */
	}
    }
#ifdef FEC_DBG_PRINT_EVENTS
  if (trace > 1 && config.debug_fec)
    {
      printf ("FEC: Syndrome Matrix s\n");
      fec_matrix_display ((fec_sym *) s, xh, FEC_MAX_COLS);	/* */
    }
#endif

  /* 
   * 3. Regenerate missing data (Time = O(h.h.c))
   *     d[xh][c] = v[xh][xh] * s[xh][c]
   */
  x = xh - 1;
  u = s[x];
  for (i = 0; i < xh; i++)
    {
      p = (*v) + (i * xh * 2);

      m = p + xh;

#ifndef FEC_LOOP
      /* flag regenerated data as known */
      pstat[lost[x - i]] = FEC_FLAG_KNOWN;
#endif

      for (j = 0; j < c; j++)
	{
	  y = 0;
	  r = u + j;		/* s[xh-1][j] */

	  for (n = p; n < m; n++)
	    {

	      FEC_MAC (*n, *r, y);

	      r -= FEC_MAX_COLS;	/* s[xh-q-1] */

#ifdef FEC_DBG_PRINT_EVENTS
	      printf ("(%2x * %2x = %2x) ^= %2x\n",
		      *((*v) + (i * xh * 2) + (n - p)),
		      s[xh - (n - p) - 1][j], y, y);
#endif
	    }

	  data_lost_row = lost[xh - i - 1];

	  /* make sure we don't write past data buffer length */
	  if (plen[data_lost_row] > j)
	    pdata[data_lost_row][j] = y;	/* d[lost[xh-i-1]][j] = y */

#ifdef FEC_DBG_PRINT_EVENTS
	  printf ("d[%d][%d]=%x\n", xh - i - 1, j, y);
#endif
	}
    }
  IF_DEBUG_FEC fprintf (stderr, "<<<fec_blk_decode\n");
  IF_DEBUG_FEC fflush (stderr);
  return (xh);
}

/***************************************************************************/
/* FEC INITIALIZATION                                                      */
/***************************************************************************/

void
rse_init (void)
{
  fec_generate_math_tables ();
  fec_generate_weights ();
}

/*
 * Generate Weight matrix
 */
void
fec_generate_weights (void)
{

  fec_sym i, j;

  for (i = 0; i < FEC_MAX_H; i++)
    {
      for (j = 0; j < (FEC_N - 1); j++)
	fec_weights[i][j] = fec_2_index[(i * j % (FEC_N - 1))];	/* FEC 1 */
    }
#ifdef FEC_DBG_PRINT_WEIGHTS
  //  if (trace > 1 && config.debug_fec)
  if (trace > 1)
    {
      printf ("FEC: RS Weight table:\n");
      fec_matrix_display ((fec_sym *) fec_weights, FEC_MAX_H, FEC_N - 1);	/* debug */
    }
#endif

  fec_matrix_transform ((fec_sym *) fec_weights, FEC_MAX_H, FEC_N - 1);	/* FEC 2 */

#ifdef FEC_DBG_PRINT_WEIGHTS
  //  if (trace > 1 && config.debug_fec)
  if (trace > 1)
    {
      printf ("FEC: RSE Weight table:\n");
      fec_matrix_display ((fec_sym *) fec_weights, FEC_MAX_H, FEC_N - 1);	/* debug */
    }
#endif

}

/***************************************************************************/
/* Matrix Manipulation                                                     */
/***************************************************************************/
/*
 * Transforms (O(h**3)) (i_max x j_max) matrix p, so left hand side = I
 * If i_max=3 and j_max=7:
 *    1  1  1  1  1  1  1    1  0  0  6  1  6  7
 *    5  7  6  3  4  2  1 -> 0  1  0  4  1  5  5
 *    7  3  2  5  6  4  1    0  0  1  3  1  2  3
 */
int
fec_matrix_transform (fec_sym * p, fec_sym i_max, fec_sym j_max)
{

  fec_sym *n, *m, *q, *r, inv;
  fec_sym i, j, k, w;


#ifdef FEC_DBG_PRINT_TRANS
  printf ("FEC: Pre-tran\n");
  fec_matrix_display ((fec_sym *) p, i_max, j_max);
#endif

  /*
   * Make right hand side of matrix Triangular
   */
  for (k = 0; k < i_max; k++)
    {				/* Loop 1 */
      for (i = 0; i < i_max; i++)
	{			/* Loop 2 */
	  /* 
	   * Multiply rows so (max - k)'th column has all 1's
	   */
	  q = (p + (i * j_max) + j_max - 1);	/* last row i entry */
	  m = q - j_max;
	  w = i;

	  while (*(q - k) == 0)
	    {			/* if zero */
	      if (++w == i_max)
		{
#ifdef FEC_DBG_PRINT_EVENTS
		  printf ("0******\n");
		  printf ("k=%d, i=%d\n", k, i);
		  fec_matrix_display (p, i_max, j_max);
#endif
		  return (FEC_ERR_TRANS_FAILED);	/* failed */
		}

	      if (*(p + (w * j_max) + j_max - 1 - k) != 0)
		{		/* swap rows */
#ifdef FEC_DBG_PRINT_EVENTS
		  printf ("FEC: swap rows (not done yet!)\n");
#endif
		  return (FEC_ERR_TRANS_SWAP_NOT_DONE);	/* Not done yet! */
		}
	    }

	  inv = fec_invefec[*(q - k)];
    //JOSH - we need to make this change because otherwise the loop guard is not provable -
    //when the loop exits we have n < m, so n can point to unitialized memory
    // n = q + 1;
    // while(n > m) {
    //   n--;
    //   *n = fec_gf_mult(*n, inv);
    // }
    for (n = q; n > m; n--) /* Loop 3 */
      *n = fec_gf_mult (*n, inv);

#ifdef FEC_DBG_PRINT_TRANS

	  printf ("FEC: i=%d inv=%2x\n", i, inv);
	  fec_matrix_display (p, i_max, j_max);

#endif

	}

#ifdef FEC_DBG_PRINT_TRANS

      printf ("FEC: max-(k=%d)'th column should be all 1's\n", k);
      fec_matrix_display (p, i_max, j_max);

#endif

      /*
       * Add k'th row to all rows (except k'th row)
       */
      r = (p + (k * j_max) + j_max - 1);	/* last row k entry */
      for (i = 0; i < i_max; i++)
	{
	  if (i != k)
	    {
	      q = (p + (i * j_max) + j_max - 1);	/* last row i entry */
	      for (j = 0; j < j_max; j++)
		*(q - j) = *(q - j) ^ (*(r - j));	/* add */
	    }
	}

#ifdef FEC_DBG_PRINT_TRANS

      printf ("FEC: max-(k=%d)'th column all 0's, except for one 1\n", k);
      fec_matrix_display (p, i_max, j_max);

#endif

    }
  /*
   * Triangular to Identity (make elements in triangle 1)
   */
  for (i = 0; i < i_max - 1; i++)
    {				/* not need on last */
      q = (p + (i * j_max) + j_max - 1);	/* last row i entry */
      m = q - j_max + 1; //JOSH : same as above
      inv = fec_invefec[*(q - i)];
      // //JOSH - same as above
      // n = q + 1;
      // while(n > m) {
      //   n--;
      //   *n = fec_gf_mult(*n, inv);
      // }
      for (n = q; n > m; n--) /* Loop 3 */
  *n = fec_gf_mult (*n, inv);
    }

  return (0);

#ifdef FEC_DBG_PRINT_TRANS

  printf ("FEC: Done tran\n");
  fec_matrix_display (p, i_max, j_max);	/* debug */

#endif

}

/***************************************************************************/
/* GF Multiplication and Inversion (1D tables)                             */
/***************************************************************************/
/*
 * Generate index<->power and invefec tables
 *   a) index, bits of the polynomial representation
 *   b) power of the primitive element "1"
 *   c) invefec (a.b=1)
 */
void
fec_generate_math_tables (void)
{

  int mod;
  int temp;			/* use temp to prevent overflow */
  int i;

  mod = fec_find_mod ();
  for (i = 0; i < FEC_N; i++)
    {
      if (i == 0)
	fec_2_index[i] = i + 1;
      else
	{
	  temp = fec_2_index[i - 1] << 1;
	  if (temp >= FEC_N)
	    fec_2_index[i] = temp ^ mod;
	  else
	    fec_2_index[i] = temp;
	}
      fec_2_power[fec_2_index[i]] = i;	/* 0'th index is not used */
    }
  for (i = 0; i < FEC_N; i++)
    fec_invefec[fec_2_index[FEC_N - 1 - fec_2_power[i]]] = i;

#ifdef FEC_MAC_LOOKUP
  gen_gf_mult_table (gf_mult_table);
#endif

}

/*
 * Find irred. polynomial for Modulus
 * NB: Modulus is one bit bigger than fec_sym so use integers
 */
int
fec_find_mod (void)
{
  int modulus;

  switch (FEC_N)
    {
    case 8:
      modulus = 0xb;
      break;
    case 16:
      modulus = 0x13;
      break;
    case 32:
      modulus = 0x25;
      break;
    case 64:
      modulus = 0x43;
      break;
    case 128:
      modulus = 0x89;
      break;
    case 256:
      modulus = 0x11d;
      break;
    default:
      fprintf (stderr, "FEC: Don't know mod FEC_N=%d\n", FEC_N);
      return (FEC_ERR_MOD_NOT_FOUND);
    }
  return (modulus);
}


#ifdef FEC_MAC_LOOKUP
void
gen_gf_mult_table (fec_sym gf_table[FEC_N][FEC_N])
{
  int i = 0, j = 0;

  for (i = 0; i < FEC_N; i++)
    {
      for (j = 0; j < FEC_N; j++)
	gf_table[i][j] = fec_gf_mult (i, j);

    }
}

#ifdef FEC_DBG_EVENTS
void
print_gf_mult_table (fec_sym gf_table[FEC_N][FEC_N])
{
  int i = 0, j = 0;

  for (i = 0; i < FEC_N; i++)
    {
      for (j = 0; j < FEC_N; j++)
	printf ("%d\t", gf_table[i][j]);

      printf ("\n");

    }

}
#endif
#endif

#ifdef FEC_DBG_EVENTS

/***************************************************************************/
/* Debug                                                                   */
/***************************************************************************/

/*
 * Display 2D Matrix 
 */
void
fec_matrix_display (fec_sym * p, fec_sym i_max, fec_sym j_max)
{

  int i, j;

  for (i = 0; i < i_max; i++)
    {
      for (j = j_max - 1; j >= 0; j--)
	printf ("%2x ", *(p + (i * j_max) + j));
      printf ("\n");
    }
}

/*
 * Display tables (just for debug)
 */
void
fec_display_tables (void)
{
  int i;
  int mod;

  mod = fec_find_mod ();
  printf ("FEC: num  2_index 2_power invefec   (mod=%x)\n", mod);
  for (i = 0; i <= FEC_N - 1; i++)
    {
      printf ("%2x     %2x      ", i, fec_2_index[i]);
      printf ("%2x      %2x\n", fec_2_power[i], fec_invefec[i]);
    }
}

#endif

#ifdef FEC_DEBUG_PRINT
void
rse_code_print (int k, int h, int c, unsigned char **pdata, int *plen,
		char *pstat)
{

  int i, j;

  IF_DEBUG_FEC fprintf (stderr, "FEC: Codeword (c=%d) h=%d k=%d\n", c, h, k);

  //  if (trace > 1 && config.debug_fec)
  if (trace > 1)
    {
      for (i = 0; i < k; i++)
	{
	  fprintf (stderr, "FEC: data packet %d:  ", i);
	  for (j = 0; j < c; j++)
	    {
	      if ((pstat[i] == FEC_FLAG_WANTED))
		fprintf (stderr, "?   ");
	      else
		{
		  /* handle var length data packets */
		  if (plen[i] > j)
		    fprintf (stderr, "%u   ", *(pdata[i] + j));
		  else
		    fprintf (stderr, "-   ");
		}

	    }
	  fprintf (stderr, " len=%d, flag=%d\n", plen[i], pstat[i]);
	}

      fprintf (stderr, "----------------------------\n");

      for (i = 0; i < h; i++)
	{
	  fprintf (stderr, " fec packet %d:  ", i);
	  for (j = 0; j < c; j++)
	    {
	      if (pdata[k + i])
		fprintf (stderr, "%u   ", *(pdata[k + i] + j));
	      else
		fprintf (stderr, "?   ");
	    }

	  fprintf (stderr, "\n");

	}

      fprintf (stderr, "\n");
    }

}
#endif
