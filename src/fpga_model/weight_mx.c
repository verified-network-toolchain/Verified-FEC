//The parts of fec.c that deal with generating the weight matrix, so we can print it and input it statically

#include <stdio.h>    /* for fprintf(), etc.      */


#define   FEC_MAX_H (128)            /* MAX of h parities */
#define FEC_MAX_COLS  (16000)   /* Max symbols/packet (c) */
#define         FEC_N           (256)           /* Max k+h = 2^m */


typedef unsigned char fec_sym;    /* m bit symbol */

#define FEC_ERR_INVALID_PARAMS        (-1)
#define FEC_ERR_ENC_MISSING_DATA      (-20)
#define FEC_ERR_MOD_NOT_FOUND         (4)
#define FEC_ERR_TRANS_FAILED          (82)
#define FEC_ERR_TRANS_SWAP_NOT_DONE   (83)

void fec_generate_math_tables(void);
int fec_find_mod(void);
int fec_matrix_transform(fec_sym *p, fec_sym i_max, fec_sym j_max);
void rse_init(void);
void fec_generate_weights(void);

fec_sym fec_2_power[FEC_N];	/* index->power table */
fec_sym fec_2_index[FEC_N];	/* power->index table */
fec_sym fec_invefec[FEC_N];	/* multiplicative inverse */
fec_sym fec_weights[FEC_MAX_H][FEC_N - 1];	/* FEC weight table */

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
	  m = q - j_max + 1; //JOSH - added +1 invaid otherwise (if i = 0, m = p - 1)
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
    n = q + 1;
    while(n > m) {
      n--;
      *n = fec_gf_mult(*n, inv);
    }
	  // for (n = q; n >= m; n--)	/* Loop 3 */ //JOSH - need n >= m because of previous change
	  //   *n = fec_gf_mult (*n, inv);

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
      //JOSH - same as above
      n = q + 1;
      while(n > m) {
        n--;
        *n = fec_gf_mult(*n, inv);
      }
 //      for (n = q; n > m; n--)//	 Loop 3 
	// *n = fec_gf_mult (*n, inv);
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

int main() {
  rse_init();
  fec_matrix_display((fec_sym *) (fec_weights), FEC_MAX_H, FEC_N - 1);
}