//API for encoding incrementally using fixed-size slices of packets

//TODO: What if packet doesn't divide evenly into slices?

#include "slice_common.h"

/* called once, before any of the other functions. Returns 0 on success */
int initialize();

/* Registers a new batch of slices, in which k will be the number of data slices,
   and h will be the number of parity slices.  Returns 0 on success.
   An implementation is required to insist that k=6 and h=3, and return failure otherwise.
   0 <= slice_batchnum < SLICES, where SLICES is an implementation-dependent constant.
 */
int start_batch(unsigned int slice_batchnum, unsigned int k, unsigned int h);

/* Inform the encoder that the contents of the jth slice are the bytes
   starting at slice, exactly SLICE_SIZE of them.
   0 <= j < k, where k is the number of data slices registered for this batch.
   The k different slices may come out of order, but no j value may be repeated.
   Returns 0 for success. 
*/
int encode_packet_slice(unsigned int slice_batchnum, unsigned int j, unsigned char *slice);

/* The slice pointer points to an uninitialized array of length SLICE_SIZE;
   fill it in with the bytes of the ith parity slice, and 0 <= i < h. 
   Return 0 on success
   Should only be called once all k slices in batch slice_batchnum have been encoded
*/
int encode_parity_slice(unsigned int slice_batchnum, unsigned int i, unsigned char *slice); 

/* Unregister this batch.  The same batchnum may be used again in future batches.
*/
int end_batch(unsigned int slice_batchnum);