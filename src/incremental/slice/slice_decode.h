// API for decoding packets incrementally

#include "batch_common.h"

/* called once, before any of the other functions. Returns 0 on success */
int initialize();

/* Registers a new batch of slices, in which k will be the number of data slices,
   and h will be the number of parity slices.  Returns 0 on success.
   An implementation is required to insist that k=6 and h=3, and return failure otherwise.
   0 <= slice_batchnum < SLICES, where SLICES is an implementation-dependent constant.
 */
int start_batch(unsigned int slice_batchnum, unsigned int k, unsigned int h);

/* Inform the decoder that the contents of the jth slice are the bytes
   starting at slice (of length SLICE_SIZE)
   0 <= j < k + h = 9
   0 <= recieved < 2^9 - this is a bitmap of the recieved packets, where the ith bit is 1 iff the ith packet is recieved
*/
int decode_packet_slice(unsigned int slice_batchnum, unsigned int j, unsigned short recieved, unsigned char *slice);

/* The slice pointer points to an uninitialized array of length SLICE_SIZE;
   fill it in with the bytes of the ith slice, and 0 <= i < h. 
   recieved is the same bitmap as above
   Return 0 on success
   Should only be called once all k slices in batch slice_batchnum have been sent to the decoder
*/ 
int get_decoded_packet_slice(unsigned int slice_batchnum, unsigned int i, unsigned short recieved, unsigned char *slice);

/* Unregister this batch.  The same batchnum may be used again in future batches.
*/
int end_batch(unsigned int slice_batchnum);

