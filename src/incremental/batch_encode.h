// API for encoding packets incrementally

#include "batch_common.h"

/* called once, before any of the other functions. Returns 0 on success */
int initialize();

//TODO: do we still need batch_packet_size with slice version? see
/* Registers a new batch of packets, in which k will be the number of data packets,
   and h will be the number of parity packets.  Returns 0 on success.
   An implementation is required to insist that k=6 and h=3, and return failure otherwise.
   0 <= batchnum < BATCHES, where batches is an implementation-dependent constant.
   0 <= batch_packet_size < MAX_PACKET_SIZE
 */

int start_batch(unsigned int batchnum, unsigned int k, unsigned int h, unsigned int batch_packet_size);

/* Inform the encoder that the contents of the jth packet are the bytes
   starting at packet, exactly packet_size of them, where packet_size <= batch_packet_size.
   0 <= j < k, where k is the number of data packets registered for this batch.
   The k different packets may come out of order, but no j value may be repeated.
   Returns 0 for success. 
*/
int encode_packet(unsigned int batchnum, unsigned int j, unsigned int packet_size, unsigned char *packet);

/* The packet pointer points to an uninitialized array of length batch_packet_size;
   fill it in with the bytes of the ith parity packet, whose length is the max of all
   the packet_sizes of the batch, and 0 <= i < h. 
   Return 0 on success
   Should only be called once all k packets in batch batchnum have been encoded
*/
int encode_parity(unsigned int batchnum, unsigned int i, unsigned int packet_size, unsigned char *packet); 

/* Unregister this batch.  The same batchnum may be used again in future batches.
*/
int end_batch(uint batchnum);






