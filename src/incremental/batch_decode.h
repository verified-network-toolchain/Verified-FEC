// API for decoding packets incrementally

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

/* Inform the decoder that the contents of the jth packet are the bytes
   starting at packet (of length packet_size)
   0 <= j < k + h = 9
   0 <= recieved < 2^9 - this is a bitmap of the received packets, where the ith bit is 1 iff the ith packet is recieved
*/
int decode_packet(unsigned int batchnum, unsigned int j, unsigned int received, unsigned int packet_size, unsigned char *packet);

/* The packet pointer points to an uninitialized array of length batch_packet_size;
   fill it in with the bytes of the ith packet, and 0 <= i < k+h. 
   received is the same bitmap as above
   Return 0 on success
   Should only be called once all k packets in batch batchnum have been sent to the decoder
*/ 
int get_decoded_packet(unsigned int batchnum, unsigned int i, unsigned int received, unsigned int packet_size, unsigned char *packet);

/* Unregister this batch.  The same batchnum may be used again in future batches.
*/
int end_batch(unsigned int batchnum);

