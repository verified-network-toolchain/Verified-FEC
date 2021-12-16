#include "./batch_decode.h"
#include "slice_decode.h"

int initialize() {
  generate_math_tables();
  return 0;
}

//This is almost identical to batch_encode
//We don't need slice numbers to be consistent, though they happen to be

//We need to mantain the current upper bound on length for the packets in each batch so we know if we need to initialize a new slice
unsigned int num_slices[BATCHES];

//Unlike in encoder, we NEED batch_packet_size to be an overall upper bound, since some packets are missing; we need to know how many slices are needed for them
int start_batch(unsigned int batchnum, unsigned int k, unsigned int h, unsigned int batch_packet_size) {
   //Start the batches for the slices we know we have. We may have to add more later.
  num_slices[batchnum] = batch_packet_size / SLICE_SIZE + 1;
  for(int i = 0; i < batch_packet_size / SLICE_SIZE + 1) {
    start_slice_batch(batchnum * SLICE_SIZE + i, k, h);
  }
  return 0;
}

int decode_packet(unsigned int batchnum, unsigned int j, unsigned int recieved, unsigned int packet_size, unsigned char *packet) {
  //Decoding just splits up packet into multiple pieces and calls decode_packet_slice
  //TODO: can we just do the pointer arithmetic, or do we actually want different buffers?

  //TODO: this assumes that the packet is a multiple of the SLICE_SIZE, which is not necessarily true
  for(int i = 0; i < num_slices[batchnum] - 1; i++) {
    decode_packet_slice(batchnum * SLICE_SIZE + i, j, recieved, packet + (SLICE_SIZE * i));
  }
  return 0;
}

//NOTE: it must be the case that packet_size >= num_slices[batchnum]
int get_decoded_packet(unsigned int batchnum, unsigned int i, unsigned int recieved, unsigned int packet_size, unsigned char *packet) {
   //Get the parities for each slice, put in appropriate place in packet buffer
  unsigned int slices = num_slices[batchnum];
  //TODO: again, assumes multiples of SLICE_SIZE (and if we assume this, dont need +/- 1)
  for(int j = 0; j < slices - 1; j++) {
    get_decoded_packet_slice(batchnum * SLICE_SIZE + j, i, received, packet + (SLICE_SIZE * j));
  }
  return 0;
}

int end_batch(unsigned int batchnum) {
   return 0;
}

