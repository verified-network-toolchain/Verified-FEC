//Slice-based implememtation of batch encoding
//The primary purpose of this layer is to handle splitting the packet into slices and to keep track of the mapping from batchnums to slice_batchnums

#include "./batch_encode.h"
#include "slice_encode.h"


int initialize() {
  generate_math_tables();
  return 0;
}

//NOTE: We could do a mapping with allocating new integers, but we would need to keep track of which ones are used and then freed
//Instead, we simply take batchnum * SLICE_SIZE + (number of slice in packet) - there are up to MAX_PACKET_SIZE / SLICE_SIZE possible slice
//numbers for a batch

//We need to mantain the current upper bound on length for the packets in each batch so we know if we need to initialize a new slice
unsigned int num_slices[BATCHES];


int start_batch(unsigned int batchnum, unsigned int k, unsigned int h, unsigned int batch_packet_size) {
  //Start the batches for the slices we know we have. We may have to add more later.
  num_slices[batchnum] = batch_packet_size / SLICE_SIZE + 1;
  for(int i = 0; i < batch_packet_size / SLICE_SIZE + 1) {
    start_slice_batch(batchnum * SLICE_SIZE + i, k, h);
  }
  return 0;
}

int encode_packet(unsigned int batchnum, unsigned int j, unsigned int packet_size, unsigned char *packet) {
  //Check to see if length is larger and if we need to allocate a new slice
  unsigned int slices = packet_size / SLICE_SIZE + 1;
  if(slices > num_slices[batchnum]) {
    for(int i = num_slices[batchnum]; i < slices; i++) {
      start_slice_batch(batchnum * SLICE_SIZE + i, FEC_K, FEC_H);
    }
    num_slices[batchnum] = slices;
  }

  //Actual encoding just splits up packet into multiple pieces and calls encode_packet_slice
  //TODO: can we just do the pointer arithmetic, or do we actually want different buffers?

  //TODO: this assumes that the packet is a multiple of the SLICE_SIZE, which is not necessarily true
  for(int i = 0; i < slices - 1; i++) {
    encode_packet_slice(batchnum * SLICE_SIZE + i, j, packet + (SLICE_SIZE * i));
  }
  return 0;
}

//NOTE: it must be the case that packet_size >= num_slices[batchnum] (ie: this packet is at least as large as max(batch_packet_size, max(size of packets seen)))
int encode_parity(unsigned int batchnum, unsigned int i, unsigned int packet_size, unsigned char *packet) {
  //Get the parities for each slice, put in appropriate place in packet buffer
  unsigned int slices = num_slices[batchnum];
  //TODO: again, assumes multiples of SLICE_SIZE (and if we assume this, dont need +/- 1)
  for(int j = 0; j < slices - 1; j++) {
    encode_parity_slice(batchnum * SLICE_SIZE + j, i, packet + (SLICE_SIZE * j));
  }
  return 0;
}

int end_batch(unsigned int batchnum) {
  return 0;
}