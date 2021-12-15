#include "slice_decode.h"

//We need to store all of the matrices to multiply by. There are C(9,3) = 84 possible matrices, each of size 3 x 3
unsigned char syndromes[84][FEC_H][FEC_H]; //TODO: fill in, or see how to do this nicely

// Each buffer is a h x SLICE_SIZE matrix
unsigned char packet_buffers[SLICES][FEC_H][SLICE_SIZE];

//Function to convert bitmap of recieved packets to syndrome index
//NOTE: proving this correct will not be trivial
//other option is to have 2^9=512 indices in syndromes matrix and leave most unused
int bitmap_to_index(unsigned short bitmap) {
  return 0; //TODO
}

//Given the bitmap of recieved packets and the index of the packet, determine whether this packet is the first, second, or third one stored
int bitmap_to_packet_index(unsigned short bitmap, unsigned int i) {
  //NOTE: need bitmap to be valid
  return 0; //TODO
}

//Field tables must already be generated by batch processor, so there is nothing to do
int initialize() {
  return 0;
}

// The caller must ensure that k = 6, h = 3, 0 \leq slice_batchnum < SLICES
int start_slice_batch(unsigned int slice_batchnum, unsigned int k, unsigned int h) {
  //set the buffer to 0 (since it may have been used before)
  for(int i = 0; i < h; i++) {
    for(int j = 0; j < SLICE_SIZE; j++) {
      packet_buffers[slice_batchnum][i][j] = 0;
    }
  }
  return 0;
}

//Essentially the same as encoding - another matrix multiply
int decode_packet_slice(unsigned int slice_batchnum, unsigned int j, unsigned short recieved, unsigned char *slice) {
  int syn_idx = bitmap_to_index(recieved);
  for(int m = 0; m < FEC_H; m++) {
    for(int n = 0; n < SLICE_SIZE; n++) {
      packet_buffers[slice_batchnum][m][n] ^= mult(syndromes[syn_idx][m][j], slice[n]); 
    }
  }
  return 0;
}

//i refers to the true index of the packet (ie: 6). We need to know if it is the 1st, 2nd, or 3rd missing packet; hence bitmap_to_packet_index
int get_decoded_packet_slice(unsigned int slice_batchnum, unsigned int i, unsigned short recieved, unsigned char *slice) {
  int idx = bitmap_to_packet_index(bitmap, i);
  for(int j = 0; j < SLICE_SIZE; j++) {
    slice[j] = packet_buffers[slice_batchnum][idx][j];
  }
  return 0;
}

int end_slice_batch(unsigned int slice_batchnum) {
  return 0;
}
