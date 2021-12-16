#include "slice_encode.h"

unsigned char weights[FEC_H][FEC_K] = {{0x7c, 0x8c, 0x55, 0x34, 0x18, 0x7f}, {0x78, 0x93, 0x40, 0x5d, 0x2b, 0x39}, {0x8a, 0x8c, 0x60, 0xbe, 0xd, 0x85}};

// Each buffer is a h x SLICE_SIZE matrix
unsigned char parity_buffers[SLICES][FEC_H][SLICE_SIZE];

//Field tables must already be generated by batch processor, so there is nothing to do
int initialize() {
  return 0;
}

// The caller must ensure that k = 6, h = 3, 0 \leq slice_batchnum < SLICES
int start_slice_batch(unsigned int slice_batchnum, unsigned int k, unsigned int h) {
  //set the buffer to 0 (since it may have been used before)
  for(int i = 0; i < h; i++) {
    for(int j = 0; j < SLICE_SIZE; j++) {
      parity_buffers[slice_batchnum][i][j] = 0;
    }
  }
  return 0;
}

int encode_packet_slice(unsigned int slice_batchnum, unsigned int j, unsigned char *slice) {
  for(int m = 0; m < FEC_H; m++) {
    for(int n = 0; n < SLICE_SIZE; n++) {
      parity_buffers[slice_batchnum][m][n] ^= mult(weights[m][j], slice[n]); 
    }
  }
  return 0;
}


int encode_parity_slice(unsigned int slice_batchnum, unsigned int i, unsigned char *slice) {
  for(int j = 0; j < SLICE_SIZE; j++) {
    slice[j] = parity_buffers[slice_batchnum][i][j];
  }
  return 0;
}

int end_slice_batch(uint slice_batchnum) {
  return 0;
}