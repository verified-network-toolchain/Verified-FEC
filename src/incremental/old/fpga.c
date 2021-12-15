
#define FEC_K (6)
#define FEC_H (3)
// These could be implementation-dependent, but we need them to be static to initialize parity_buffers.
// Their values do not affect the correctness
#define BATCHES (300)
#define MAX_PACKET_SIZE (100)

#define FIELD_SIZE (256U)

unsigned char weights[FEC_H][FEC_K] = {{0x7c, 0x8c, 0x55, 0x34, 0x18, 0x7f}, {0x78, 0x93, 0x40, 0x5d, 0x2b, 0x39}, {0x8a, 0x8c, 0x60, 0xbe, 0xd, 0x85}};
// Each buffer is a h x c matrix
unsigned char parity_buffers[BATCHES][FEC_H][MAX_PACKET_SIZE];
//unsigned int packet_sizes[BATCHES];

//field tables
unsigned char fec_2_index[FIELD_SIZE];
unsigned char fec_2_power[FIELD_SIZE];

void generate_field_tables (void) {
  int mod = 0x11d;  

  for (int i = 0; i < FIELD_SIZE; i++) {
    if (i == 0) {
      fec_2_index[i] = i + 1;
    }
    else {
      int temp = fec_2_index[i - 1] << 1; /* use temp to prevent overflow */
      if (temp >= FIELD_SIZE)
        fec_2_index[i] = temp ^ mod;
      else
        fec_2_index[i] = temp;
    }
    fec_2_power[fec_2_index[i]] = i;  /* 0'th index is not used */
  }
}

unsigned char mult(unsigned char a, unsigned char b) {
  if (a && b) {
    if ((fec_2_power[a]+fec_2_power[b]) > FIELD_SIZE-1U) {
      return (fec_2_index[((fec_2_power[a]+fec_2_power[b])-(FIELD_SIZE-1U))]);
    }
    else {
      return ((fec_2_index[(fec_2_power[a]+fec_2_power[b])]));
    }
  }
  else {
    return 0;
  }
}

// Initialize the static weight matrix
int initialize() {
  generate_field_tables();
  return 0;
}

// The caller must ensure that k = 6, h = 3, 0 \leq batchnum < BATCHES, and 0 \leq batch_packet_size < MAX_PACKET_SIZE
int start_batch(unsigned int batchnum, unsigned int k, unsigned int h, unsigned int batch_packet_size) {
  //packet_sizes[batchnum] = batch_packet_size; 
  //set the buffer to 0 (since it may have been used before) - only need to fill until h and batch_packet_size
  for(int i = 0; i < h; i++) {
    for(int j = 0; j < batch_packet_size; j++) {
      parity_buffers[batchnum][i][j] = 0;
    }
  }
  return 0;
}

/* Inform the encoder that the contents of the jth packet are the bytes
   starting at packet, exactly packet_size of them, where packet_size <= batch_packet_size.
   0 <= j < k, where k is the number of data packets registered for this batch.
   The k different packets may come out of order, but no j value may be repeated.
   Returns 0 for success. 
*/
int encode_packet(unsigned int batchnum, unsigned int j, unsigned int packet_size, unsigned char *packet) {
  for(int m = 0; m < FEC_H; m++) {
    for(int n = 0; n < packet_size; n++) {
      parity_buffers[batchnum][m][n] ^= mult(weights[m][j], packet[n]); 
    }
  }
  return 0;
}

/* The packet pointer points to an uninitialized array of length batch_packet_size;
   fill it in with the bytes of the ith parity packet, whose length is the max of all
   the packet_sizes of the batch, and 0 <= i < h. 
   Return 0 on success
*/
int encode_parity(unsigned int batchnum, unsigned int packet_size, unsigned int i, unsigned char *packet) {
  for(int j = 0; j < packet_size; j++) {
    packet[j] = parity_buffers[batchnum][i][j];
  }
  return 0;
}
