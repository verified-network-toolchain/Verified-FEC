//Encode by saving all packets and using fec.c

#include "../batch_encode.h"
#include "../../fecActuator/fec.h"
#include <stdlib.h>
#include <string.h>

//Mapping from batchnums to packets and lengths
unsigned char **packet_data[BATCHES];
int *packet_lengths[BATCHES];
//Mantain maximum packet seen so far
unsigned int max_lengths[BATCHES];
int parities_done[BATCHES]; //Are the parities computed for a batch?

int initialize() {
  rse_init();
  return 0;
}

//Works for any h and k
int start_batch(unsigned int batchnum, unsigned int k, unsigned int h, unsigned int batch_packet_size) {
  //Allocate space for packets and lengths
  //We don't need batch_packet_size
  unsigned char **packets = calloc(k+h, sizeof(unsigned char *));
  if(packets == NULL) return -1;
  packet_data[batchnum] = packets;
  int *lengths = calloc(k+h, sizeof(int));
  if(lengths == NULL) return -1;
  packet_lengths = lengths;
  max_lengths[batchnum] = 0;
  parities_done[batchnum] = 0;
  return 0;
}

//Just stores a copy of the packet. When we first call encode_parity, we will compute the parity packets
int encode_packet(unsigned int batchnum, unsigned int j, unsigned int packet_size, unsigned char *packet) {
  //Allocate space for packet copy - we don't know what will happen to the passed-in pointer
  unsigned char *new_packet = malloc(packet_size);
  if(new_packet == NULL) return -1;
  memcpy(new_packet, packet, packet_size);
  packet_data[batchnum][j] = new_packet;
  packet_lengths[batchnum][j] = packet_size;
  if(packet_size > max_lengths[batchnum]) {
    max_lengths[batchnum] = packet_size;
  }
  return 0;
}

//NOTE: this currently hard codes at 6 and 3, but it would be very easy to make generic (just store k and h from start_batch)
int encode_parity(unsigned int batchnum, unsigned int i, unsigned int packet_size, unsigned char *packet) {
  unsigned char **packets = packet_data[batchnum];
  if(!parities_done[batchnum]) {
    //Calculate parities
    //Allocate space for pstat
    char *stats = calloc((FEC_K + FEC_H) * sizeof(char));
    if(stats == NULL) return -1;
    fec_blk_encode(FEC_K, FEC_H, max_lengths[batchnum], packet_data[batchnum], packet_lengths[batchnum], stats);
    //free stats because it is never used again
    //TODO: should we use a single, static stats array? It's kind of cheating, but works because we know fec_blk_encode doesn't modify it and because we assume k=6 and h=3
    free(stats);
  }
  unsigned char *parity_packet = packets[FEC_K + i];
  //Need packet_size >= max(packets)
  memcpy(packet, parity_packet, max_lengths[batchnum]);
  return 0;
}

//Free all allocated memory
//NOTE: some of the intermediate steps could have failed or not been run. So we need to check that each packet is nonzero before freeing
int end_batch(unsigned int batchnum) {
  //Free packet data
  unsigned char **packets = packet_data[batchnum];
  if(packets) {
    for(int i = 0; i < FEC_H + FEC_K; i++) {
      if(packets[i]) {
        free(packets[i]);
      }
    }
    free(packets);
  }
  packet_data[batchnum] = NULL; //Otherwise, points to invalid pointer (which we shouldnt read, but just in case)

  //Free lengths
  int *lengths = packet_lengths[batchnum];
  if(lengths) {
    free(lengths);
  }
  packet_lengths[batchnum] = NULL;

  //TODO: do there here or in start_batch?
  max_lengths[batchnum] = 0;
  parities_done[batchnum] = 0;
  return 0;
  

}
