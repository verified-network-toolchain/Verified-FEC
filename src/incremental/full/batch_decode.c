//Decode by saving all packets and using fec.c

#include "../batch_decode.h"
#include "../../fecActuator/fec.h"
#include <stdlib.h>
#include <string.h>

//Mapping from batchnums to packets and lengths
unsigned char **packet_data[BATCHES];
int *packet_lengths[BATCHES]; //TODO: could be done all statically by using FEC_K + FEC_H (and same for stats)
//Find "c" for each batch
unsigned int max_lengths[BATCHES];
//Stats for each batch
char *packet_stats[BATCHES];
int decode_done[BATCHES]; //Are the parities computed for a batch?

int initialize() {
  rse_init();
  return 0;
}

int start_batch(unsigned int batchnum, unsigned int k, unsigned int h, unsigned int batch_packet_size) {
  //Allocate space for packets, lengths, stats
  //We don't need batch_packet_size
  unsigned char **packets = calloc(k+h, sizeof(unsigned char *));
  if(packets == NULL) return -1;
  packet_data[batchnum] = packets;
  int *lengths = calloc(k+h, sizeof(int));
  if(lengths == NULL) return -1;
  packet_lengths[batchnum] = lengths;
  char *stat_data = malloc(k+h, sizeof(char));
  if(stat_data == NULL) return -1;
  //stats should be all 1 (missing); we will fill in as we recieve
  for(int i = 0; i < k + h; i++) {
    stat_data[i] = FEC_FLAG_WANTED;
  } 
  packet_stats[batchnum] = stat_data;
  max_lengths[batchnum] = 0;
  decode_done[batchnum] = 0;
  return 0;
}

//In this implementation, we ignore the bitmap, because we get each packet before doing anything anyway
int decode_packet(unsigned int batchnum, unsigned int j, unsigned int recieved, unsigned int packet_size, unsigned char *packet) {
  //Allocate space for packet copy - we don't know what will happen to the passed-in pointer
  unsigned char *new_packet = malloc(packet_size);
  if(new_packet == NULL) return -1;
  memcpy(new_packet, packet, packet_size);
  packet_data[batchnum][j] = new_packet;
  packet_lengths[batchnum][j] = packet_size;
  packet_stats[batchnum][j] = FEC_FLAG_KNOWN;
  //If this is a parity packet, set c (all parity packets have the same length)
  if(j >= FEC_K) {
    max_lengths[batchnum] = packet_size;
  }
  return 0;
}

int get_decoded_packet(unsigned int batchnum, unsigned int i, unsigned int recieved, unsigned int packet_size, unsigned char *packet) {
  if(!decode_done[batchnum]) {
    //If c is not yet initialized, we did not receive any parity packets, so the original data must have been recieved (or there were too many erasures). We send an error (TODO: should we just return original packet?)
    if(max_lengths[batchnum] == 0) return -1;
    //Mark length of missing packets as c, as in black actuator
    for(int j = 0; j < FEC_K + FEC_H; j++) {
      if(packet_stats[j] == FEC_FLAG_WANTED) {
        packet_lengths[batchnum][j] = max_lengths[batchnum];
      }
    }
    fec_blk_decode(FEC_K, max_lengths[batchnum], packet_data[batchnum], packet_lengths[batchnum], packet_stats[batchnum]);
    decode_done[batchnum] = 1;
  }
  unsigned char *recovered_packet = packets[i];
  //Need packet_size >= max(packets)
  memcpy(packet, recovered_packet, max_lengths[batchnum]);
  return 0;
}

//Free all allocated memory
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

  //Free stats
  char *stats = packet_stats[batchnum];
  if(stats) {
    free(stats);
  }
  packet_stats[batchnum] = NULL;

  //TODO: do there here or in start_batch?
  max_lengths[batchnum] = 0;
  decode_done[batchnum] = 0;
  return 0;
}