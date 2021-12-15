#include "batch_common.h"

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