
int FEC_N = 128;
int modulus = 0x89;

unsigned char fec_2_power[128];	/* index->power table */
unsigned char fec_2_index[128];	/* power->index table */
unsigned char fec_invefec[128]; /* inverse table */
unsigned char gf_mult_table[128][128]; /*mult table*/

void generate_index_power_tables(void) {
  int i;
  int temp;
  for (i = 0; i < FEC_N; i++) {
      if (i == 0) {
        fec_2_index[i] = i + 1;
      }
      else {
        temp = fec_2_index[i - 1] << 1;
        if (temp >= FEC_N) {
          fec_2_index[i] = temp ^ modulus;
        }
        else {
          fec_2_index[i] = temp;
        }
      }
      fec_2_power[fec_2_index[i]] = i;	/* 0'th index is not used */
  }
}

void generate_inverse_table(void) {
  for (int i = 0; i < FEC_N; i++) {
    fec_invefec[fec_2_index[FEC_N - 1 - fec_2_power[i]]] = i;
  }
}

unsigned char multiply (unsigned char a, unsigned char b) {
  if (a && b) {
    unsigned char pow = fec_2_power[a] + fec_2_power[b];
    if(pow > FEC_N - 1) {
      return (fec_2_index[(pow - (FEC_N - 1))]);
    }
    else {
      return  (fec_2_index[pow]);
    }
  }
  else {
    return 0;
  }
}

void generate_mult_table(void) {
  for (int i = 0; i < FEC_N; i++) {
      for (int j = 0; j < FEC_N; j++) {
        gf_mult_table[i][j] = multiply (i, j);
      }
    }
}

int main(void) {
  return 0;
}