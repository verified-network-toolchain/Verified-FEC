#define BATCHES (300)
#define MAX_PACKET_SIZE (1500) //1500 bytes max

#define FEC_K (6)
#define FEC_H (3)

//Finite field (GF(256)) multiplication (so we don't have to define it everywhere)
#define FIELD_SIZE (256U)

//Must be called before multiplying
void generate_field_tables (void);

unsigned char mult(unsigned char a, unsigned char b);