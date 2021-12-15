#include "batch_common.h"

//Constant slice size - this can change but is fixed once program begins
//For simplicity, right now it is divisible by MAX_BATCH_SIZE
#define SLICE_SIZE (250)

//NOTE: need this value to be small enough to fix in memory on FPGA
#define SLICES (SLICE_SIZE * BATCHES)