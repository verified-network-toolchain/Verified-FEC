#include "batch_common.h"

//Constant slice size - this can change but is fixed once program begins
#define SLICE_SIZE (256)

//NOTE: need this value to be small enough to fix in memory on FPGA
#define SLICES (SLICE_SIZE * BATCHES)