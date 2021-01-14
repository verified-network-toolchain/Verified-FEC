#include <stddef.h>

unsigned sumarray(unsigned *a, int n) {
  unsigned *curr = a;
  unsigned *end = a + n;
  unsigned s = 0;
  while(curr < end) {
    s += *curr;
    curr++;
  }
  return s;
}