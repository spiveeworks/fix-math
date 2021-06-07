#include <stdio.h>

#include "fix_fs.h"

void check_invsqrt_nr(u64 x, u64 order) {
    u64 y = invsqrt_nr(x, order);
    float in = (float)x/(float)(1 << order), out = (float)y/(float)(1<<order);
    printf("prod = %f\n", in * out * out);
    u64 y2 = invsqrt_nr_rr(x, order);
    float out2 = (float)y2/(float)(1<<order);
    printf("prod_rr = %f\n", in * out2 * out2);
}

int main() {
    printf("ilb(0) = %ld\n", ilb64(0));
    printf("ilb(-1) = %ld\n", ilb64(-1));
    check_invsqrt_nr(1000, 16);
    check_invsqrt_nr(10000, 16);
    check_invsqrt_nr(65000, 15);
    check_invsqrt_nr(55000, 15);
    check_invsqrt_nr(100000, 16);
    check_invsqrt_nr(1000000, 16);
}
