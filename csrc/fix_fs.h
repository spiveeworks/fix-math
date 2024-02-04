#ifndef FIX_INCLUDE_FIX_FS_H
#define FIX_INCLUDE_FIX_FS_H
#include "adm_types.h"

s64 ilb64(s64 x) {
    __asm__("bsrl %0, %1" : "=r"(x) : "r"(x));
    return x;
}

u64 invsqrt_nr(u64 x, u64 order) {
    /* For Newton-Raphson on the decreasing curve x^(-0.5), we use the standard
       initial guess of 2^(-log_2(x)/2), which is exact for whole powers of
       four. We approximate log_2 using the reverse bit-scan operation, but
       have to be careful not to round down during division, so that 2.0 has an
       initial guess of 0.5 rather than 1.0, for example. In fact, we want
       numbers as low as 1.75 to map to 0.5, so we use two integer additions to
       multiply by 1.1875 before performing the bit-scan. */
    s64 ilb = ilb64(x + (x >> 3) + (x >> 4)) - order;

    /* round off rather than rounding down */
    u64 y = 1 << (order - ((ilb + 1) >> 1));

    y = y * ((3 << order) - ((x * y >> order) * y >> order)) >> (order + 1);
    y = y * ((3 << order) - ((x * y >> order) * y >> order)) >> (order + 1);
    y = y * ((3 << order) - ((x * y >> order) * y >> order)) >> (order + 1);
    return y;
}

u64 invsqrt_nr_rr(u64 x, u64 order) {
    /* reduce range to [0.5, 2.0) and then do NR as normal*/
    s64 ilb = ilb64(x) + 1 - order;
    s64 ilb_even = (u64)ilb & ~1UL;
    u64 is_neg = (u64)ilb >> 63UL;
    /* 0xFFFFFFFF if negative, 0x00000000 if positive */
    u64 neg_mask = -is_neg;

    u64 lshift = neg_mask & (u64)-ilb_even;
    u64 rshift = (~neg_mask) & (u64)ilb_even;

    x <<= lshift;
    x >>= rshift;

    u64 y = (1UL << order);

    y = y * ((3UL << order) - ((x * y >> order) * y >> order)) >> (order + 1);
    y = y * ((3UL << order) - ((x * y >> order) * y >> order)) >> (order + 1);
    y = y * ((3UL << order) - ((x * y >> order) * y >> order)) >> (order + 1);

    /* map y to the interval corresponding to invsqrt(x) */
    y <<= lshift >> 1UL;
    y >>= rshift >> 1UL;

    return y;
}

#endif
