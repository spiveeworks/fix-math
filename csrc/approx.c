#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>

/* TODO use uint64 and int64 and word64 and so on? */
typedef uint32_t u32;
typedef uint64_t u64;
typedef int64_t s64;

const u32 HALFMAX32 = (u32)1 << 31;
const u64 SQRTMAX64 = (u64)1 << 32;
const u64 LO = ((u64)1 << 32) - 1;
// this is never used since rshift destroys low bits
// const u64 HI = LO << 32;

#ifdef _WIN32
#define alloca _alloca
#endif

//////////////////////////////
// uinf

// little-endian dynamically sized unsigned integer
typedef struct {
    u64 size;
    u32 *data;
} uinf;

#define UINF_STATIC(NAME, SIZE) \
u32 NAME##_data[SIZE];\
uinf NAME = {SIZE, NAME##_data};

/* We set this to malloc because alloca seems to behave weird on Windows? The
   debugger gets very confused, and sometimes the behaviour of the program
   seems to agree? TODO: Switch to our own stack allocator, to handle
   freeing. */
uinf uinf_alloc(u64 size) {
    return (uinf){size, malloc(size * sizeof(u32))};
}

void uinf_zero(uinf out) {
    for (u64 i = 0; i < out.size; i++) {
        out.data[i] = 0;
    }
}

void uinf_negative_one(uinf out) {
    for (u64 i = 0; i < out.size; i++) {
        out.data[i] = ~0;
    }
}

void uinf_assign64_high(uinf out, u64 x) {
    uinf_zero(out);
    out.data[out.size - 1] = x >> 32;
    if (out.size > 1) out.data[out.size - 2] = x & LO;
}

u64 uinf_read64_high(uinf x) {
    u64 hi = x.data[x.size-1];
    u64 lo = x.size > 1 ? x.data[x.size-2] : 0;
    return (hi << 32) | lo;
}

void uinf_assign64_low(uinf out, u64 x) {
    uinf_zero(out);
    out.data[0] = x & LO;
    if (out.size > 1) out.data[1] = x >> 32;
}

u64 uinf_read64_low(uinf x) {
    u64 hi = x.size > 1 ? x.data[1] : 0;
    u64 lo = x.data[0];
    return (hi << 32) | lo;
}

void uinf_halfmax(uinf out) {
    uinf_zero(out);
    out.data[out.size - 1] = HALFMAX32;
}

// @Cleanup actually use these instead of putting for loops everywhere?
// @Performance don't do that?
void uinf_write_high(uinf out, uinf in) {
    u64 offset = out.size - in.size;
    for (u64 i = 0; i < in.size && i < out.size; i++) {
        out.data[i + offset] = in.data[i];
    }
}

void uinf_write_low(uinf out, uinf in) {
    for (u64 i = 0; i < in.size && i < out.size; i++) {
        out.data[i] = in.data[i];
    }
}

void uinf_write_signed(uinf out, uinf in) {
    if (in.data[in.size - 1] & HALFMAX32) {
        uinf_negative_one(out);
    } else {
        uinf_zero(out);
    }
    uinf_write_low(out, in);
}

// perfectly safe to set any of these equal,
// just don't overlap end of x/y with start of out
// returns the final overflow if desired
bool uinf_add(uinf out, uinf x, uinf y) {
    u64 carry = 0;
    for (u64 i = 0; i < out.size; i++) {
        if (i < x.size) {
            carry += x.data[i];
        }
        if (i < y.size) {
            carry += y.data[i];
        }
        out.data[i] = carry & LO; // the mask might be implicit from downcast
        carry >>= 32;
        /* TODO: after we finish both inputs, check if carry is 0 and break? */
    }
    return carry;
}

bool uinf_inc(uinf out) {
    /* TODO: Break this up into simpler logic, like uinf_negate? */
    u64 carry = 1;
    for (u64 i = 0; i < out.size; i++) {
        carry += out.data[i];
        out.data[i] = carry & LO; // the mask might be implicit from downcast
        carry >>= 32;
    }
    return carry;
}

// two's complement
// equivalent to uinf_sub(x, {0, 0}, x);
void uinf_negate(uinf x) {
    u64 i = 0;
    /* First skip all the zeros, which negate to 0. */
    while (i < x.size && !x.data[i]) i++;
    /* Then negate one element using two's complement. */
    if (i < x.size) {
        x.data[i] = ~x.data[i] + 1;
        i++;
    }
    /* Then the +1 of two's complement has been done, so we can just continue
       with one's complement for the higher ints. */
    while (i < x.size) {
        x.data[i] = ~x.data[i];
        i++;
    }
}

void uinf_sub(uinf out, uinf x, uinf y) {
    // x - y = x + (-y) = x + ~y + 1
    u64 carry = 1;
    for (u64 i = 0; i < out.size; i++) {
        if (i < x.size) {
            carry += x.data[i];
        }
        if (i < y.size) {
            carry += ~y.data[i];
        } else {
            carry += 0xFFFFFFFF;
        }
        x.data[i] = carry & LO; // the mask might be implicit from downcast
        carry >>= 32;
    }
}

// out += x * y
// typically want to initialize out to 0
// x and y can be the same, out must be completely separate
// returns final overflow, which may itself have overflowed if out is very
// small
u32 uinf_mul(uinf out, uinf x, uinf y) {
    u32 carry = 0;
    for (u64 offset = 0; offset < out.size; offset++) {
        /* As we calculate more and more, we figure out what certain ints will
           be, starting with the least significant int, and moving up. Create a
           uinf without these finished ints included, so that we can add new
           values directly to the more significant ints. */
        uinf out_slice = out;
        out_slice.size -= offset;
        out_slice.data += offset;

        /* Find all pairs i, j that add up to offset, and multiply them. */
        u64 xwidth = offset < x.size - 1 ? offset : x.size - 1;
        u64 ywidth = offset < y.size - 1 ? offset : y.size - 1;
        for (u64 i = offset - ywidth; i <= xwidth; i++) {
            u64 j = offset - i;

            /* Full multiply, then uinf add. */
            u64 prod_long = (u64)x.data[i] * (u64)y.data[j];
            u32 prod_data[2] = {prod_long & LO, prod_long >> 32};
            uinf prod = {2, prod_data};
            carry += uinf_add(out_slice, out_slice, prod);
        }
    }
    return carry;
}

// out -= x * y
void uinf_mul_sub(uinf out, uinf x, uinf y) {
    for (u64 offset = 0; offset < out.size; offset++) {
        uinf out_slice = out;
        out_slice.size -= offset;
        out_slice.data += offset;

        /* Same looping structure as mul with add. */
        u64 xwidth = offset < x.size - 1 ? offset : x.size - 1;
        u64 ywidth = offset < y.size - 1 ? offset : y.size - 1;
        for (u64 i = offset - ywidth; i <= xwidth; i++) {
            u64 j = offset - i;

            /* Full multiply, as before. */
            u64 prod_long = (u64)x.data[i] * (u64)y.data[j];
            u32 prod_data[2] = {prod_long & LO, prod_long >> 32};
            uinf prod = {2, prod_data};
            /* TODO: collect borrow and return? */
            uinf_sub(out_slice, out_slice, prod);
        }
    }
}

bool uinf_eq_zero(uinf x) {
    for (u64 i = 0; i < x.size; i++) {
        if (x.data[i] != 0) {
            return false;
        }
    }
    return true;
}

signed uinf_cmp(uinf x, uinf y) {
    u64 i = x.size < y.size ? y.size : x.size;
    while (i > 0) {
        i--;
        u32 xi = i < x.size ? x.data[i] : 0;
        u32 yi = i < y.size ? y.data[i] : 0;
        if (xi != yi) return xi < yi ? -1 : +1;
    }
    return 0;
}

signed uinf_cmp_signed(uinf x, uinf y) {
    bool x_positive = !(x.data[x.size - 1] & HALFMAX32);
    bool y_positive = !(y.data[y.size - 1] & HALFMAX32);
    if (x_positive == y_positive) {
        // same sign, compare as unsigned integers
        return uinf_cmp(x, y);
    }
    // different sign, whichever is positive is larger
    return x_positive ? +1 : -1;
}

void uinf_rshift(uinf x, u64 shift) {
    u64 shift_hi = shift / 32;
    shift %= 32;
    const u32 mask = (1 << shift) - 1;
    u32 prev_carry = 0;
    u64 i = x.size;
    while (i > 0) {
        i--;
        u32 carry = x.data[i] & mask;
        x.data[i] >>= shift;
        x.data[i] |= prev_carry << (32 - shift);
        prev_carry = carry;
    }
    if (shift_hi == 0) {
        return;
    }
    for (u64 j = 0; j < x.size; j++) {
        if (j < x.size - shift_hi) {
            x.data[j] = x.data[j + shift_hi];
        } else {
            x.data[j] = 0;
        }
    }
}

void uinf_rshift_signed(uinf x, u64 shift) {
    bool neg = x.data[x.size - 1] & HALFMAX32;
    if (neg) {
        uinf_negate(x);
    }
    uinf_rshift(x, shift);
    if (neg) {
        uinf_negate(x);
    }
}

void uinf_lshift(uinf x, u64 shift) {
    u64 shift_hi = shift / 32;
    shift %= 32;
    if (shift) {
        u32 prev_carry = 0;
        for (u64 i = 0; i < x.size; i++) {
            u32 carry = x.data[i] >> (32 - shift);
            x.data[i] <<= shift;
            x.data[i] |= prev_carry;
            prev_carry = carry;
        }
    }
    if (shift_hi == 0) {
        return;
    }
    u64 i = x.size;
    while (i > 0) {
        i--;
        if (i >= shift_hi) {
            x.data[i] = x.data[i-shift_hi];
        } else {
            x.data[i] = 0;
        }
    }

}

// out += remainder / divisor
// remainder %= divisor
// like uinf_mul, one typically wants to zero out first.
void uinf_div(uinf out, uinf remainder, uinf divisor) {
    uinf quotient_piece = uinf_alloc(3);

    while (divisor.size > 1 && divisor.data[divisor.size - 1] == 0) {
        divisor.size -= 1;
    }
    u64 divisor_approx = divisor.data[divisor.size - 1];
    int shift = 0;
    while (divisor_approx < 0x80000000) {
        shift += 1;
        divisor_approx <<= 1;
    }

    // TODO: maybe we can branch into a faster scalar divide algorithm, if
    // there are only 32 bits to worry about? We still get a significant speed
    // benefit when divisor_approx is exact, though!
    if (divisor.size >= 2) {
        u32 next = divisor.data[divisor.size - 2];
        u32 next_shift = 32U - shift;
        divisor_approx |= next >> next_shift;
        u32 mask = (1U << next_shift) - 1U;
        if ((next & mask) != 0) {
            divisor_approx += 1;
        } else {
            for (int i = 0; i < divisor.size - 2; i++) {
                if (divisor.data[i] != 0) {
                    // Round up, to be conservative.
                    divisor_approx += 1;
                    break;
                }
            }
        }
    }

    while (1) {
        while (remainder.size > 0 && remainder.data[remainder.size - 1] == 0) {
            remainder.size -= 1;
        }
        if (remainder.size < divisor.size) {
            return;
        }

        u64 remainder_approx = uinf_read64_high(remainder);
        s64 offset; // number of whole ints the divisor is being shifted
        if (remainder.size == divisor.size) {
            // Shift remainder back 32, forward shift, to match divisor_approx.
            remainder_approx >>= 32U - shift;
            // No whole valued shift.
            offset = 0;
        } else {
            // Remainder is bigger than divisor by some arbitrary amount, so
            // shift divisor until it is just one int behind.
            offset = remainder.size - divisor.size - 1;
        }
        // Do an approximate division, to get an idea of how much to subtract.
        // At the end of the day long division is still just repeated
        // subtraction.
        u64 q = remainder_approx / divisor_approx;
        // subtract `q * divisor` from out, implementing `offset` by skipping
        // the low ints of `out` entirely.
        uinf out_slice = out;
        uinf rem_slice = remainder;
        if (q > 0) {
            out_slice.size -= offset;
            out_slice.data += offset;
            rem_slice.size -= offset;
            rem_slice.data += offset;
            uinf_assign64_low(quotient_piece, q);
            if (remainder.size != divisor.size) {
                // If we shifted divisor, but not remainder, then we should
                // shift the quotient as well, since we have found many
                // multiples of the divisor, not just one.
                uinf_lshift(quotient_piece, shift);
            }
            uinf_mul_sub(rem_slice, quotient_piece, divisor);
            uinf_add(out_slice, out_slice, quotient_piece);
        } else if (remainder.size == divisor.size) {
            // The remainder and divisor can agree on their 32 most significant
            // bits, while still being different at lower order bits. We do a
            // single comparison and subtraction if this is the case, after
            // which remainder should be less than 4 billionths of the size of
            // divisor.
            if (uinf_cmp(remainder, divisor) >= 0) {
                uinf_sub(remainder, remainder, divisor);
                uinf_inc(out);
            }
            return;
        } else {
            fprintf(stderr, "Error: Predicted q = 0 during long division? "
                "File %s, line %d.\n", __FILE__, __LINE__);
            exit(1);
        }
    }
}

// could make a finf type?
void uinf_mul_rshift_signed(uinf out, uinf x, u64 x_exp) {
    bool outsign = false;
    bool xsign = false;
    if (out.data[out.size-1] & HALFMAX32) {
        outsign = true;
        uinf_negate(out);
    }
    if (x.data[x.size-1] & HALFMAX32) {
        xsign = true;
        uinf_negate(x);
    }
    uinf temp = uinf_alloc(out.size + x.size);
    uinf_zero(temp);
    uinf_mul(temp, out, x);
    uinf_rshift(temp, x_exp);
    uinf_write_low(out, temp);
    if (xsign) {
        uinf_negate(x);
    }
    if (outsign != xsign) {
        uinf_negate(out);
    }
}

//////////////////////////////
// cartesian rotation counter

// complex number in a unit square with a number to keep track of winding
typedef struct {
    uinf quarter_turns;
    uinf x;
    uinf y;
} Rotation;

Rotation rot_alloc(int size) {
    return (Rotation){uinf_alloc(size), uinf_alloc(size), uinf_alloc(size)};
}

/*
void rot_debug(Rotation z1) {
    printf("%016llx *", z1.quarter_turns);
    for (u64 i = 0; i < z1.x.size; i++) {
        printf(" %08x", z1.x.data[z1.x.size - i - 1]);
    }
    printf(",");
    for (u64 i = 0; i < z1.y.size; i++) {
        printf(" %08x", z1.y.data[z1.y.size - i - 1]);
    }
}
*/

// out += z1 * z2
// result will have magnitude adjusted to stop it running to 0/infinity
void rot_mul(Rotation *out, Rotation z1, Rotation z2) {
    // i^n1*(x1 + i*y1) * i^n2*(x2 + i*y2)
    // = i^(n1+n2)*(x1*x2 - y1*y2 + i*(x1*y2 + x2*y1))
    uinf_add(out->quarter_turns, out->quarter_turns, z1.quarter_turns);
    uinf_add(out->quarter_turns, out->quarter_turns, z2.quarter_turns);

    bool carry = false;
    carry = carry || uinf_mul(out->y, z1.x, z1.y);
    carry = carry || uinf_mul(out->y, z1.y, z1.x);

    uinf_mul(out->x, z1.x, z2.x);
    uinf_negate(out->x);
    bool rotate = uinf_mul(out->x, z1.y, z2.y);
    // at this point we have y1*y2 - (out->x + x1*x2)
    // the subend was negative so no overflow means it is still negative

    if (!rotate) {
        uinf_negate(out->x);
    }

    if (carry) {
        uinf_rshift(out->x, 1);
        uinf_rshift(out->y, 1);
        out->y.data[out->y.size - 1] |= HALFMAX32;
    }

    if (rotate) {
        uinf x = out->x;
        out->x = out->y;
        out->y = x;
        uinf_inc(out->quarter_turns);
    }

    while (!(
        (out->x.data[out->x.size - 1] & HALFMAX32) ||
        (out->y.data[out->y.size - 1] & HALFMAX32)
    )) {
        uinf_lshift(out->x, 1);
        uinf_lshift(out->y, 1);
    }
}

//////////////////////////////
// reference functions

// x = arctan(y)
// modifies x and y
// assumes x is initially 0
void arctan(uinf x, uinf y) {
    //   2^n * arctan(y)
    // = 2^n * arg(1 + iy)
    // = 4 * arg((1 + iy)^(2^(n-2)))
    // = quarter turns of (1 + iy)^(2^(n-2))
    const u64 n = y.size * 32;
    uinf z_x = uinf_alloc(y.size);
    Rotation z = {x, z_x, y};
    uinf_halfmax(z.x);
    uinf_rshift(y, 1);
    Rotation out = rot_alloc(2*y.size);
    for (u64 i = 0; i < n-2; i++) {
        uinf_zero(out.quarter_turns);
        uinf_zero(out.x);
        uinf_zero(out.y);
        rot_mul(&out, z, z);
        for (u64 j = 0; j < z.x.size; j++) {
            z.quarter_turns.data[j] = out.quarter_turns.data[j];
            z.x.data[j] = out.x.data[j + y.size];
            z.y.data[j] = out.y.data[j + y.size];
        }
    }
}

// x = arcsin(sqrt(s))
// modifies x and s
// assumes x is initially 0
// note arcsin(y) = arcspread(y*y)
void arcspread(uinf x, uinf s) {
    // set s to sin^2(theta), then
    // sin^2(2theta) = 4sin^2(theta)cos^2(theta)
    //               = 4sin^2(theta)(1-sin^2(theta))
    //               = 4s(1-s)
    // and whenever s > 0.5 we can interpret this as
    // sin^2(2(theta + 1/8)) = sin^2(2theta + 1/4)
    //                       = cos^2(2theta)
    //                       = 1 - sin^2(2theta)
    const u64 n = x.size * 32;
    uinf negs = uinf_alloc(s.size);
    uinf out = uinf_alloc(2 * s.size);
    bool shift = false;
    for (u64 i = 0; i < n-2; i++) {
        shift = s.data[s.size - 1] & HALFMAX32;
        for (size_t j = 0; j < s.size; j++) {
            negs.data[j] = s.data[j];
        }
        uinf_negate(negs);

        uinf_zero(out);
        uinf_mul(out, s, negs);

        uinf_lshift(x, 1);
        uinf_lshift(out, 2);
        if (shift) {
            uinf_negate(out);
            uinf_inc(x);
        }
        for (size_t j = 0; j < s.size; j++) {
            s.data[j] = out.data[j + s.size];
            negs.data[j] = out.data[j + s.size];
        }
    }
}

// modifies x but not y
// assumes x is initially 0
void arcsin(uinf x, uinf y) {
    uinf out = uinf_alloc(2 * y.size);
    uinf_zero(out);
    uinf_mul(out, y, y);
    uinf s = {y.size + 1, out.data + y.size - 1};
    arcspread(x, s);
}

// modifies x but not y
// assumes x is initially 0
void arccos(uinf x, uinf y) {
    uinf out = uinf_alloc(2 * y.size);
    uinf_zero(out);
    uinf_mul(out, y, y);
    uinf s = {y.size + 1, out.data + y.size - 1};
    uinf_negate(s);
    arcspread(x, s);
}

/*
void arccos_signed(uinf x, uinf y) {
    bool neg = y.data[y.size - 1] & HALFMAX32;
    uinf_lshift(y, 1);
    arccos(x, y);
    if (neg) {
        uinf_negate(x);
        x.data[x.size - 1] ^= HALFMAX32;
    }
}
*/

// x = -log_2(y) mod 1
// modifies x and y
// assumes x is initially 0
void neglog2(uinf x, uinf y) {
    if (uinf_eq_zero(y)) {
        /* y is zero, so log2 is undefined, or negative infinity. Infinity
           mod 1 is genuinely undefined, but we could pretend that y is just a
           really tiny power of 2, giving an integer as the result of log2,
           which overflows to 0. */
        uinf_zero(x);
        return;
    }
    //   2^64 * log(y)
    // = log(y^(2^64))
    // so calculate (y^(2^64)) as a floating point and discard the mantissa
    const u64 n = y.size * 32;
    uinf out = uinf_alloc(y.size * 2);
    for (u64 i = 0; i < n; i++) {
        bool lows_all_zero = true;
        for (u64 j = 0; (s64)j <= (s64)y.size-2; j++) {
            if (y.data[j] != 0) {
                lows_all_zero = false;
            }
        }
        // this short circuit condition mainly exists so that the result is the
        // floor instead of ceil(x-1)
        if (lows_all_zero && y.data[y.size-1] == HALFMAX32) {
            uinf_inc(x);
            // double y to get 1, which is a fixpoint y = y^2
            // so just finish doubling x and return
            uinf_lshift(x, n - i);
            return;
        }
        uinf_zero(out);
        uinf_mul(out, y, y);
        uinf_lshift(x, 1);
        while (!(out.data[out.size - 1] & HALFMAX32)) {
            uinf_lshift(out, 1);
            uinf_inc(x);
        }
        for (u64 j = 0; j < y.size; j++) {
            y.data[j] = out.data[j + y.size];
        }
    }
}

// x = log_2(1 + y) mod 1
void log2(uinf x, uinf y) {
    neglog2(x, y);
    uinf_negate(x);
}

// x = log_2(1 + y)
void inclog2(uinf x, uinf y) {
    uinf_rshift(y, 1);
    y.data[y.size-1] |= 1U << 31U;
    // 0.5+y/2 is now in the range [0.5, 1),
    // => log(0.5+y/5) in [-1, 0)
    // => -log(0.5+y/5) in (0, 1]
    // so we have x = -log(0.5+y/2), unless y = 0 where x overflows to 0
    neglog2(x, y);
    // negating a fixed point number with no whole part is the same as
    // calculating 1 - x = 1 + log(0.5+y/2) = log(1 + y)
    // if y = 0 then 1 - x overflows again, giving 0 = log(1 + 0)
    // (this derivation is much less magical when you look at the self similar
    // graph of log_2(x))
    uinf_negate(x);
}

/* left in for reference when reading the more generalized uinf bisection
 *
u32 bisect32(u32 (*f)(u32), u32 y, bool increasing) {
    u32 b = 1U << 31;
    u32 x = 0;
    for (u32 b = 1U << 31; b != 0; b >>= 1) {
        if (f(x | b) == y) {
            return x | b;
        }
        bool toolow = f(x | b) < y;
        if (toolow == increasing) {
            x |= b;
        }
    }
    return x;
}
*/

// finds the bottom n bits of x so that f(x) = y.
// Assumes that these bits are initially 0.
void bisect(
    void (*f)(uinf, uinf), uinf x, uinf y,
    u64 n, bool is_signed
) {
    bool increasing;
    {
        uinf xswp = uinf_alloc(x.size);

        uinf yl = uinf_alloc(y.size);
        uinf_zero(yl);
        uinf_zero(xswp);
        xswp.data[xswp.size-1] |= 1U << 30;
        f(yl, xswp);

        uinf yr = uinf_alloc(y.size);
        uinf_zero(yr);
        uinf_zero(xswp);
        xswp.data[xswp.size-1] |= 3U << 30;
        f(yr, xswp);

        signed cmp = is_signed ? uinf_cmp_signed(yl, yr) : uinf_cmp(yl, yr);
        increasing = cmp <= 0;
    }
    uinf yc = uinf_alloc(y.size);
    uinf newx = uinf_alloc(x.size);
    for (s64 i = x.size-1; i >= 0; i--) {
        for (int j = 31; j >= 0; j--) {
            if (i * 32 + j >= n) { continue; }
            uinf_write_low(newx, x);
            newx.data[i] |= 1U << (u32)j;
            uinf_zero(yc);
            f(yc, newx);
            signed cmp = is_signed ? uinf_cmp_signed(yc, y) : uinf_cmp(yc, y);
            if (cmp == 0) {
                x.data[i] |= 1U << (u32)j;
                return;
            }
            if ((cmp < 0) == increasing) {
                x.data[i] |= 1U << (u32)j;
            }
        }
    }
}

//////////////////////////////
// polynomial

typedef struct {
    u64 terms;
    u64 exp;
    u64 size;
    u32 *data;
} poly;

#define POLY_STATIC(name, terms, exp, size) \
u32 name##_data[(terms) * (size)];\
poly name = {terms, exp, size, name##_data};

uinf poly_index(poly p, u64 i) {
    return (uinf){p.size, &p.data[p.size * i]};
}

void poly_zero(poly p) {
    for (u64 i = 0; i < p.terms; i++) {
        uinf_zero(poly_index(p, i));
    }
}

void poly_diff(poly p) {
    for (u32 i = 1; i < p.terms; i++) {
        uinf c = poly_index(p, i-1);
        uinf n = {1, &i};
        uinf k = poly_index(p, i);
        uinf_zero(c);
        uinf_mul(c, k, n);
    }
    uinf_zero(poly_index(p, p.terms - 1));
}

void poly_eval(uinf out, poly p, uinf x, u64 x_exp, u64 out_exp) {
    uinf_zero(out);
    uinf swap = uinf_alloc(p.size + out.size);
    for (s64 i = 0; i < p.terms; i++) {
        // out *= x
        uinf_mul_rshift_signed(out, x, x_exp);

        // out += c
        uinf_zero(swap);
        uinf c = poly_index(p, p.terms - i - 1);
        uinf_write_signed(swap, c);
        uinf_lshift(swap, out_exp);
        uinf_rshift_signed(swap, p.exp);
        uinf_add(out, out, swap);
    }
}

//////////////////////////////
// constants

// near 0 we have x ~= sin(x) ~= tan(x)
// in radians we have implemented arctan(x)/2pi
// so set x to 2^-n and calculate
// arctan(x)/2pi = x/2pi = 2^-n/2pi
// and return the low bits of this
void reciprocol_twopi(uinf out) {
    uinf x = uinf_alloc(out.size * 2);
    uinf_zero(x);
    uinf y = uinf_alloc(out.size * 2);
    uinf_zero(y);
    y.data[out.size] = 1;
    arctan(x, y);
    for (size_t i = 0; i < out.size; i++) {
        out.data[i] = x.data[i];
    }
}

// dlog_2(x)/dx = 1/ln(2) * dln(x)/dx = 1/ln(2) * 1/x
// at x = 1 this is 1/ln(2)
// now use dlog_2(x)/dx = (log_2(x+h)-log_2(x))/h
// giving 1/ln(2) = log_2(1+h)/h
// very similar to the 1/2pi formula!
// set h to 2^-n and take the low bits as before
//
// note 1/ln(2) is greater than 1 so the the top word of out is just 1
void reciprocol_ln2(uinf out) {
    uinf x = uinf_alloc(out.size * 2 - 1);
    uinf_zero(x);
    uinf y = uinf_alloc(out.size * 2 - 1);
    uinf_zero(y);
    y.data[out.size-1] = 1;
    inclog2(x, y);
    for (size_t i = 0; i < out.size; i++) {
        out.data[i] = x.data[i];
    }
}

///////////
// Render

#define IMAGE_WIDTH 512ULL
#define IMAGE_HEIGHT 512ULL

void render(char *name,
    void (*f)(uinf,uinf), bool invert, poly p,
    u64 yscale, u64 xscale
) {
    static u64 ys[IMAGE_WIDTH];
    static u64 poly_ys[IMAGE_WIDTH];
    static s64 dys[IMAGE_WIDTH];

    for (size_t i = 0; i < IMAGE_WIDTH; i++) {
        u32 x32 = i * xscale / (IMAGE_WIDTH-1) + 1;

        {
            uinf x = uinf_alloc(2);
            uinf_assign64_low(x, x32);
            uinf y = uinf_alloc(2);
            poly_eval(y, p, x, 32, 32);
            poly_ys[i] = uinf_read64_low(y);
        }

        {
            uinf x = {1, &x32};
            u32 actual = 0;
            uinf y = {1, &actual};
            if (invert) bisect(f, y, x, 32, false);
            else f(y, x);
            ys[i] = (s64)actual;
            dys[i] = (s64)poly_ys[i] - (s64)actual;
        }
    }

    FILE *out = fopen(name, "wb");
    const u64 bright = 255;
    fprintf(out, "P6 %llu %llu %llu ", IMAGE_WIDTH, IMAGE_HEIGHT, bright);
    for (size_t j = 0; j < IMAGE_HEIGHT; j++) {
        for (size_t i = 0; i < IMAGE_WIDTH; i++) {
            u64 y = IMAGE_HEIGHT-1 - j;
            u64 poly_y = poly_ys[i] * (IMAGE_HEIGHT - 1) / yscale;
            int cyan = 0;
            if (y < poly_y) {
                cyan = bright;
            } else if (y == poly_y) {
                u64 rem = poly_ys[i] * (IMAGE_HEIGHT - 1) % yscale;
                cyan = rem * bright / yscale;
            }
            int red = 0;
            u64 fun_y = ys[i] * (IMAGE_HEIGHT - 1) / yscale;
            if (y < fun_y) {
                red = bright;
            } else if (y == fun_y) {
                u64 rem = ys[i] * (IMAGE_HEIGHT - 1) % yscale;
                red = rem * bright / yscale;
            }

            s64 dy0 = IMAGE_HEIGHT/2 + dys[i]*((s64)IMAGE_HEIGHT - 1)/(s64)yscale;
            int green = cyan;
            int blue = cyan;
            bool incident = y == dy0;

            fputc(red, out);
            fputc(green, out);
            fputc(blue, out);
        }
    }
    fclose(out);
}

#define MODEL_SIZE 2
#define MODEL_TERMS 3
#define MODEL_EXP 32

POLY_STATIC(model, MODEL_TERMS, MODEL_EXP, MODEL_SIZE);
POLY_STATIC(dmodel, MODEL_TERMS, MODEL_EXP, MODEL_SIZE);

void model_initialize(u64 a, u64 b, u64 c) {
    uinf_assign64_low(poly_index(model, 0), c);
    uinf_assign64_low(poly_index(model, 1), b);
    uinf_assign64_low(poly_index(model, 2), a);

    uinf_assign64_low(poly_index(dmodel, 0), c);
    uinf_assign64_low(poly_index(dmodel, 1), b);
    uinf_assign64_low(poly_index(dmodel, 2), a);
    poly_diff(dmodel);
}

// TODO: Make this take an integer representing the size of the fractional
// part, and print both sides as a full decimal.
void print_frac_part(uinf x) {
    u32 ten_val = 10;
    uinf ten = {1, &ten_val};

    uinf out = uinf_alloc(x.size + 1);
    uinf remainder = uinf_alloc(x.size);
    uinf_write_high(remainder, x);

    if (remainder.size == 0) {
        putc('0', stdout);
        return;
    }
    /* 2^320 is about 2e96, but we don't trust the bottom few bits anyway, so
       just print 95 digits for every 10 ints. */
    u32 digits = remainder.size * 95 / 10;
    for (int i = 0; i < digits; i++) {
        uinf_zero(out);
        uinf_mul(out, remainder, ten);
        putc('0' + out.data[out.size - 1], stdout);
        bool all_zero = true;
        for (int i = 0; i < remainder.size; i++) {
            u32 val = out.data[i];
            if (val != 0) all_zero = false;
            remainder.data[i] = val;
        }
        if (all_zero) return;
    }
}

void print_constants(void) {
    {
        uinf c = uinf_alloc(3);
        int c_whole_part = 1;
        int c_frac_part = c.size - c_whole_part;
        uinf_zero(c);
        c.data[c.size - c_whole_part] = 4;
        printf("c = %d\n", c.data[c.size - c_whole_part]);

        int d_whole_part = 1;
        int d_frac_part = 1;
        uinf d = uinf_alloc(d_whole_part + d_frac_part);
        uinf_zero(d);
        d.data[d_frac_part - 1] = 4;
        d.data[d.size - d_whole_part] = 0;
        if (d_whole_part > 0) {
            printf("d = %d.", d.data[d.size - d_whole_part]);
            uinf d_frac = {d_frac_part, d.data};
            print_frac_part(d_frac);
        } else {
            printf("d = 0.");
            print_frac_part(d);
        }
        printf("\n");

        uinf q = uinf_alloc(c.size);
        int q_frac_part = c_frac_part - d_frac_part;
        int q_whole_part = q.size - q_frac_part;
        uinf_zero(q);
        uinf_div(q, c, d);
        printf("q = {");
        for (int i = q.size - 1; i >= 0; i--) {
            printf("0x%08X", q.data[i]);
            if (i > 0) {
                printf(", ");
            }
        }
        printf("}\n");
        printf("c = %lld.", (u64)q.data[q.size - q_whole_part + 1] << 32
            | q.data[q.size - q_whole_part]);
        uinf q_frac = {q_frac_part, q.data};
        print_frac_part(q_frac);
        printf(" * d + %d.", c.data[c.size - c_whole_part]);
        uinf c_frac = {c_frac_part, c.data};
        print_frac_part(c_frac);
        printf("\n");

        uinf_mul(c, q, d);
        printf("c = %d.", c.data[c.size - c_whole_part]);
        print_frac_part(c_frac);
        printf("\n");
    }

    printf("\n");

    /* 11 ints gives about 104 digits of good decimal expansion. */
    uinf r2pi = uinf_alloc(11);
    printf("1/2pi = 0.");
    reciprocol_twopi(r2pi);
    print_frac_part(r2pi);
    printf("\n");

    uinf pi = uinf_alloc(r2pi.size + 1);
    uinf remainder = uinf_alloc(2 * r2pi.size);
    uinf_zero(pi);
    uinf_zero(remainder);
    remainder.data[remainder.size - 1] = HALFMAX32;
    printf("pi = ");
    // (1/2) / (1/2pi) = 1/2 * 2pi = pi
    uinf_div(pi, remainder, r2pi);
    // TODO: Make a mixed fraction printing algorithm.
    printf("%d.", pi.data[pi.size - 1]);
    pi.size -= 1;
    print_frac_part(pi);
    printf("\n");
}

void render_all(void) {
    model_initialize(1ULL<<31ULL, 1ULL<<31ULL, 0);
    render("powb.ppm",
            inclog2, true, model,
            SQRTMAX64, SQRTMAX64-2);
    model_initialize(~0ULL<<36ULL,1ULL<<35ULL,0);
    render("sin.ppm",
            arcsin, true, model,
            SQRTMAX64, SQRTMAX64/4);
    model_initialize((~0ULL<<36ULL),0,(1ULL<<32ULL)-1);
    render("cos.ppm",
            arccos, true, model,
            SQRTMAX64, SQRTMAX64/4);
    model_initialize(1ULL<<36, 3ULL<<33ULL, 0);
    render("tan.ppm",
            arctan, true, model,
            SQRTMAX64, SQRTMAX64/8);
}

int main() {
    print_constants();
    render_all();
}

