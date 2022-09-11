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

#define UINF_ALLOCA(NAME, SIZE) \
u32 *NAME##_data = alloca(SIZE * sizeof(u32));\
uinf NAME = {SIZE, NAME##_data};

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
    out.data[out.size - 2] = x & LO;
    out.data[out.size - 1] = x >> 32;
}

u64 uinf_read64_high(uinf x) {
    u64 hi = x.data[x.size-1];
    u64 lo = x.data[x.size-2];
    return (hi << 32) | lo;
}

void uinf_assign64_low(uinf out, u64 x) {
    uinf_zero(out);
    out.data[0] = x & LO;
    out.data[1] = x >> 32;
}

u64 uinf_read64_low(uinf x) {
    u64 hi = x.data[1];
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
    }
    return carry;
}

bool uinf_inc(uinf out) {
    u64 carry = 1;
    for (u64 i = 0; i < out.size; i++) {
        carry += out.data[i];
        out.data[i] = carry & LO; // the mask might be implicit from downcast
        carry >>= 32;
    }
    return carry;
}

// out += x * y
// typically want to initialize out to 0
// x and y can be the same, out must be completely separate
// returns final overflow, which may itself have overflowed if out is very
// small
u32 uinf_mul(uinf out, uinf x, uinf y) {
    u32 carry = 0;
    for (u64 offset = 0; offset < out.size; offset++) {
        uinf out_slice = out;
        out_slice.size -= offset;
        out_slice.data += offset;
        u64 xwidth = offset < x.size - 1 ? offset : x.size - 1;
        u64 ywidth = offset < y.size - 1 ? offset : y.size - 1;
        for (u64 i = offset - ywidth; i <= xwidth; i++) {
            u64 j = offset - i;
            
            u64 prod_long = (u64)x.data[i] * (u64)y.data[j];
            u32 prod_data[2] = {prod_long & LO, prod_long >> 32};
            uinf prod = {2, prod_data};
            carry += uinf_add(out_slice, out_slice, prod);
        }
    }
    return carry;
}

// twos complement
// equivalent to uinf_sub(x, {0, 0}, x);
void uinf_negate(uinf x) {
    u64 i = 0;
    while (i < x.size && !x.data[i]) i++;
    if (i < x.size) {
        x.data[i] = ~x.data[i] + 1;
        i++;
    }
    while (i < x.size) {
        x.data[i] = ~x.data[i];
        i++;
    }
}

void uinf_sub(uinf out, uinf x, uinf y) {
    u64 carry = 1;
    for (u64 i = 0; i < out.size; i++) {
        if (i < x.size) {
            carry += x.data[i];
        }
        if (i < y.size) {
            carry += ~y.data[i];
        }
        x.data[i] = carry & LO; // the mask might be implicit from downcast
        carry >>= 32;
    }
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
    UINF_ALLOCA(temp, out.size + x.size);
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

#define ROT_ALLOCA(name, size) \
UINF_ALLOCA(name##_qt, size);\
UINF_ALLOCA(name##_x, size);\
UINF_ALLOCA(name##_y, size);\
Rotation name = {name##_qt, name##_x, name##_y};

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
    UINF_ALLOCA(z_x, y.size);
    Rotation z = {x, z_x, y};
    uinf_halfmax(z.x);
    uinf_rshift(y, 1);
    ROT_ALLOCA(out, 2*y.size);
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
    UINF_ALLOCA(negs, s.size);
    UINF_ALLOCA(out, 2 * s.size);
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
    UINF_ALLOCA(out, 2 * y.size);
    uinf_zero(out);
    uinf_mul(out, y, y);
    uinf s = {y.size + 1, out.data + y.size - 1};
    arcspread(x, s);
}

// modifies x but not y
// assumes x is initially 0
void arccos(uinf x, uinf y) {
    UINF_ALLOCA(out, 2 * y.size);
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
    bool y_zero = true;
    for (u64 j = 0; j < y.size; j++) {
        if (y.data[j] != 0) {
            y_zero = false;
        }
    }
    if (y_zero) {
        /* y is zero, so log2 is undefined, or negative infinity. Infinity
           mod 1 is genuinely undefined, but we could pretend that y is just a
           really tiny power of 2, giving an integer as the result of log2,
           which overflows to 0. */
        for (u64 j = 0; j < x.size; j++) {
            x.data[j] = 0;
        }
        return;
    }
    //   2^64 * log(y)
    // = log(y^(2^64))
    // so calculate (y^(2^64)) as a floating point and discard the mantissa
    const u64 n = y.size * 32;
    UINF_ALLOCA(out, y.size * 2);
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
        for (u64 j = 0; j < out.size; j++) {
            out.data[j] = 0;
        }
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
        UINF_ALLOCA(xswp, x.size)

        UINF_ALLOCA(yl, y.size)
        uinf_zero(yl);
        uinf_write_low(xswp, x);
        f(yl, xswp);

        UINF_ALLOCA(yr, y.size)
        uinf_zero(yr);
        uinf_write_low(xswp, x);
        f(yr, xswp);

        signed cmp = is_signed ? uinf_cmp_signed(yl, yr) : uinf_cmp(yl, yr);
        increasing = cmp <= 0;
    }
    UINF_ALLOCA(yc, y.size)
    UINF_ALLOCA(newx, x.size)
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
    UINF_ALLOCA(swap, p.size + out.size);
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

// near 0 we have x ~= sin(x) ~= tan(x)
// in radians we have implemented arctan(x)/2pi
// so set x to 2^-n and calculate
// arctan(x)/2pi = x/2pi = 2^-n/2pi
// and return the low bits of this
void reciprocol_twopi(uinf out) {
    UINF_ALLOCA(x, out.size * 2);
    uinf_zero(x);
    UINF_ALLOCA(y, out.size * 2);
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
    UINF_ALLOCA(x, out.size * 2 - 1);
    uinf_zero(x);
    UINF_ALLOCA(y, out.size * 2 - 1);
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
    void (*finv)(uinf,uinf), poly p,
    u64 yscale, u64 xscale
) {
    static u64 xs[IMAGE_HEIGHT];
    for (size_t j = 0; j < IMAGE_HEIGHT; j++) {
        u32 y = (IMAGE_HEIGHT - 1 - j) * yscale / (IMAGE_HEIGHT-1) + 1;
        u32 x = 0;
        finv((uinf){1, &x}, (uinf){1, &y});
        xs[j] = x;
    }
    bool increasing = xs[3*IMAGE_WIDTH/4] < xs[IMAGE_WIDTH/4];

    static u64 ys[IMAGE_WIDTH];
    static s64 dys[IMAGE_WIDTH];
    for (size_t i = 0; i < IMAGE_WIDTH; i++) {
        u32 x32 = i * xscale / (IMAGE_WIDTH-1) + 1;

        UINF_ALLOCA(x, 2);
        uinf_assign64_low(x, x32);
        UINF_ALLOCA(y, 2);
        poly_eval(y, p, x, 32, 32);
        ys[i] = uinf_read64_low(y);

        u32 actual = 0;
        bisect(finv, (uinf){1, &actual}, (uinf){1, &x32}, 32, false);
        dys[i] = (s64)ys[i] - (s64)actual;
    }

    FILE *out = fopen(name, "wb");
    const u64 bright = 255;
    fprintf(out, "P6 %llu %llu %llu ", IMAGE_WIDTH, IMAGE_HEIGHT, bright);
    for (size_t j = 0; j < IMAGE_HEIGHT; j++) {
        u64 x0 = xs[j] * (IMAGE_WIDTH - 1) / xscale;
        for (size_t i = 0; i < IMAGE_WIDTH; i++) {
            u64 y0 = ys[i] * (IMAGE_HEIGHT - 1) / yscale;
            int cyan = 0;
            if ((IMAGE_HEIGHT-1 - j) < y0) {
                cyan = bright;
            } else if ((IMAGE_HEIGHT-1 - j) == y0) {
                u64 rem = ys[i] * (IMAGE_HEIGHT - 1) % yscale;
                cyan = rem * bright / yscale;
            }
            int red = 0;
            if (i < x0) {
                red = bright;
            } else if (i == x0) {
                u64 rem = xs[j] * (IMAGE_WIDTH - 1) % xscale;
                red = rem * bright / xscale;
            }
            if (increasing) {
                red = bright - red;
            }

            s64 dy0 = IMAGE_HEIGHT/2 + dys[i]*((s64)IMAGE_HEIGHT - 1)/(s64)yscale;
            int green = cyan;
            int blue = cyan;
            bool incident = false;
            if ((IMAGE_HEIGHT-1 - j) == dy0) {
                incident = true;
            }

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

UINF_STATIC(r2pi, 2);

void model_initialize(u64 a, u64 b, u64 c) {
    uinf_assign64_low(poly_index(model, 0), c);
    uinf_assign64_low(poly_index(model, 1), b);
    uinf_assign64_low(poly_index(model, 2), a);

    uinf_assign64_low(poly_index(dmodel, 0), c);
    uinf_assign64_low(poly_index(dmodel, 1), b);
    uinf_assign64_low(poly_index(dmodel, 2), a);
    poly_diff(dmodel);

    reciprocol_twopi(r2pi);
}

int main() {
    model_initialize(1ULL<<31ULL, 1ULL<<31ULL, 0);
    render("powb.ppm",
            inclog2, model,
            SQRTMAX64, SQRTMAX64-2);
    model_initialize(~0ULL<<36ULL,1ULL<<35ULL,0);
    render("sin.ppm",
            arcsin, model,
            SQRTMAX64, SQRTMAX64/4);
    model_initialize((~0ULL<<36ULL),0,(1ULL<<32ULL)-1);
    render("cos.ppm",
            arccos, model,
            SQRTMAX64, SQRTMAX64/4);
    model_initialize(1ULL<<36, 3ULL<<33ULL, 0);
    render("tan.ppm",
            arctan, model,
            SQRTMAX64, SQRTMAX64/8);
}

