#include <stdio.h>

typedef unsigned u32;
typedef long long unsigned u64;

const u32 HALFMAX32 = (u32)1 << 31;
const u64 SQRTMAX64 = (u64)1 << 32;
const u64 LO = ((u64)1 << 32) - 1;
// this is never used since rshift destroys low bits
// const u64 HI = LO << 32;

typedef enum {
	false,
	true,
} bool;

//////////////////////////////
// uinf

// little-endian dynamically sized unsigned integer
typedef struct {
	u64 size;
	u32 *data;
} uinf;

#define UINF_ALLOCA(name, size) \
u32 name##_data[size];\
uinf name = {size, name##_data};

void uinf_zero(uinf out) {
	for (u64 i = 0; i < out.size; i++) {
		out.data[i] = 0;
	}
}

void uinf_assign64(uinf out, u64 x) {
	uinf_zero(out);
	out.data[out.size - 2] = x & LO;
	out.data[out.size - 1] = x >> 32;
}

u64 uinf_read64(uinf x) {
	u64 hi = x.data[x.size-1];
	u64 lo = x.data[x.size-2];
	return (hi << 32) | lo;
}

void uinf_halfmax(uinf out) {
	uinf_zero(out);
	out.data[out.size - 1] = HALFMAX32;
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

bool uinf_lss(uinf x, uinf y) {
	u64 i = x.size < y.size ? y.size : x.size;
	while (i > 0) {
		i--;
		u32 xi = i < x.size ? x.data[i] : 0;
		u32 yi = i < y.size ? y.data[i] : 0;
		if (xi != yi) return xi < yi;
	}
	return false;
}

void uinf_rshift(uinf x, u64 shift) {
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
}

void uinf_lshift(uinf x, u64 shift) {
	u64 shift_lo = shift % 32;
	u64 shift_hi = shift / 32;
	u32 prev_carry = 0;
	for (u64 i = 0; i < x.size; i++) {
		u32 carry = x.data[i] >> (32 - shift_lo);
		x.data[i] <<= shift_lo;
		x.data[i] |= prev_carry;
		prev_carry = carry;
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

// dedekind cuts represent real numbers as the set of rational numbers smaller
// than them
// so tan(x) as a cut is the set {y : y < tan(x)}
// so our convention is f_cut(x, y) <=> y < f(x)
// such that currying f_cut would actually give a function Rat->Real

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

// x = -log_2(y)-1
// modifies x and y
// assumes x is initially 0
void neglog2(uinf x, uinf y) {
	//   2^64 * log(y)
	// = log(y^(2^64))
	// so calculate (y^(2^64)) as a floating point and discard the mantissa
	const u64 n = y.size * 32;
	UINF_ALLOCA(out, y.size * 2);
	for (u64 i = 0; i < n; i++) {
		// this short circuit condition mainly exists so that the result is the
		// floor instead of ceil(x-1)
		if (y.data[0] == 0 && y.data[1] == HALFMAX32) {
			uinf_inc(x);
			// double y to get 1, which is a fixpoint of _^2
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

/*
bool tan_cut(Unit x, Unit y) {
	// y < tan(x)
	// arctan(y) < x
	return unit_lss(arctan(y), x);
}

Unit bisect(bool (*f_cut)(Unit, Unit), Unit x) {
	Unit y = UNIT_HALF;
	Unit delta = unit_rshift(y, 1);
	while (u64_from_unit(delta)) {
		if (f_cut(x, y)) {
			// increase while below the cut
			y = unit_add(y, delta);
		} else {
			// decrease while above the cut
			y = unit_sub(y, delta);
		}
		delta = unit_rshift(delta, 1);
	}
	return y;
}

Unit tan_bisect(Unit x) {
	return bisect(tan_cut, x);
}
*/

int test() {
#define YS 5
	float ys[YS] = {0.49f, 0.5f, 0.51f, 0.5625f, 0.0078125f};
	const u64 arctans[YS] = {1337637691987343317, 1361218612134873190, 1384611644667422749, 1504319350508084718, 22936177926750894};
	const u64 logs[YS] = {537654661102540701, 0, 17919736732383054105U, 15312181060378489024U, 0};
	for (int j = 0; j < YS; j++) {
		float y = ys[j];
		y *= SQRTMAX64;
		y *= SQRTMAX64;
		u64 y_u = y;
		{
			UINF_ALLOCA(x, 2);
			uinf_zero(x);
			UINF_ALLOCA(y, 2);
			uinf_assign64(y, y_u);
			arctan(x, y);
			u64 arclen_u = uinf_read64(x);
			if (arclen_u != arctans[j]) {
				float arclen = arclen_u;
				arclen /= SQRTMAX64;
				arclen /= SQRTMAX64;
				printf("Incorrect value:\n");
				printf("arctan(%llu) = %llu\n", y_u, arclen_u);
				printf("i.e. arctan(%.8f) = %f\n", ys[j], arclen);
				printf("\n");
			}
		}
		{
			UINF_ALLOCA(x, 2);
			uinf_zero(x);
			UINF_ALLOCA(y, 2);
			uinf_assign64(y, y_u);
			neglog2(x, y);
			u64 neglog_u = uinf_read64(x);
			if (neglog_u != logs[j]) {
				float neglog = neglog_u;
				neglog /= SQRTMAX64;
				neglog /= SQRTMAX64;
				printf("Incorrect value:\n");
				printf("-log(%llu) = %llu\n", y_u, neglog_u);
				printf("i.e. log(%.8f) = %f\n", ys[j], -neglog);
				printf("\n");
			}
		}
	}
}

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

int main() {
	test();
	UINF_ALLOCA(data, 2);
	reciprocol_twopi(data);
	u64 data_u = uinf_read64(data);
	float data_f = data_u;
	data_f /= SQRTMAX64;
	data_f /= SQRTMAX64;
	printf("1/2pi = %llu\n", data_u);
	printf("i.e. pi = %.8f\n", 0.5f / data_f);
}

