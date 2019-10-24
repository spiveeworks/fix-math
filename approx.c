#include <stdio.h>

typedef unsigned u32;
typedef long long unsigned u64;

const u32 HALFMAX32 = (u32)1 << 31;
const u64 SQRTMAX64 = (u64)1 << 32;
const u64 LO = SQRTMAX64 - 1;
// don't think we actually use this
// since we need to rshift anyway
const u64 HI = LO << 32;

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
		x.data[i] = carry & LO; // the mask might be implicit from downcast
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
	u32 prev_carry = 0;
	for (u64 i = 0; i < x.size; i++) {
		u32 carry = x.data[i] >> (32 - shift);
		x.data[i] <<= shift;
		x.data[i] |= prev_carry;
		prev_carry = carry;
	}
}

//////////////////////////////
// cartesian rotation counter

// complex number in a unit square with a number to keep track of winding
typedef struct {
	u64 quarter_turns;
	uinf x;
	uinf y;
} Rotation;

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
Rotation rot_mul(Rotation out, Rotation z1, Rotation z2) {
	// i^n1*(x1 + i*y1) * i^n2*(x2 + i*y2)
	// = i^(n1+n2)*(x1*x2 - y1*y2 + i*(x1*y2 + x2*y1))
	out.quarter_turns += z1.quarter_turns;
	out.quarter_turns += z2.quarter_turns;

	bool carry = false;
	carry = carry || uinf_mul(out.y, z1.x, z1.y);
	carry = carry || uinf_mul(out.y, z1.y, z1.x);

	uinf_mul(out.x, z1.x, z2.x);
	uinf_negate(out.x);
	bool rotate = uinf_mul(out.x, z1.y, z2.y);
	// at this point we have y1*y2 - (out.x + x1*x2)
	// the subend was negative so no overflow means it is still negative

	if (!rotate) {
		uinf_negate(out.x);
	}

	if (carry) {
		uinf_rshift(out.x, 1);
		uinf_rshift(out.y, 1);
		out.y.data[out.y.size - 1] |= HALFMAX32;
	}

	if (rotate) {
		uinf x = out.x;
		out.x = out.y;
		out.y = x;
		out.quarter_turns++;
	}

	while (!(
		(out.x.data[out.x.size - 1] & HALFMAX32) ||
		(out.y.data[out.y.size - 1] & HALFMAX32)
	)) {
		uinf_lshift(out.x, 1);
		uinf_lshift(out.y, 1);
	}

	return out;
}

//////////////////////////////
// reference functions

// dedekind cuts represent real numbers as the set of rational numbers smaller
// than them
// so tan(x) as a cut is the set {y : y < tan(x)}
// so our convention is f_cut(x, y) <=> y < f(x)
// such that currying f_cut would actually give a function Rat->Real

u64 arctan(u64 y) {
	//   2^64 * arctan(y)
	// = 2^64 * arg(1 + iy)
	// = 4 * arg((1 + iy)^(2^62))
	// = quarter turns of (1 + iy)^(2^62)
#define ACC 2
	u32 data[ACC * 6];
	Rotation z = {0, {ACC, data}, {ACC, data + ACC}};
	Rotation out = {0, {2*ACC, data + 2 * ACC}, {2*ACC, data + 4 * ACC}};
	z.x.data[0] = 0;
	z.x.data[1] = HALFMAX32;
	y >>= 1;
	z.y.data[0] = y & LO;
	z.y.data[1] = y >> 32;
	for (u64 i = 0; i < 62; i++) {
		out.quarter_turns = 0;
		for (u64 j = 0; j < out.x.size; j++) {
			out.x.data[j] = 0;
			out.y.data[j] = 0;
		}
		out = rot_mul(out, z, z);
		z.quarter_turns = out.quarter_turns;
		for (u64 j = 0; j < z.x.size; j++) {
			z.x.data[j] = out.x.data[j + ACC];
			z.y.data[j] = out.y.data[j + ACC];
		}
	}
	return z.quarter_turns;
}

u64 neglog2(u64 y0) {
	//   2^64 * arctan(y)
	// = 2^64 * arg(1 + iy)
	// = 4 * arg((1 + iy)^(2^62))
	// = quarter turns of (1 + iy)^(2^62)
#define ACC 2
	u32 data[ACC * 3];
	uinf y = {ACC, data}, out = {2*ACC, data+ACC};
	y.data[0] = y0 & LO;
	y.data[1] = y0 >> 32;
	u64 x = 0;
	for (u64 i = 0; i < 64; i++) {
		// this short circuit condition mainly exists so that the result is the
		// floor instead of ceil(x-1)
		if (y.data[0] == 0 && y.data[1] == HALFMAX32) {
			x += 1;
			// double y to get 1, which is a fixpoint of _^2
			// so just finish doubling x and return
			return i == 0 ? 0 : x << (64 - i);
		}
		for (u64 j = 0; j < out.size; j++) {
			out.data[j] = 0;
		}
		uinf_mul(out, y, y);
		x *= 2;
		while (!(out.data[out.size - 1] & HALFMAX32)) {
			uinf_lshift(out, 1);
			x += 1;
		}
		for (u64 j = 0; j < y.size; j++) {
			y.data[j] = out.data[j + ACC];
		}
	}
	return x;
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

int main() {
#define YS 5
	float ys[YS] = {0.49f, 0.5f, 0.51f, 0.5625f, 0.0078125f};
	for (int j = 0; j < YS; j++) {
		float y = ys[j];
		y *= SQRTMAX64;
		y *= SQRTMAX64;
		u64 y_u = y;
		u64 arclen_u = arctan(y);
		float arclen = arclen_u;
		arclen /= SQRTMAX64;
		arclen /= SQRTMAX64;
		u64 neglog_u = neglog2(y);
		float neglog = neglog_u;
		neglog /= SQRTMAX64;
		neglog /= SQRTMAX64;
		printf("arctan(%llu) = %llu\n", y_u, arclen_u);
		printf("i.e. arctan(%.8f) = %f\n", ys[j], arclen);
		printf("-log(%llu) = %llu\n", y_u, neglog_u);
		printf("i.e. log(%.8f) = %f\n", ys[j], -neglog);
		printf("\n");
		/*
		for (int i = 0; i <= size; i++) {
			float x = (float)i/(float)(8*size);
			if (arclen < x) {
				putchar('X');
			} else {
				putchar(' ');
			}
		}
		printf("\n");
		*/
	}
	/*
	const u32 n = 16;
	for (u32 i = 0; i < n; i++) {
		float x = (float)i/(float)(8*n);
		Unit y = arctan(unit_from_f64(x));
		printf("arctan(%.15f) = %llu\n", x, u64_from_unit(y));
	}
	*/
}

