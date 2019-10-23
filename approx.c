#include <stdio.h>

typedef unsigned u32;
typedef long long unsigned u64;

const u64 LO = ((u64) 1 << 32) - 1;
const u64 HI = LO << 32;

typedef struct {
	u32 hi;
	u32 lo;
} Unit;

const Unit UNIT_HALF = {1 << 31, 0};

Unit unit_from_u64(u64 x) {
	Unit result;
	result.lo = x & LO;
	result.hi = (x & HI) >> 32;
	return result;
}

u64 u64_from_unit(Unit x) {
	return ((u64) x.hi << 32) | (u64) x.lo;
}

float f32_from_unit(Unit x) {
	return (float)x.hi / (float)((u64)1 << 32);
}

Unit unit_from_f32(float x) {
	Unit result = {x * (float)((u64)1 << 32), 0};
	return result;
}


Unit unit_add(Unit x, Unit y) {
	Unit addlo = unit_from_u64((u64) x.lo + (u64) y.lo);
	addlo.hi += x.hi + y.hi;
	return addlo;
}

Unit unit_mul(Unit x, Unit y) {
	// x = x.hi / 2^32 + x.lo / 2^64;
	// x * y = (x.hi * y.hi / 2^64 + (x.lo * y.hi + x.hi * y.lo) / 2 ^ 96
	//   + x.lo * y.lo / 2^128
	Unit mulhihi = unit_from_u64((u64) x.hi * (u64) y.hi);
	mulhihi.lo += unit_from_u64((u64) x.lo * (u64) y.hi).hi;
	mulhihi.lo += unit_from_u64((u64) x.hi * (u64) y.lo).hi;
	return mulhihi;
}

typedef enum {
	false,
	true,
} bool;

// could use u64_from_unit(x) < u64_from_unit(y)
// but this will generalize
bool unit_lss(Unit x, Unit y) {
	if (x.hi == y.hi) {
		return x.lo < y.lo;
	}
	// else {
		return x.hi < y.hi;
	// }
}

// twos complement
Unit unit_negate(Unit x) {
	// manually check for 0 because overflow is undefined in C
	if (x.lo == 0) {
		if (x.hi == 0) {
			// do nothing
		} else {
			x.hi = ~x.hi + 1;
		}
	} else {
		x.hi = ~x.hi;
		x.lo = ~x.lo + 1;
	}
	return x;
}

Unit unit_sub(Unit x, Unit y) {
	// x - y
	// 1 - (1 - (x - y))
	// 1 - (1 - x + y)
	// (to avoid overflow)
	return unit_negate(unit_add(unit_negate(x), y));
}

bool test_unit_overflow(Unit x, Unit y) {
	//   x + y >= 1
	//   x >= 1 - y
	// !(x < 1 - y)
	return unit_lss(x, unit_negate(y));
}

Unit unit_rshift(Unit x, u32 shift) {
	u32 mask = (1 << shift) - 1;
	u32 carry = x.hi & mask;
	x.hi >>= shift;
	x.lo >>= shift;
	x.lo |= carry << (32 - shift);
	return x;
}

Unit unit_lshift(Unit x, u32 shift) {
	u32 mask = (1 << shift) - 1;
	u32 carry = x.lo & (mask << (32 - shift));
	x.hi <<= shift;
	x.lo <<= shift;
	x.hi |= carry >> (32 - shift);
	return x;
}

// complex number in a unit square with a number to keep track of winding
typedef struct {
	u64 quarter_turns;
	Unit x;
	Unit y;
} Rotation;

// will halve result to keep it in unit square if necessary
Rotation rot_mul(Rotation z1, Rotation z2) {
	// i^n1*(x1 + i*y1) * i^n2*(x2 + i*y2)
	// = i^(n1+n2)*(x1*x2 - y1*y2 + i*(x1*y2 + x2*y1))
	Unit xx = unit_mul(z1.x, z2.x);
	Unit xy = unit_mul(z1.x, z2.y);
	Unit yx = unit_mul(z1.y, z2.x);
	Unit yy = unit_mul(z1.y, z2.y);
	if (test_unit_overflow(xy, yx)) {
		xx = unit_rshift(xx, 1);
		xy = unit_rshift(xy, 1);
		yx = unit_rshift(yx, 1);
		yy = unit_rshift(yy, 1);
	}
	Unit ipart = unit_add(xy, yx);

	Rotation result;
	result.quarter_turns = z1.quarter_turns + z2.quarter_turns;
	// handle underflow by factoring out i
	if (unit_lss(xx, yy)) {
		result.quarter_turns += 1;
		// x + i*y = i*(y - i*x)
		result.x = ipart;
		result.y = unit_sub(yy, xx);
	} else {
		result.x = unit_sub(xx, yy);
		result.y = ipart;
	}
	while (unit_lss(result.x, UNIT_HALF) && unit_lss(result.y, UNIT_HALF)) {
		result.x = unit_lshift(result.x, 1);
		result.y = unit_lshift(result.y, 1);
	}
	return result;
}

bool tan_lss(Unit x, Unit y) {
	// tan(x) < y
	// arg(1 + i*y) < x
	// 4*arg((1 + i*y)^(2^62)) < x*2^64
	// quarter_turns < x
	Rotation z = {0,UNIT_HALF,unit_rshift(y, 1)};
	for (int i = 0; i < 62; i++) {
		z = rot_mul(z, z);
	}
	return z.quarter_turns < u64_from_unit(x);
}

Unit bisect(bool (*f_lss)(Unit, Unit), Unit x) {
	Unit y = UNIT_HALF;
	Unit delta = unit_rshift(y, 1);
	while (u64_from_unit(delta)) {
		if (f_lss(x, y)) {
			y = unit_sub(y, delta);
		} else {
			y = unit_add(y, delta);
		}
		delta = unit_rshift(delta, 1);
	}
	return y;
}

Unit tan_bisect(Unit x) {
	return bisect(tan_lss, x);
}

int main() {
	const int size = 50;
	for (int j = 0; j <= size; j++) {
		for (int i = 0; i <= size; i++) {
			float x = (float)i/(float)(8*size);
			float y = (float)(20 - j)/(float)size;
			if (tan_lss(unit_from_f32(x), unit_from_f32(y))) {
				putchar('X');
			} else {
				putchar(' ');
			}
		}
		printf("\n");
	}
	const u32 n = 16;
	for (u32 i = 0; i < n; i++) {
		float x = (float)i/(float)(8*n);
		float y = f32_from_unit(tan_bisect(unit_from_f32(x)));
		printf("tan(%f) = %f\n", x, y);
	}
}

