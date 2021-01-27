// Missing function needed for TIS-CI

#include <limits.h>
#include <math.h>
#include <stdint.h>
#include <float.h>

int isatty(int fd)
{
  return 0;
}

float fabsf(float x)
{
  if (x == 0.0)
    return 0.0;
  if (x > 0.0)
    return x;
  return -x;
}

long long int llabs(long long int j)
{
  if (j == LLONG_MIN)
  {
    //@ assert invalid_llabs_input: \false;
  }
  if (j < 0)
    j = -j;
  return j;
}

/* rint, lrint, llrint from musl */

static const double_t toint = 1/DBL_EPSILON;

double rint(double x)
{
  union
  {
    double f;
    uint64_t i;
  } u = {x};
  int e = u.i >> 52 & 0x7ff;
  int s = u.i >> 63;
  double_t y;

  if (e >= 0x3ff + 52)
    return x;
  if (s)
    y = x - toint + toint;
  else
    y = x + toint - toint;
  if (y == 0)
    return s ? -0.0 : 0;
  return y;
}

long lrint(double x) {
  return rint(x);
}

long long llrint(double x)
{
return rint(x);
}

static const float_t tointf = 1/FLT_EPSILON;

float rintf(float x)
{
	union {float f; uint32_t i;} u = {x};
	int e = u.i>>23 & 0xff;
	int s = u.i>>31;
	float_t y;

	if (e >= 0x7f+23)
		return x;
	if (s)
		y = x - tointf + tointf;
	else
		y = x + tointf - tointf;
	if (y == 0)
		return s ? -0.0f : 0.0f;
	return y;
}

long lrintf(float x) {
  return rintf(x);
}

long long llrintf(float x) {
  return rintf(x);
}

double scalbn(double x, int n)
{
  union
  {
    double f;
    uint64_t i;
  } u;
  double_t y = x;

  if (n > 1023)
  {
    y *= 0x1p1023;
    n -= 1023;
    if (n > 1023)
    {
      y *= 0x1p1023;
      n -= 1023;
      if (n > 1023)
        n = 1023;
    }
  }
  else if (n < -1022)
  {
    /* make sure final n < -53 to avoid double
		   rounding in the subnormal range */
    y *= 0x1p-1022 * 0x1p53;
    n += 1022 - 53;
    if (n < -1022)
    {
      y *= 0x1p-1022 * 0x1p53;
      n += 1022 - 53;
      if (n < -1022)
        n = -1022;
    }
  }
  u.i = (uint64_t)(0x3ff + n) << 52;
  x = y * u.f;
  return x;
}

double ldexp(double x, int n)
{
	return scalbn(x, n);
}

double frexp(double x, int *e)
{
	union { double d; uint64_t i; } y = { x };
	int ee = y.i>>52 & 0x7ff;

	if (!ee) {
		if (x) {
			x = frexp(x*0x1p64, e);
			*e -= 64;
		} else *e = 0;
		return x;
	} else if (ee == 0x7ff) {
		return x;
	}

	*e = ee - 0x3fe;
	y.i &= 0x800fffffffffffffull;
	y.i |= 0x3fe0000000000000ull;
	return y.d;
}

float frexpf(float x, int *e)
{
	union { float f; uint32_t i; } y = { x };
	int ee = y.i>>23 & 0xff;

	if (!ee) {
		if (x) {
			x = frexpf(x*0x1p64, e);
			*e -= 64;
		} else *e = 0;
		return x;
	} else if (ee == 0xff) {
		return x;
	}

	*e = ee - 0x7e;
	y.i &= 0x807ffffful;
	y.i |= 0x3f000000ul;
	return y.f;
}

/*@ requires NOT_ZERO: x > 0;
  @ ensures 0 <= \result < sizeof(long long) * CHAR_BIT; */
int __builtin_ctzll(long long unsigned x) {
  // This uses a binary search algorithm from Hacker's Delight.
  int n = 1;
  if ((x & 0x00000000FFFFFFFF) == 0) {n = n +32; x = x >>32;}
  if ((x & 0x000000000000FFFF) == 0) {n = n +16; x = x >>16;}
  if ((x & 0x00000000000000FF) == 0) {n = n + 8; x = x >> 8;}
  if ((x & 0x000000000000000F) == 0) {n = n + 4; x = x >> 4;}
  if ((x & 0x0000000000000003) == 0) {n = n + 2; x = x >> 2;}
  return n - (x & 1);
}
