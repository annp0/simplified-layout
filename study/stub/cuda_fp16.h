#pragma once
/* Minimal host stub: CUTLASS's numeric types reference `half` even in
   host-only builds. The layout algebra never touches these values. */
#include <cstdint>
struct __half_raw;
struct __half {
  unsigned short __x;
  __half() : __x(0) {}
  __half(unsigned short v) : __x(v) {}
  inline __half(__half_raw const& r);
  inline operator __half_raw() const;
};
typedef __half half;
struct __half2 { __half x, y; };
typedef __half2 half2;
static inline float __half2float(__half h) { (void)h; return 0.0f; }
static inline __half __float2half(float f) { (void)f; return __half{0}; }
static inline __half __float2half_rn(float f) { (void)f; return __half{0}; }
static inline __half __ushort_as_half(unsigned short u) { return __half{u}; }
static inline unsigned short __half_as_ushort(__half h) { return h.__x; }
struct __half_raw { unsigned short x; };
inline __half::__half(__half_raw const& r) : __x(r.x) {}
inline __half::operator __half_raw() const { __half_raw r; r.x = __x; return r; }
