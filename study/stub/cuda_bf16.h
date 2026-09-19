#pragma once
#include <cstdint>
struct __nv_bfloat16_raw;
struct __nv_bfloat16 {
  unsigned short __x;
  __nv_bfloat16() : __x(0) {}
  __nv_bfloat16(unsigned short v) : __x(v) {}
  inline __nv_bfloat16(__nv_bfloat16_raw const& r);
  inline operator __nv_bfloat16_raw() const;
};
struct __nv_bfloat16_raw { unsigned short x; };
inline __nv_bfloat16::__nv_bfloat16(__nv_bfloat16_raw const& r) : __x(r.x) {}
inline __nv_bfloat16::operator __nv_bfloat16_raw() const { __nv_bfloat16_raw r; r.x = __x; return r; }
struct __nv_bfloat162 { __nv_bfloat16 x, y; };
static inline float __bfloat162float(__nv_bfloat16 h) { (void)h; return 0.0f; }
static inline __nv_bfloat16 __float2bfloat16(float f) { (void)f; return __nv_bfloat16(); }
static inline __nv_bfloat16 __float2bfloat16_rn(float f) { (void)f; return __nv_bfloat16(); }
