#pragma once
/* Minimal stub of CUDA's vector_types.h, host-only. */
struct dim3 {
  unsigned x, y, z;
  dim3(unsigned x_ = 1, unsigned y_ = 1, unsigned z_ = 1) : x(x_), y(y_), z(z_) {}
};
struct char2  { signed char x, y; };
struct char4  { signed char x, y, z, w; };
struct uchar2 { unsigned char x, y; };
struct uchar4 { unsigned char x, y, z, w; };
struct short2 { short x, y; };
struct short4 { short x, y, z, w; };
struct ushort2{ unsigned short x, y; };
struct ushort4{ unsigned short x, y, z, w; };
struct int2   { int x, y; };
struct int4   { int x, y, z, w; };
struct uint2  { unsigned x, y; };
struct uint3  { unsigned x, y, z; };
struct uint4  { unsigned x, y, z, w; };
struct long2  { long x, y; };
struct ulong2 { unsigned long x, y; };
struct longlong2 { long long x, y; };
struct ulonglong2{ unsigned long long x, y; };
struct float2 { float x, y; };
struct float4 { float x, y, z, w; };
struct double2{ double x, y; };
struct double4{ double x, y, z, w; };
