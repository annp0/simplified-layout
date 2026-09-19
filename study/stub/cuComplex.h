#pragma once
/* Minimal host stub of CUDA's complex types. */
struct cuFloatComplex { float x, y; };
struct cuDoubleComplex { double x, y; };
typedef cuFloatComplex cuComplex;
static inline float  cuCrealf(cuFloatComplex z) { return z.x; }
static inline float  cuCimagf(cuFloatComplex z) { return z.y; }
static inline double cuCreal (cuDoubleComplex z) { return z.x; }
static inline double cuCimag (cuDoubleComplex z) { return z.y; }
static inline cuFloatComplex  make_cuFloatComplex (float r, float i)  { return cuFloatComplex{r, i}; }
static inline cuDoubleComplex make_cuDoubleComplex(double r, double i){ return cuDoubleComplex{r, i}; }
