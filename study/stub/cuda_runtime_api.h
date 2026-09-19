#pragma once
/* Minimal stub so CuTe's header-only layout algebra compiles on the host.
   Only what cute/util/debug.hpp touches; nothing here is ever executed. */
#include <cstdio>
typedef int cudaError_t;
static const cudaError_t cudaSuccess = 0;
static inline cudaError_t cudaGetLastError(void) { return cudaSuccess; }
static inline const char* cudaGetErrorString(cudaError_t) { return "stub"; }
