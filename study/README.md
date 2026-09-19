# CuTe, measured

The paper asserts that CuTe's admissibility conditions "are not visible in
the CuTe API, yet all of them are visible failures"
(`paper/layout-algebra.tex`). This directory turns that assertion into a
measurement.

    ./run.sh          # build and run against a CUTLASS checkout

It needs **no GPU and no CUDA toolkit**. CuTe's layout algebra is
header-only and host-compilable; the only obstacle is that the headers
include CUDA runtime headers unconditionally, so `stub/` supplies the
handful of declarations they need (`half`, `dim3`, `cuFloatComplex`, …).
Nothing in `stub/` is ever executed — the algebra never touches those
values.

Point it at checkouts with:

    CUTLASS_DIR=/path/to/cutlass CCCL_DIR=/path/to/cccl ./run.sh

Both are shallow clones:

    git clone --depth 1 https://github.com/NVIDIA/cutlass.git
    git clone --depth 1 https://github.com/NVIDIA/cccl.git
