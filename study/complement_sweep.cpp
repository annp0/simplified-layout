// How often does CuTe's complement meet its own documented postconditions?
//
// The postconditions are taken verbatim from CuTe's own unit test,
// test/unit/cute/core/complement.cpp:
//
//     EXPECT_GE(cosize(completed), size(cotarget));            // (1)
//     for (int i = 1; i < size(result); ++i) {
//       EXPECT_LT(result(i-1), result(i));                     // (2) ordered
//       for (int j = 0; j < size(layout); ++j)
//         EXPECT_NE(result(i), layout(j));                     // (3) disjoint
//     }
//
// and each rank-2 layout is classified by the divisibility condition the
// complement formula requires -- N_0 d_0 | d_1, with the modes sorted by
// stride. Everything is static, so this is the case CuTe CAN check.
#include <cute/layout.hpp>
#include <cstdio>

using namespace cute;

struct Tally { int total = 0, ok = 0, broken = 0; };
static Tally satisfied, violated;

template <int N0, int D0, int N1, int D1, int M>
void one() {
  auto a = make_layout(make_shape(Int<N0>{}, Int<N1>{}),
                       make_stride(Int<D0>{}, Int<D1>{}));
  auto r = complement(a, Int<M>{});
  auto completed = make_layout(a, r);

  bool p1 = (cosize(completed) >= M);
  bool p2 = true, p3 = true;
  for (int i = 1; i < size(r); ++i) {
    if (!(r(i-1) < r(i))) p2 = false;
    for (int j = 0; j < size(a); ++j) if (r(i) == a(j)) p3 = false;
  }
  bool all = p1 && p2 && p3;

  // modes sorted by stride; D0 <= D1 is enforced by the caller
  constexpr bool cond = (D1 % (N0 * D0)) == 0;
  Tally& t = cond ? satisfied : violated;
  ++t.total;
  if (all) ++t.ok; else ++t.broken;

  if (!all) {
    std::printf("  (%d,%d):(%d,%d)  M=%-3d  ->  ", N0, N1, D0, D1, M);
    print(r);
    std::printf("   cond=%-3s cosize=%-3d %s%s%s\n",
                cond ? "yes" : "NO", (int)cosize(completed),
                p1 ? "" : "[cosize] ", p2 ? "" : "[ordered] ", p3 ? "" : "[disjoint] ");
  }
}

// The complement formula divides d_1 by N_0 d_0; when that quotient is
// zero CuTe fires a static_assert ("Non-injective Layout detected"), a
// case it DOES reject, so those are skipped rather than counted.
template <int N0, int D0, int N1, int D1, int M>
void guarded() {
  if constexpr (D1 >= D0 * N0 && D0 <= D1) one<N0, D0, N1, D1, M>();
}

template <int N0, int D0, int N1, int M, int... D1>
void over_d1(std::integer_sequence<int, D1...>) {
  (guarded<N0, D0, N1, D1 + 1, M>(), ...);
}

template <int N0, int D0, int M, int... N1>
void over_n1(std::integer_sequence<int, N1...>) {
  (over_d1<N0, D0, N1 + 2, M>(std::make_integer_sequence<int, 16>{}), ...);
}

template <int D0, int M, int... N0>
void over_n0(std::integer_sequence<int, N0...>) {
  (over_n1<N0 + 2, D0, M>(std::make_integer_sequence<int, 3>{}), ...);
}

template <int M>
void sweep() {
  over_n0<1, M>(std::make_integer_sequence<int, 3>{});
  over_n0<2, M>(std::make_integer_sequence<int, 3>{});
}

int main() {
  std::printf("complement postcondition failures (CuTe's own predicates)\n\n");
  sweep<12>();
  sweep<24>();
  sweep<48>();
  std::printf("\n  divisibility condition SATISFIED: %4d layouts, %4d meet all postconditions, %4d fail\n",
              satisfied.total, satisfied.ok, satisfied.broken);
  std::printf("  divisibility condition VIOLATED : %4d layouts, %4d meet all postconditions, %4d fail\n",
              violated.total, violated.ok, violated.broken);
  // machine-readable, for study/run.sh
  std::printf("#cute comp.satisfied %d\n", satisfied.total);
  std::printf("#cute comp.satisfied_broken %d\n", satisfied.broken);
  std::printf("#cute comp.violated %d\n", violated.total);
  std::printf("#cute comp.violated_broken %d\n", violated.broken);
  std::printf("#cute comp.total %d\n", satisfied.total + violated.total);
  return 0;
}
