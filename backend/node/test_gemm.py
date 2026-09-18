import sys, struct, random, re
sys.path.insert(0, '/home/nan/cupatch-new/cupatch-master'); sys.path.insert(0, '/home/nan/warpgemm')
from cupatch.cuda.harness import Harness, Buf, Out
from sasm import assemble
h = Harness()
allok = True
for path in sys.argv[1:]:
    M, N, K = map(int, re.search(r'gemm_(\d+)_(\d+)_(\d+)', path).groups())
    hdr, image = assemble(path)
    random.seed(M * 1000003 + N * 1009 + K)
    A  = [[float(random.randint(-3, 3)) for _ in range(K)] for _ in range(M)]
    Bt = [[float(random.randint(-3, 3)) for _ in range(K)] for _ in range(N)]
    ref = [[sum(A[m][k] * Bt[n][k] for k in range(K)) for n in range(N)] for m in range(M)]
    r = h.run(image, hdr['kernel'], args=[Buf([x for row in A for x in row], 'f16'), Buf([x for row in Bt for x in row], 'f16'),
                                          Out(M * N * 4, 'f32')], grid=(1, 1, 1), block=(32, 1, 1))
    C = list(struct.unpack('<%df' % (M * N), r.outputs[0].raw))
    bad = [(m, n, C[m * N + n], ref[m][n]) for m in range(M) for n in range(N) if abs(C[m * N + n] - ref[m][n]) > 1e-3]
    ok = r.status == 'ok' and not bad
    allok &= ok
    flops = 2.0 * M * N * K
    print('%-22s status=%s %s  %.3f ms  %.1f GFLOP/s  regs=%s  first bad: %s' % (path, r.status, 'MATCH' if ok else 'MISMATCH', r.elapsed_ms, flops / r.elapsed_ms / 1e6, hdr['regs'], bad[:3]))
print('ALL MATCH:', allok)
