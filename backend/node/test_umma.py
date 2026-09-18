import sys, struct, random, re
sys.path.insert(0, '/home/nan/cupatch-new/cupatch-master'); sys.path.insert(0, '/home/nan/warpgemm')
from cupatch.cuda.harness import Harness, Buf, Out
from sasm import assemble
path = sys.argv[1]
M, N, K = map(int, re.search(r'umma_(\d+)_(\d+)_(\d+)', path).groups())
hdr, image = assemble(path)
open(path.replace('.sass', '.cubin'), 'wb').write(image)
random.seed(M * 1000003 + N * 1009 + K)
A  = [[float(random.randint(-3, 3)) for _ in range(K)] for _ in range(M)]
Bt = [[float(random.randint(-3, 3)) for _ in range(K)] for _ in range(N)]
ref = [[sum(A[m][k] * Bt[n][k] for k in range(K)) for n in range(N)] for m in range(M)]
r = Harness().run(image, hdr['kernel'], args=[Buf([x for row in A for x in row], 'f16'), Buf([x for row in Bt for x in row], 'f16'),
                                              Out(M * N * 4, 'f32')], grid=(1, 1, 1), block=(hdr['threads'], 1, 1))
print('%-24s status=%s %s regs=%s smem=%s' % (path, r.status, getattr(r, 'error', '') or '', hdr['regs'], hdr['smem']))
if r.status == 'ok':
    C = list(struct.unpack('<%df' % (M * N), r.outputs[0].raw))
    bad = [(m, n, C[m * N + n], ref[m][n]) for m in range(M) for n in range(N) if abs(C[m * N + n] - ref[m][n]) > 1e-3]
    print('  %s  %.3f ms  bad=%d/%d  first bad %s' % ('MATCH' if not bad else 'MISMATCH', r.elapsed_ms, len(bad), M * N, bad[:4]))
    print('  row0 got', C[:6], 'ref', ref[0][:6])
