import sys, struct, random
sys.path.insert(0, '/home/nan/cupatch-new/cupatch-master'); sys.path.insert(0, '/home/nan/warpgemm')
from cupatch.cuda.harness import Harness, Buf, Out, Scalar
from sasm import assemble
hdr, image = assemble('mmak.sass')
open('mmak.cubin','wb').write(image)
h = Harness()
allok = True
for K in (16, 64, 256):
    random.seed(K)
    A  = [[float(random.randint(-3, 3)) for _ in range(K)] for _ in range(16)]
    Bt = [[float(random.randint(-3, 3)) for _ in range(K)] for _ in range(8)]
    ref = [[sum(A[m][k]*Bt[n][k] for k in range(K)) for n in range(8)] for m in range(16)]
    r = h.run(image, hdr['kernel'], args=[Buf([x for r_ in A for x in r_],'f16'), Buf([x for r_ in Bt for x in r_],'f16'),
                                          Out(16*8*4,'f32'), Scalar(K,'u32')], grid=(1,1,1), block=(32,1,1))
    C = list(struct.unpack('<128f', r.outputs[0].raw)); got = [C[i*8:(i+1)*8] for i in range(16)]
    ok = r.status == 'ok' and all(abs(got[m][n]-ref[m][n]) < 1e-3 for m in range(16) for n in range(8))
    allok &= ok
    print('K=%-4d status=%s  %s  (%.3f ms)  row0 got %s ref %s' % (K, r.status, 'MATCH' if ok else 'MISMATCH', r.elapsed_ms, got[0][:4], ref[0][:4]))
print('ALL MATCH:', allok)
