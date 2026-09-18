import sys, struct, random
sys.path.insert(0, '/home/nan/cupatch-new/cupatch-master'); sys.path.insert(0, '/home/nan/warpgemm')
from cupatch.cuda.harness import Harness, Buf, Out
from sasm import assemble
hdr, image = assemble('mma1.sass')
random.seed(1)
A  = [[float(random.randint(-3, 3)) for _ in range(16)] for _ in range(16)]   # 16x16
Bt = [[float(random.randint(-3, 3)) for _ in range(16)] for _ in range(8)]    # 8x16 (n,k)
C_ref = [[sum(A[m][k] * Bt[n][k] for k in range(16)) for n in range(8)] for m in range(16)]
a_flat = [x for row in A for x in row]; b_flat = [x for row in Bt for x in row]
r = Harness().run(image, hdr['kernel'], args=[Buf(a_flat, 'f16'), Buf(b_flat, 'f16'), Out(16*8*4, 'f32')],
                  grid=(1,1,1), block=(32,1,1))
print('status:', r.status, r.error if r.error else '')
raw = r.outputs[0].raw
C = list(struct.unpack('<%df' % (len(raw)//4), raw))
got = [C[i*8:(i+1)*8] for i in range(16)]
ok = all(abs(got[m][n] - C_ref[m][n]) < 1e-3 for m in range(16) for n in range(8))
print('row 0 got :', got[0]); print('row 0 ref :', C_ref[0])
print('MATCH:', ok)
