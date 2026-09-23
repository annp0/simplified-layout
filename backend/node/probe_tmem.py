"""Launch the allocator probe (warpc talloc N) several times in one context:
a launch that hangs after one that finished means the free left columns
allocated on the SM."""
import os, sys, ctypes
sys.path.insert(0, os.environ.get('CUPATCH', os.path.expanduser('~/cupatch-new/cupatch-master')))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cupatch.cuda import launcher as L
from sasm import assemble

hdr, image = assemble(sys.argv[1])
ctx = L.CudaContext()
mod = ctx.load_module(image)  # held: the function lives as long as its module
f = mod.get_function(hdr['kernel'])
out = ctx.alloc(64)
for i in range(int(sys.argv[2]) if len(sys.argv) > 2 else 5):
    f.launch(grid=(148, 1, 1), block=(hdr['threads'], 1, 1), args=[ctypes.c_uint64(out.ptr)], shared_mem=0, timed=False)
    print('launch', i, 'done', flush=True)
