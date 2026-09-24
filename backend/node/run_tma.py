"""Run a warpc GEMM kernel on the device: assemble it, encode the tensor maps it
describes, launch it (clustered when it asks for a cluster), check the result
against numpy and time it."""
import os, sys, re, ctypes, struct, time
import numpy as np
sys.path.insert(0, os.environ.get('CUPATCH', os.path.expanduser('~/cupatch-new/cupatch-master')))
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cupatch.cuda import launcher as L
from sasm import assemble
from clusterlaunch import launch_cluster, time_cluster

CU_TENSOR_MAP_DATA_TYPE_FLOAT16 = 6
CU_TENSOR_MAP_DATA_TYPE_FLOAT32 = 7
CU_TENSOR_MAP_SWIZZLE_128B = 3
CU_FUNC_ATTRIBUTE_MAX_DYNAMIC_SHARED_SIZE_BYTES = 8

def cuda():
    lib = L._load_cuda()
    if not hasattr(lib, '_tma_bound'):
        lib.cuTensorMapEncodeTiled.argtypes = [ctypes.c_void_p, ctypes.c_int, ctypes.c_uint32, ctypes.c_void_p,
                                               ctypes.POINTER(ctypes.c_uint64), ctypes.POINTER(ctypes.c_uint64),
                                               ctypes.POINTER(ctypes.c_uint32), ctypes.POINTER(ctypes.c_uint32),
                                               ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_int]
        lib.cuTensorMapEncodeTiled.restype = ctypes.c_int
        lib.cuFuncSetAttribute.argtypes = [ctypes.c_void_p, ctypes.c_int, ctypes.c_int]
        lib.cuFuncSetAttribute.restype = ctypes.c_int
        lib._tma_bound = True
    return lib

def tensor_map_2d(dptr, rows, cols, elem_bytes, box_rows, box_cols, swizzle=CU_TENSOR_MAP_SWIZZLE_128B, dtype=CU_TENSOR_MAP_DATA_TYPE_FLOAT16):
    """A row-major rows x cols matrix; box = box_rows x box_cols; returns 128 bytes."""
    lib = cuda()
    buf = ctypes.create_string_buffer(256)
    addr = (ctypes.addressof(buf) + 63) & ~63
    dims = (ctypes.c_uint64 * 2)(cols, rows)
    strides = (ctypes.c_uint64 * 1)(cols * elem_bytes)
    box = (ctypes.c_uint32 * 2)(box_cols, box_rows)
    estr = (ctypes.c_uint32 * 2)(1, 1)
    r = lib.cuTensorMapEncodeTiled(ctypes.c_void_p(addr), dtype, 2, ctypes.c_void_p(int(dptr)),
                                   dims, strides, box, estr, 0, swizzle, 2, 0)
    if r != 0:
        raise RuntimeError('cuTensorMapEncodeTiled failed: %d' % r)
    return ctypes.string_at(addr, 128)

def run(path, M, N, K, repeat=20, seed=1):
    hdr, image = assemble(path)
    tm, tn, tk = map(int, hdr['tile'].split())
    dyn = int(hdr['dynsmem'])
    ctx = L.CudaContext()
    lib = cuda()
    rng = np.random.default_rng(seed)
    A = rng.integers(-3, 4, size=(M, K)).astype(np.float16)
    Bt = rng.integers(-3, 4, size=(N, K)).astype(np.float16)
    ref = A.astype(np.float32) @ Bt.astype(np.float32).T
    dA = ctx.alloc(A.nbytes); ctx.write_bytes(dA, A.tobytes())
    dB = ctx.alloc(Bt.nbytes); ctx.write_bytes(dB, Bt.tobytes())
    dC = ctx.alloc(M * N * 4); ctx.write_bytes(dC, b'\x00' * (M * N * 4))
    cl = int(hdr.get('cluster', 1))
    mod = ctx.load_module(image)
    func = mod.get_function(hdr['kernel'])
    r = lib.cuFuncSetAttribute(func._handle, CU_FUNC_ATTRIBUTE_MAX_DYNAMIC_SHARED_SIZE_BYTES, dyn)
    if r != 0:
        raise RuntimeError('cuFuncSetAttribute failed: %d' % r)
    # Every tensor map as the kernel states it: the box and the swizzle are read
    # off the layout of the shared tile each matrix moves through, so the host
    # encodes exactly the image the kernel's addresses assume. Nothing here is
    # a default.
    arrays = {'a': (dA, (M, K)), 'bt': (dB, (N, K)), 'c': (dC, (M, N))}
    dtypes = {2: CU_TENSOR_MAP_DATA_TYPE_FLOAT16, 4: CU_TENSOR_MAP_DATA_TYPE_FLOAT32}
    swizzles = {128: CU_TENSOR_MAP_SWIZZLE_128B}
    if len(hdr.get('tmap', [])) != len(hdr['params']) - (1 if 'debug' in hdr else 0):
        raise RuntimeError('every parameter must be a tensor map the kernel describes')
    ptrs = []
    for name, rows, cols, elem, brows, bcols, swz in hdr['tmap']:
        rows, cols, elem, brows, bcols, swz = map(int, (rows, cols, elem, brows, bcols, swz))
        buf, shape = arrays[name]
        if (rows, cols) != shape:
            raise RuntimeError('%s: the kernel was compiled for %dx%d, the run is %dx%d' % ((name, rows, cols) + shape))
        dmap = ctx.alloc(128)
        ctx.write_bytes(dmap, tensor_map_2d(buf.ptr, rows, cols, elem, brows, bcols, swizzle=swizzles[swz], dtype=dtypes[elem]))
        ptrs.append(dmap.ptr)
    args = [ctypes.c_uint64(p) for p in ptrs]
    dbg = None
    if 'debug' in hdr:
        # a debugging build: each wait that gives up writes (wait, parity) here
        ndbg = 1 << 20
        dbg = ctx.alloc(8 * ndbg); ctx.write_bytes(dbg, b'\x00' * (8 * ndbg))
        args.append(ctypes.c_uint64(dbg.ptr))
    grid = (tuple(int(x) for x in hdr['grid'].split()) + (1,)) if 'grid' in hdr else (N // tn, M // tm, 1)
    block = (hdr['threads'], 1, 1)
    if cl > 1:
        launch_cluster(func, grid, block, args, shared_mem=dyn, cluster=(cl, 1, 1))
    else:
        func.launch(grid=grid, block=block, args=args, shared_mem=dyn, timed=False)
    if dbg is not None:
        import collections
        w = np.frombuffer(ctx.read_bytes(dbg, 8 * (1 << 20)), dtype=np.uint32).reshape(-1, 2)
        hit = np.nonzero(w[:, 0])[0]
        sites = dict(l[2:].split(': ', 1) for l in open(path) if l.startswith('# wait '))
        print('waits that gave up: %d' % len(hit))
        for (wid, par), n in collections.Counter((int(w[i, 0]), int(w[i, 1])) for i in hit).most_common(12):
            ex = [int(i) for i in hit if w[i, 0] == wid][:4]
            print('   %4d x  %s  parity %#x  (cta.warp %s)' % (n, sites.get('wait %d' % wid, '?'), par, ', '.join('%d.%d' % (i // 8, i % 8) for i in ex)))
    C = np.frombuffer(ctx.read_bytes(dC, M * N * 4), dtype=np.float32).reshape(M, N)
    bad = np.argwhere(np.abs(C - ref) > 1e-3)
    if os.environ.get('WARPC_DUMP'):
        np.save(os.environ['WARPC_DUMP'], np.stack([C, ref]))
    # the first launch has finished and been checked; say so before timing,
    # which launches again, so a hang is attributed to the right launch
    print('first launch done, %d wrong' % len(bad), file=sys.stderr, flush=True)
    if os.environ.get('WARPC_TILES') and len(bad):
        # which output tiles are wrong, and whether they were never written
        wrong = np.abs(C - ref) > 1e-3
        t = wrong.reshape(M // tm, tm, N // tn, tn).any(axis=(1, 3))
        z = (C == 0).reshape(M // tm, tm, N // tn, tn).all(axis=(1, 3))
        print("   wrong tiles %d of %d, never written %d" % (int(t.sum()), t.size, int((t & z).sum())))
        rows = [''.join('x' if t[i, j] else '.' for j in range(t.shape[1])) for i in range(min(t.shape[0], 16))]
        print("   " + "\n   ".join(rows))
    if os.environ.get('WARPC_DIAG') and len(bad):
        import collections
        z = int(np.sum(C[bad[:,0], bad[:,1]] == 0.0))
        print("   zeros %d of %d" % (z, len(bad)))
        print("   tiles %s" % collections.Counter((int(r)//tm, int(c)//tn) for r,c in bad).most_common(5))
        print("   warp-of-tile %s" % sorted(collections.Counter((int(r)%tm)//32 for r,_ in bad).items()))
        print("   chunk %s" % sorted(collections.Counter((int(c)%tn)//32 for _,c in bad).items()))
        print("   piece %s" % sorted(collections.Counter((int(c)%32)//4 for _,c in bad).items()))
        print("   row-in-32 %s" % sorted(collections.Counter(int(r)%32 for r,_ in bad).items())[:10])
        nz = bad[C[bad[:,0], bad[:,1]] != 0.0]
        if len(nz):
            r0, c0 = nz[0]
            hit = np.argwhere(np.abs(ref - C[r0, c0]) < 1e-3)
            print("   nonzero bad (%d,%d) got %s ; ref has that value at %s" % (r0, c0, C[r0,c0], hit[:4].tolist()))
    if cl > 1:
        # device time, between CUDA events, as the plain launch below is timed
        ms = time_cluster(func, grid, block, args, shared_mem=dyn, cluster=(cl, 1, 1), repeat=repeat)
    else:
        ms = func.launch(grid=grid, block=block, args=args, shared_mem=dyn, timed=True, repeat=repeat)
    flops = 2.0 * M * N * K
    print('%-28s %dx%dx%d grid=%s  %s bad=%d/%d  %.4f ms  %.1f TFLOP/s' % (path, M, N, K, grid[:2], 'MATCH' if len(bad) == 0 else 'MISMATCH', len(bad), M * N, ms, flops / ms / 1e9))
    if len(bad):
        i, j = bad[0]; print('   first bad (%d,%d): got %s ref %s' % (i, j, C[i, j], ref[i, j]))
        print('   row0 got', C[0, :6], 'ref', ref[0, :6])
        rows_bad = sorted(set(bad[:, 0].tolist())); print('   bad rows: %d, first %s' % (len(rows_bad), rows_bad[:8]))
        cols_bad = sorted(set(bad[:, 1].tolist())); print('   bad cols: %d, first %s' % (len(cols_bad), cols_bad[:8]))
    return len(bad) == 0

def shape_of(path):
    """M, N, K as the kernel's tensor maps state them: a is M x K, bt is N x K."""
    dims = {}
    for line in open(path):
        if line.startswith('.tmap '):
            name, rows, cols = line.split()[1:4]
            dims[name] = (int(rows), int(cols))
    (m, k), (n, _) = dims['a'], dims['bt']
    return m, n, k

if __name__ == '__main__':
    path = sys.argv[1]
    run(path, *shape_of(path), repeat=int(sys.argv[2]) if len(sys.argv) > 2 else 30)
