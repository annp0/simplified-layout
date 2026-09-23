"""Launch a kernel with a cluster dimension, via cuLaunchKernelEx."""
import ctypes, os, sys
sys.path.insert(0, os.environ.get('CUPATCH', os.path.expanduser('~/cupatch-new/cupatch-master')))
from cupatch.cuda import launcher as L

CU_LAUNCH_ATTRIBUTE_CLUSTER_DIMENSION = 4

class LaunchAttrValue(ctypes.Union):
    _fields_ = [('pad', ctypes.c_byte * 64), ('clusterDim', ctypes.c_uint * 3)]

class LaunchAttribute(ctypes.Structure):
    _fields_ = [('id', ctypes.c_int), ('pad', ctypes.c_byte * 4), ('value', LaunchAttrValue)]

class LaunchConfig(ctypes.Structure):
    _fields_ = [('gridDimX', ctypes.c_uint), ('gridDimY', ctypes.c_uint), ('gridDimZ', ctypes.c_uint),
                ('blockDimX', ctypes.c_uint), ('blockDimY', ctypes.c_uint), ('blockDimZ', ctypes.c_uint),
                ('sharedMemBytes', ctypes.c_uint), ('hStream', ctypes.c_void_p),
                ('attrs', ctypes.POINTER(LaunchAttribute)), ('numAttrs', ctypes.c_uint)]

_keepalive = []

def launch_cluster(func, grid, block, args, shared_mem=0, cluster=(1, 1, 1), sync=True):
    lib = L._load_cuda()
    if not hasattr(lib, '_ex_bound'):
        lib.cuLaunchKernelEx.argtypes = [ctypes.POINTER(LaunchConfig), ctypes.c_void_p, ctypes.c_void_p, ctypes.c_void_p]
        lib.cuLaunchKernelEx.restype = ctypes.c_int
        lib._ex_bound = True
    params, keep = L._build_params(args)
    _keepalive.append((params, keep))
    if len(_keepalive) > 4096:
        del _keepalive[:2048]
    attr = LaunchAttribute()
    attr.id = CU_LAUNCH_ATTRIBUTE_CLUSTER_DIMENSION
    attr.value.clusterDim[0], attr.value.clusterDim[1], attr.value.clusterDim[2] = cluster
    cfg = LaunchConfig(grid[0], grid[1], grid[2], block[0], block[1], block[2], shared_mem, None,
                       ctypes.pointer(attr), 1)
    r = lib.cuLaunchKernelEx(ctypes.byref(cfg), func._handle, params, None)
    if r != 0:
        raise RuntimeError('cuLaunchKernelEx: %d' % r)
    if sync:
        r = lib.cuCtxSynchronize()
        if r != 0:
            raise RuntimeError('cuCtxSynchronize: %d' % r)
