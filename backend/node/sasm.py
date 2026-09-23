#!/usr/bin/env python3
"""Our SASS text -> cubin, through cupatch's assembler and ELF builder.

Header directives:  .kernel NAME  .sm sm_100a  .regs N  .barriers N  .params 8 8 ...
                    .threads N  .smem BYTES (user shared memory; the window's first
                    0x400 bytes are reserved)  .tcgen05 (kernel uses TMEM)
Lines:  LABEL:   or   INSTRUCTION {stall= yield= writebar= readbar= waitbar=}
"""
import sys, re, struct, os
# cupatch is the encoder; CUPATCH names its checkout
sys.path.insert(0, os.environ.get('CUPATCH', os.path.expanduser('~/cupatch-new/cupatch-master')))
from cupatch.obj import builder as B
from cupatch.obj.builder import KernelBuilder
from cupatch.obj.elf import SectionSpec, SHT_NOBITS, SHF_WRITE, SHF_ALLOC, SHF_INFO_LINK
from cupatch.obj.nvinfo import encode_bval, encode_hval, encode_sval
from cupatch.asm.parse import parse

BRANCH_OPS = {'BRA', 'BRX', 'JMP', 'BSSY', 'CALL', 'BRXU', 'JMX'}
CTRL_RE = re.compile(r'\{([^}]*)\}\s*$')

# Spellings cupatch's parser refuses as ambiguous: the form and its sources.
NAMED_FORMS = [
    (re.compile(r'^BAR\.SYNC\.DEFER_BLOCKING 0x0$'),
     lambda m: ('bar__SYNC_dfrBlk_II_optionalCount_II', dict(barmode=0, defer_blocking=1, Sb=0, Sc=0))),
    (re.compile(r'^BAR\.SYNC\.DEFER_BLOCKING (0x[0-9a-f]+), (0x[0-9a-f]+)$'),
     lambda m: ('bar__SYNC_dfrBlk_II_optionalCount_II',
                dict(barmode=0, defer_blocking=1, Sb=int(m.group(1), 16), Sc=int(m.group(2), 16)))),
    (re.compile(r'^UTCBAR \[UR(\d+)\], URZ$'),
     lambda m: ('utcbar__1CTA', dict(cluster_sz=0, paramtype=0, wakeup=0, multicast=0, URa=int(m.group(1)), URb=255, URc=255))),
    # the same commit delivered to every CTA the mask names; ptxas spells it
    # UTCBAR.MULTICAST for a one-CTA MMA and puts a plain mask in the register
    (re.compile(r'^UTCBAR\.MULTICAST \[UR(\d+)\], URZ, UR(\d+)$'),
     lambda m: ('utcbar__1CTA', dict(cluster_sz=0, paramtype=0, wakeup=0, multicast=1,
                                     URa=int(m.group(1)), URb=255, URc=int(m.group(2))))),
]

def parse_ctrl(clause):
    d = {}
    for kv in clause.split():
        k, v = kv.split('=')
        d[k] = int(v, 0)
    return d

def assemble(path):
    hdr = {'kernel': 'k', 'sm': 'sm_100a', 'regs': 16, 'barriers': 0, 'params': [], 'threads': None, 'smem': 0,
           'tcgen05': False, 'mbarriers': 1}
    lines = []
    for raw in open(path):
        s = raw.split('#')[0].split('//')[0].strip()
        if not s:
            continue
        if s.startswith('.'):
            key, _, rest = s[1:].partition(' ')
            if key == 'params':
                hdr['params'] = [int(x, 0) for x in rest.split()]
            elif key in ('regs', 'barriers', 'threads', 'smem', 'mbarriers'):
                hdr[key] = int(rest, 0)
            elif key == 'tcgen05':
                hdr['tcgen05'] = True
            elif key == 'tmap':
                # one per tensor-map parameter, in parameter order:
                # name rows cols elem_bytes box_rows box_cols swizzle_bytes
                hdr.setdefault('tmap', []).append(rest.split())
            else:
                hdr[key] = rest.strip()
            continue
        lines.append(s)
    labels, insns = {}, []
    for s in lines:
        if re.fullmatch(r'[A-Za-z_.$][\w.$]*:', s):
            labels[s[:-1]] = len(insns)
        else:
            insns.append(s)
    b = KernelBuilder(name=hdr['kernel'], sm=hdr['sm'], mangle=False)
    emitted = []
    for s in insns:
        m = CTRL_RE.search(s)
        ctrl = parse_ctrl(m.group(1)) if m else {}
        body = s[:m.start()].strip() if m else s
        emitted.append(body)
        toks = body.replace(',', ' ').split()
        mnem = next(t for t in toks if not t.startswith('@'))
        if mnem.split('.')[0] in BRANCH_OPS and toks[-1] in labels:
            # the text parser refuses code addresses; branches go through emit_branch
            target = labels[toks[-1]]
            guard = {}
            if toks[0].startswith('@'):
                g = toks[0][1:]
                if g.startswith('!'):
                    guard['Pg@not'] = 1; g = g[1:]
                guard['Pg'] = 7 if g == 'PT' else int(g[1:])
            b.emit_branch(mnem, target, ctrl, **guard)
            continue
        named_form = next(((f, srcs) for rx, mk in NAMED_FORMS for mm in [rx.match(body)] if mm for f, srcs in [mk(mm)]), None)
        if named_form:
            form, srcs = named_form
            b.emit(form, ctrl, **srcs)
            continue
        form, sources, named = parse(b._enc, body)
        # encode directly: emit(**sources) collides with sources named 'op'
        w0, w1 = b._enc.encode(form, sources, dict(ctrl, **named))
        b.emit_raw(w0, w1)
    # Metadata ptxas emits for a kernel that uses mbarriers or barriers: where
    # each of those instructions sits, and which uniform register holds the
    # barrier it names. The driver reads this when it has to suspend a kernel.
    def bar_reg(text):
        m = re.search(r'\[UR(\d+)', text)
        return int(m.group(1)) if m else 0xff

    mbar_words, coop_offsets, wide_offsets = [], [], []
    for i, text in enumerate(emitted):
        mnem = text.split()[0] if not text.startswith('@') else text.split()[1]
        kind = None
        if mnem.startswith('SYNCS.EXCH'):
            kind = 0x00
        elif mnem.startswith('SYNCS.PHASECHK'):
            kind = 0x0a
        if kind is not None:
            mbar_words += [i * 16, 0xff, 0, (bar_reg(text) << 16) | 0x0100 | kind]
        if mnem.startswith('BAR.') or mnem.startswith('WARPSYNC'):
            coop_offsets.append(i * 16)
        if mnem.startswith('VOTEU') or mnem.startswith('REDUX'):
            wide_offsets.append(i * 16)

    extras = {}
    if hdr['threads']:
        extras['max_threads'] = (hdr['threads'], 1, 1)
    if hdr['smem']:
        extras['extra_sections'] = [SectionSpec('.nv.shared.' + hdr['kernel'], SHT_NOBITS,
                                                flags=SHF_WRITE | SHF_ALLOC | SHF_INFO_LINK,
                                                size=0x400 + hdr['smem'], align=1024,
                                                info_section='.text.' + hdr['kernel'])]
    attrs = b''
    if wide_offsets:
        attrs += encode_sval(0x31, *wide_offsets)            # INT_WARP_WIDE_INSTR_OFFSETS
    if coop_offsets:
        attrs += encode_sval(0x28, *coop_offsets)            # COOP_GROUP_INSTR_OFFSETS
        attrs += encode_sval(0x29, *([0xffffffff] * len(coop_offsets)))
    if mbar_words:
        attrs += encode_sval(0x39, *mbar_words)              # MBARRIER_INSTR_OFFSETS
    attrs += encode_sval(0x1e, 0)                            # CRS_STACK_SIZE
    if hdr['barriers']:
        attrs += encode_bval(0x4c, hdr['barriers'])          # NUM_BARRIERS
    if hdr['tcgen05']:
        drop = set(filter(None, os.environ.get('SASM_DROP_ATTRS', '').split(',')))
        # EIATTR_AT_ENTRY_FRAGMENTS (TMEM_CTA1) is deliberately NOT emitted. It
        # asks the driver to run its own fragment at kernel entry, and on a
        # device whose tensor memory is not in the state that fragment expects
        # the launch fails outright (error 719), reproducibly on that device
        # and not on others. Tensor memory allocation works without it: what
        # the allocator needs is RESERVED_SMEM_USED and TCGEN05_1CTA_USED.
        if 'frag' in drop:
            attrs += encode_sval(0x4f, 4)
        if 'smem' not in drop:
            attrs += bytes([0x01, 0x41, 0, 0])               # RESERVED_SMEM_USED
        if 'tcgen' not in drop:
            attrs += bytes([0x01, 0x51, 0, 0])               # TCGEN05_1CTA_USED
        if 'mbar' not in drop:
            attrs += encode_hval(0x38, max(1, hdr['mbarriers']))  # NUM_MBARRIERS
        # VRC_CTA_INIT_COUNT must be 0x80 (the alloc permit UVIRTCOUNT.DEALLOC.SMPOOL 0x80 releases)
        if 'vrc' not in drop:
            orig = B.kernel_info
            def patched(*a, **k):
                return orig(*a, **k).replace(encode_bval(0x4a, 0), encode_bval(0x4a, 0x80))
            B.kernel_info = patched
    if attrs:
        extras['extra_attrs'] = attrs
    image = b.build(num_regs=hdr['regs'], num_barriers=hdr['barriers'], params=hdr['params'], **extras)
    return hdr, image

if __name__ == '__main__':
    hdr, image = assemble(sys.argv[1])
    out = sys.argv[2] if len(sys.argv) > 2 else hdr['kernel'] + '.cubin'
    open(out, 'wb').write(image)
    print('wrote', out, len(image), 'bytes')
