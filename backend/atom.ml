(* The layouts the Blackwell instructions fix.

   A kernel never writes a layout. The instruction that consumes a tile fixes
   its layout, and every copy is compiled from the layouts of its two ends.
   This module holds those layouts as values of the algebra, and the deciders
   that read an instruction's encoding back off a layout. Each decider rebuilds
   the image the encoding describes and compares it with the layout at every
   coordinate, so a layout the instruction cannot express is refused here, at
   compile time, rather than read wrongly on the device. *)

open Layouts

let pf = Printf.sprintf

(* The 128-byte XOR swizzle on byte addresses: the 16-byte chunk index (bits
   4..6) is XORed with the row index mod 8 (bits 7..9). CuTe's Swizzle<3,4,3>;
   SWIZZLE_128B in a tensor map, layout type 2 in a UMMA descriptor. It is the
   only mode the kernels use, so it is the only one given here: each further
   mode needs its own check on the device. *)
let sw128 : Swizzle.t = { bits = 3; src = 7; dst = 4 }

let sw128_span = 128 (* the bytes of one swizzled row *)

let sw128_period = 1024 (* the pattern repeats every 8 rows: a tile's base must be a multiple *)

let dims (l : (_, _) Layout.t) =
  match Layout.shape l with
  | Product [ Bound r; Bound c ] -> r, c
  | _ -> failwith "Atom: a two-dimensional tile"

let at2 l r c = Layout.offset l (Coord.Tuple [ Idx r; Idx c ])

(* do two maps agree at every coordinate of [l]'s domain, the second read
   through [coord] *)
let agrees l ~coord ~image =
  List.for_all (fun c -> Layout.offset l c = image (coord c)) (Coord.enumerate (Layout.shape l))

(* [rows] rows of [cols] elements of [elem] bytes, each row exactly one
   swizzle span, rows packed, the 128-byte XOR over the whole. This is the
   image a SWIZZLE_128B tensor-map box produces and consumes, and the K-major
   operand a SWIZZLE_128B UMMA descriptor describes. *)
let swizzled_rows ~rows ~cols ~elem : (Space.logical, Space.physical) Layout.t =
  if cols * elem <> sw128_span
  then failwith (pf "Atom: a 128-byte swizzled row holds %d bytes, not %d" sw128_span (cols * elem));
  Layout.with_swizzle
    (Layout.storage (Group [ Axis { size = rows; stride = cols * elem }; Axis { size = cols; stride = elem } ]))
    sw128

(* ---- tensor-map box ---- *)

type box =
  { box_rows : int
  ; box_cols : int
  ; box_elem : int
  ; box_swizzle : int (* bytes of the swizzle span *)
  }

(* The tensor-map box whose image is [l]: a box of the tile's shape with the
   128-byte swizzle, required to agree with [l] everywhere. *)
let tma_box l ~elem =
  let rows, cols = dims l in
  let canonical = swizzled_rows ~rows ~cols ~elem in
  if not (agrees l ~coord:Fun.id ~image:(Layout.offset canonical))
  then failwith "Atom.tma_box: no tensor-map box produces this layout";
  { box_rows = rows; box_cols = cols; box_elem = elem; box_swizzle = sw128_span }

(* ---- UMMA shared-memory operand descriptor ---- *)

type desc =
  { sbo : int (* bytes between 8-row core-matrix groups *)
  ; kstep : int (* 16-byte units the start advances by per MMA k step *)
  }

(* The K-major SWIZZLE_128B descriptor of [l]: rows one span apart inside an
   8-row group, groups SBO bytes apart, the XOR over the result. SBO is read
   off rows 0 and 8, which the swizzle leaves alone; the image the descriptor
   then describes is rebuilt and compared with [l]. The k steps of an MMA
   advance the start address, so every step's columns must be that image
   shifted by the step's offset before the swizzle -- also checked. *)
let umma_kmajor l ~elem ~mma_k =
  let rows, cols = dims l in
  if rows mod 8 <> 0 then failwith "Atom.umma_kmajor: rows come in groups of 8";
  if cols mod mma_k <> 0 then failwith "Atom.umma_kmajor: the tile holds whole MMA k steps";
  let sbo = at2 l 8 0 - at2 l 0 0 in
  let plain r c = ((r / 8) * sbo) + (r mod 8 * sw128_span) + (c * elem) in
  let image r c = Swizzle.eval sw128 (plain r c) in
  let coord = function Coord.Tuple [ Idx r; Idx c ] -> r, c | _ -> assert false in
  if not (agrees l ~coord ~image:(fun (r, c) -> image r c))
  then failwith "Atom.umma_kmajor: no SWIZZLE_128B K-major descriptor describes this layout";
  let step = at2 l 0 mma_k - at2 l 0 0 in
  for j = 0 to (cols / mma_k) - 1 do
    for r = 0 to rows - 1 do
      for c = 0 to mma_k - 1 do
        if at2 l r ((j * mma_k) + c) <> Swizzle.eval sw128 (plain r c + (j * step))
        then failwith "Atom.umma_kmajor: an MMA k step is not the descriptor advanced by its offset"
      done
    done
  done;
  if step mod 16 <> 0 then failwith "Atom.umma_kmajor: a k step is not a whole 16-byte unit";
  { sbo; kstep = step / 16 }

(* the descriptor's two words: start address and leading offset in the low
   word, SBO, version 1 and the layout type in the high one. LBO is not used
   by the swizzled K-major type; the encoding wants 1 there. *)
let desc_low_fixed = 1 lsl 16

let desc_high d = (d.sbo lsr 4) lor (1 lsl 14) lor (2 lsl 29)

(* ---- UMMA: one tcgen05.mma ---- *)

type elt =
  | F16
  | BF16
  | F32

let elt_bytes = function F16 | BF16 -> 2 | F32 -> 4
let elt_string = function F16 -> "f16" | BF16 -> "bf16" | F32 -> "f32"

type major =
  | K_major
  | MN_major

(* where the instruction reads an operand: a shared-memory descriptor, or
   tensor memory (A only) *)
type src =
  | Smem_desc
  | Tmem

(* The instruction, as CuTe's SM100_MMA_F16BF16_SS and _2x1SM_SS name it
   (cute/arch/mma_sm100_umma.hpp): the operand and accumulator types, the
   shape M x N it computes over all the CTAs it spans, those CTAs (its
   cta_group), each operand's major and where it is read from. *)
type umma =
  { ab : elt
  ; acc : elt
  ; m : int
  ; n : int
  ; ctas : int
  ; a_major : major
  ; b_major : major
  ; a_src : src
  }

(* the shapes CuTe's atoms accept for kind::f16 *)
let umma ~ab ~acc ~m ~n ~ctas ~a_major ~b_major ~a_src =
  (match ab with F16 | BF16 -> () | F32 -> failwith "Atom.umma: kind::f16 takes f16 or bf16 operands");
  (match acc with F16 | F32 -> () | BF16 -> failwith "Atom.umma: the accumulator is f16 or f32");
  (match ctas with
   | 1 ->
     if not (m = 64 || m = 128) then failwith (pf "Atom.umma: M = %d; one CTA takes 64 or 128" m);
     if not (n mod 8 = 0 && 8 <= n && n <= 256) then failwith (pf "Atom.umma: N = %d; one CTA takes a multiple of 8 in 8..256" n)
   | 2 ->
     if not (m = 128 || m = 256) then failwith (pf "Atom.umma: M = %d; a CTA pair takes 128 or 256" m);
     if not (n mod 16 = 0 && 16 <= n && n <= 256)
     then failwith (pf "Atom.umma: N = %d; a CTA pair takes a multiple of 16 in 16..256" n)
   | c -> failwith (pf "Atom.umma: cta_group %d" c));
  if a_src = Tmem && a_major <> K_major then failwith "Atom.umma: A read from tensor memory is K-major";
  { ab; acc; m; n; ctas; a_major; b_major; a_src }

(* the K of one instruction: 256 bits of each operand row *)
let umma_k u = 32 / elt_bytes u.ab

(* The atom's thread-value layouts, CuTe's MMA_Traits ALayout, BLayout and
   CLayout (cute/atom/mma_traits_sm100.hpp): coordinate (cta, (row, col)) to
   the row-major index of the operand's M x K, the N x K, or the result's
   M x N. The CTAs split the rows of A, of B and of the result, each taking
   a contiguous block. *)
let umma_split ~ctas ~rows ~cols : (Space.thread_value, Space.logical) Layout.t =
  Layout.of_linear
    (Group
       [ Axis { size = ctas; stride = rows / ctas * cols }
       ; Group [ Axis { size = rows / ctas; stride = cols }; Axis { size = cols; stride = 1 } ]
       ])

let umma_a u = umma_split ~ctas:u.ctas ~rows:u.m ~cols:(umma_k u)
let umma_b u = umma_split ~ctas:u.ctas ~rows:u.n ~cols:(umma_k u)
let umma_c u = umma_split ~ctas:u.ctas ~rows:u.m ~cols:u.n

(* The rows of an operand (or of the result) CTA [v] holds, read off the
   atom's layout: its first row and how many, refused unless they are one
   contiguous run of whole rows. *)
let cta_rows l ~cols ~v =
  let rows_of =
    List.sort_uniq compare
      (List.filter_map
         (function
           | Coord.Tuple [ Idx w; inner ] when w = v -> Some (Layout.offset l (Coord.Tuple [ Idx w; inner ]) / cols)
           | _ -> None)
         (Coord.enumerate (Layout.shape l)))
  in
  match rows_of with
  | [] -> failwith "Atom.cta_rows: no such CTA"
  | first :: _ ->
    let count = List.length rows_of in
    if List.nth rows_of (count - 1) <> first + count - 1 then failwith "Atom.cta_rows: the rows are not contiguous";
    first, count

(* The 32-bit instruction descriptor, field by field as CuTe's
   UMMA::InstrDescriptor lays it out (cute/arch/mma_sm100_desc.hpp):
   c_format [4,6), a_format [7,10), b_format [10,13), a_major 15, b_major 16,
   N >> 3 at [17,23), M >> 4 at [24,29). Dense, no negation, no shift. *)
let idesc u =
  let fmt = function F16 -> 0 | BF16 -> 1 | F32 -> assert false in
  let c_format = match u.acc with F16 -> 0 | F32 -> 1 | BF16 -> assert false in
  let major = function K_major -> 0 | MN_major -> 1 in
  (c_format lsl 4)
  lor (fmt u.ab lsl 7)
  lor (fmt u.ab lsl 10)
  lor (major u.a_major lsl 15)
  lor (major u.b_major lsl 16)
  lor ((u.n lsr 3) lsl 17)
  lor ((u.m lsr 4) lsl 24)

let umma_string u =
  pf "tcgen05.mma.cta_group::%d.kind::f16 %s x %s -> %s, M=%d N=%d K=%d, A %s %s, B smem %s" u.ctas
    (elt_string u.ab) (elt_string u.ab) (elt_string u.acc) u.m u.n (umma_k u)
    (match u.a_src with Smem_desc -> "smem" | Tmem -> "tmem")
    (match u.a_major with K_major -> "K-major" | MN_major -> "MN-major")
    (match u.b_major with K_major -> "K-major" | MN_major -> "MN-major")

(* ---- tensor memory ---- *)

(* The accumulator of a cta_group::1 M=128 MMA: row r is tensor-memory lane r,
   column c is column c, and an address is lane << 16 | column. *)
let tmem_accumulator ~rows ~cols : (Space.logical, Space.physical) Layout.t =
  if rows <> 128 then failwith "Atom.tmem_accumulator: the M=128 accumulator has 128 lanes";
  Layout.storage (Group [ Axis { size = rows; stride = 1 lsl 16 }; Axis { size = cols; stride = 1 } ])

(* tcgen05.ld.32x32b.x[n], one warp's fragment: lane l receives lane l of the
   warp's 32, register r column r, over a [32 x n] block. The block's place in
   the accumulator is the warp's quarter of the lanes and the column chunk;
   the instruction fixes the quarter to the warp's index mod 4. *)
let ldtm_block = 32

let ldtm_32x32b ~n : (Space.thread_value, Space.logical) Layout.t =
  Layout.of_linear (Group [ Axis { size = ldtm_block; stride = n }; Axis { size = n; stride = 1 } ])

(* The instruction's contract on its composite into tensor memory. [at w ch
   l r] is the address the composite gives lane l's register r of block
   (w, ch), where w is the block's place among the warps' lane quarters and
   ch its place along the load's chunks: one warp-uniform address per block,
   lane l at + l << 16 and register r at + r from it, and block w inside the
   lanes warp w may reach. *)
let check_ldtm ~at ~blocks_w ~blocks_ch ~n =
  for w = 0 to blocks_w - 1 do
    for ch = 0 to blocks_ch - 1 do
      let base = at w ch 0 0 in
      if base lsr 16 <> ldtm_block * w
      then failwith (pf "Atom.check_ldtm: block %d starts at lane %d, outside the warp's quarter" w (base lsr 16));
      for l = 0 to ldtm_block - 1 do
        for r = 0 to n - 1 do
          if at w ch l r - base <> (l lsl 16) + r
          then failwith "Atom.check_ldtm: the composite is not what one warp-uniform address reads"
        done
      done
    done
  done
