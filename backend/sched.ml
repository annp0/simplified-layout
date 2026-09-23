(* Control words for a straight-line program with loops: issue cycles from
   fixed latencies, scoreboards for variable-latency results and late
   reads, waits where a consumer needs them. Program order is kept; the
   scheduler decides only stalls, barriers and wait masks.

   A loop is handled by carrying the state at its back edge to its head
   and rescheduling until nothing changes: the pending-barrier sets only
   grow and the fixed-latency remainders only lengthen, so it converges. *)

open Sass

let br_stall = 13 (* what a taken branch is assumed to cost *)
let pipe_gap = function "hmma" -> 4 | _ -> 1

type snap =
  { s_ready : (reg * int) list
  ; s_hold : (reg * int) list
  ; s_pw : (reg * int) list
  ; s_pr : (reg * int) list
  }

let find0 tbl r = Option.value (Hashtbl.find_opt tbl r) ~default:0

let clear tbl mask =
  let gone = Hashtbl.fold (fun r m acc -> if m land mask <> 0 then (r, m land lnot mask) :: acc else acc) tbl [] in
  List.iter (fun (r, m) -> if m = 0 then Hashtbl.remove tbl r else Hashtbl.replace tbl r m) gone

let schedule (items : item list) : string list =
  let arr = Array.of_list items in
  let n = Array.length arr in
  let label_index = Hashtbl.create 8 in
  Array.iteri (fun i it -> match it with Label l -> Hashtbl.replace label_index l i | I _ -> ()) arr;
  let carry : (string, snap) Hashtbl.t = Hashtbl.create 8 in
  let issue = Array.make n 0 and waitm = Array.make n 0 and wbar = Array.make n 7 and rbar = Array.make n 7 in
  let pass () =
    let ready = Hashtbl.create 64 and hold = Hashtbl.create 64 in
    let pw = Hashtbl.create 64 and pr = Hashtbl.create 64 in
    let clock = ref (-1) in
    let prev_var = ref false and wcount = ref 0 and rcount = ref 0 and cur_wb = ref 0 and cur_rb = ref 3 in
    let last_pipe = Hashtbl.create 4 in
    (* issue cycle of the last instruction that set each scoreboard: a wait
       issued in the very next cycle does not see the barrier yet *)
    let sb_time = Array.make 6 (-100) in
    let changed = ref false in
    let set a i v = if a.(i) <> v then (a.(i) <- v; changed := true) in
    Array.iteri
      (fun i it ->
        match it with
        | Label l ->
          prev_var := false;
          (match Hashtbl.find_opt carry l with
           | None -> ()
           | Some s ->
             let at = !clock + 1 in
             List.iter (fun (r, rem) -> Hashtbl.replace ready r (max (find0 ready r) (at + rem))) s.s_ready;
             List.iter (fun (r, rem) -> Hashtbl.replace hold r (max (find0 hold r) (at + rem))) s.s_hold;
             List.iter (fun (r, m) -> Hashtbl.replace pw r (find0 pw r lor m)) s.s_pw;
             List.iter (fun (r, m) -> Hashtbl.replace pr r (find0 pr r lor m)) s.s_pr)
        | I ins ->
          let t = ref (!clock + 1) and wait = ref 0 in
          (match Hashtbl.find_opt last_pipe ins.pipe with Some ti -> t := max !t (ti + pipe_gap ins.pipe) | None -> ());
          let need_ready r = match Hashtbl.find_opt ready r with Some c -> t := max !t c | None -> () in
          let need_wait tbl r = match Hashtbl.find_opt tbl r with Some m -> wait := !wait lor m | None -> () in
          List.iter (fun r -> need_wait pw r; need_ready r) (ins.uses @ ins.late_uses);
          List.iter
            (fun r ->
              need_wait pw r;
              need_wait pr r;
              need_ready r;
              match Hashtbl.find_opt hold r with Some c -> t := max !t c | None -> ())
            ins.defs;
          (* a fence or barrier waits for every outstanding late read: the stores
             before it must have taken their data before it takes effect *)
          if ins.drain then begin
            Hashtbl.iter (fun _ m -> wait := !wait lor m) pr;
            if ins.branch = `Exit then Hashtbl.iter (fun _ m -> wait := !wait lor m) pw
          end;
          for i = 0 to 5 do
            if !wait land (1 lsl i) <> 0 then t := max !t (sb_time.(i) + 2)
          done;
          clear pw !wait;
          clear pr !wait;
          (* a write scoreboard for a variable-latency result, a read scoreboard
             for sources read after issue; consecutive such instructions share
             a batch's barriers *)
          let scoreboarded = ins.lat = Variable || ins.late_uses <> [] in
          let wb, rb =
            if scoreboarded then begin
              if not !prev_var then begin
                cur_wb := !wcount mod 3; incr wcount;
                cur_rb := 3 + (!rcount mod 3); incr rcount
              end;
              (if ins.lat = Variable && ins.defs <> [] then !cur_wb else 7), if ins.late_uses <> [] then !cur_rb else 7
            end
            else 7, 7
          in
          let rb = match ins.force_rb with Some r -> r | None -> rb in
          let wb = match ins.force_wb with Some w when wb <> 7 -> w | _ -> wb in
          prev_var := scoreboarded;
          List.iter
            (fun r ->
              Hashtbl.remove ready r; Hashtbl.remove hold r; Hashtbl.remove pw r;
              match ins.lat with
              | Fixed l -> Hashtbl.replace ready r (!t + l)
              | Variable -> Hashtbl.replace pw r (1 lsl wb))
            ins.defs;
          if rb <> 7 then List.iter (fun r -> Hashtbl.replace pr r (find0 pr r lor (1 lsl rb))) ins.late_uses;
          if ins.src_hold > 0 then List.iter (fun r -> Hashtbl.replace hold r (!t + ins.src_hold)) ins.uses;
          Hashtbl.replace last_pipe ins.pipe !t;
          if wb <> 7 then sb_time.(wb) <- !t;
          if rb <> 7 then sb_time.(rb) <- !t;
          set issue i !t; set waitm i !wait; set wbar i wb; set rbar i rb;
          clock := !t;
          (match ins.branch with
           | `Bra l when Hashtbl.find label_index l < i ->
             let depart = !t + br_stall in
             let rel tbl = Hashtbl.fold (fun r c acc -> if c > depart then (r, c - depart) :: acc else acc) tbl [] in
             let all tbl = Hashtbl.fold (fun r m acc -> (r, m) :: acc) tbl [] in
             Hashtbl.replace carry l { s_ready = rel ready; s_hold = rel hold; s_pw = all pw; s_pr = all pr }
           | _ -> ()))
      arr;
    !changed
  in
  let rec fix k = if pass () && k < 8 then fix (k + 1) in
  fix 0;
  (* materialize *)
  let next_issue i =
    let rec go j = if j >= n then None else match arr.(j) with I _ -> Some issue.(j) | Label _ -> go (j + 1) in
    go (i + 1)
  in
  let out = ref [] in
  let emit s = out := s :: !out in
  let ctrl ~stall ~wb ~rb ~wait =
    Printf.sprintf "{stall=%d yield=%d writebar=%d readbar=%d waitbar=%d}" stall (if stall <= 2 then 1 else 0) wb rb wait
  in
  Array.iteri
    (fun i it ->
      match it with
      | Label l -> emit (l ^ ":")
      | I ins ->
        let need = match next_issue i with Some t -> t - issue.(i) | None -> 5 in
        let need = match ins.branch with `Bra _ -> max need br_stall | `Exit -> 5 | `No -> need in
        let need = max need ins.min_stall in
        let stall = max 1 (min need 15) in
        emit (Printf.sprintf "  %s%s %s" ins.guard ins.text (ctrl ~stall ~wb:wbar.(i) ~rb:rbar.(i) ~wait:waitm.(i)));
        let rem = ref (need - stall) in
        while !rem > 0 do
          let s = min !rem 15 in
          emit (Printf.sprintf "  NOP %s" (ctrl ~stall:s ~wb:7 ~rb:7 ~wait:0));
          rem := !rem - s
        done)
    arr;
  List.rev !out
