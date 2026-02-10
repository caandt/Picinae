open Arm7_cfi
open Domainslib

let range a b = List.init (b-a) ((+) a)

let buf = Bytes.create 4;;
let read_uint ic =
  match In_channel.really_input ic buf 0 4 with
  | Some () -> (Bytes.get_int32_le buf 0 |> Int32.to_int) land 0xFFFF_FFFF
  | None -> 0;;
let read4 f ic =
  let a = read_uint ic in
  let b = read_uint ic in
  let c = read_uint ic in
  let d = read_uint ic in
  let e = f ic in
  (a, b, c, d, e);;
let read_uint_array ic =
  let remaining = Int64.sub (In_channel.length ic) (In_channel.pos ic) in
  let len = Int64.div remaining 4L |> Int64.to_int in
  let arr = Array.make len 0 in
  for i = 0 to len - 1 do
    arr.(i) <- read_uint ic
  done;
  arr;;

let read_ints filename =
  In_channel.with_open_bin filename read_uint_array
let read_ints' filename =
  In_channel.with_open_bin filename (read4 read_uint_array)

let write_ints filename data =
  Out_channel.with_open_bin filename (fun oc ->
    let buf = Bytes.create 4 in
    List.iter (fun value ->
      Bytes.set_int32_le buf 0 (Int32.of_int value);
      Out_channel.output_bytes oc buf
    ) data)

let input = Sys.argv.(1);;
let (bi, bi', tbi, ai, code) = read_ints' input;;
print_endline ("read file " ^ input);;
let input = Sys.argv.(2);;
let lr = read_ints input;;
print_endline ("read file " ^ input);;
let dis = 0x3fffc3f8::range bi (bi + Array.length code + 1);;
let pol (_:int) = dis;;

let use_lr' i = Array.mem i lr;;

let rec rw_par zs tc pol i2i' i ti ai bi txt =
  let dis = (pol 0) in
  let dis' = List.map i2i' dis in
  let num_domains = Domain.recommended_domain_count () in
  let pool = Task.setup_pool ~num_domains:(num_domains - 1) () in
  match find_hash dis dis' 31 with
  | None -> None
  | Some (sl, sr) ->
      let tc' _ = Some ((ti,sl), sr) in
      let tbl =
            (fun mjtm dis dis' ai sl sr n ->
  let m = mjtm dis dis' sl sr (Hashtbl.create (2*n)) in
  List.init n (fun x -> match Hashtbl.find_opt m x with | Some y -> y | _ -> ai * 4)
)
              make_jump_table_map dis dis' ai sl sr ((lsl) 1 ((-) 32 sr))
        in (
    let input = zs in
    let len = Array.length input in
    let txt_arr = Array.make len [] in
    let failed = Atomic.make false in
    Task.run pool (fun () ->
      Task.parallel_for pool ~chunk_size:1024 ~start:0 ~finish:(len - 1) ~body:(fun idx ->
        if not (Atomic.get failed) then
          match rewrite_inst tc' i2i' input.(idx) (pol 0) (i+idx) ti ai bi txt use_lr' with
          | Some ((r1, _), _) -> txt_arr.(idx) <- r1
          | None -> Atomic.set failed true
      )
    );
    if Atomic.get failed then None
    else
      let list1 = Array.to_list txt_arr in
      Some (list1, [tbl])
  )

let cfi_rw2 pol code bi bi' ti ai =
  let tc = fun _ -> None in
  let () = print_endline "starting rewrite" in
  let irm_lens = Array.to_list(Array.mapi (fun i -> rewrite_inst_len ((+) bi i) bi (Array.length code)) code) in
  let () = print_endline "computed lens" in
  let i2i' = make_i2i' bi bi' ai irm_lens in
  let () = print_endline "created i2i'" in
  let res = rw_par code tc pol i2i' bi ti ai bi code in
  let () = print_endline "completed rewrite" in
  res

let stem = Filename.remove_extension (Filename.basename input);;
let res = cfi_rw2 pol code bi bi' tbi ai;;
match res with
| Some (txt, dat) ->
    write_ints ("cfitmp/" ^ stem ^ ".i_s.bin") (make_i's (Array.to_list(Array.mapi (fun i -> rewrite_inst_len ((+) bi i) bi (Array.length code)) code)) bi');
    write_ints ("cfitmp/" ^ stem ^ ".txt.bin") (List.concat txt);
    write_ints ("cfitmp/" ^ stem ^ ".dat.bin") (List.concat dat);
    print_endline "success"
| None ->
    print_endline "failed"
