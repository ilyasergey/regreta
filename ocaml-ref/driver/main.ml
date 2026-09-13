(* Command-line driver for the Greta reference implementation.

   Reads the line-based text format shared with `lake exe greta` (see ../docs/testing.md),
   runs one of the reference algorithms, and prints the result in the same format so that
   the two implementations can be compared directly. *)

open Gretacore

(* ---------------------------------------------------------------- text format *)

let dec s = if s = "-" then "" else s
let enc s = if s = "" then "-" else s

let tokens line =
  String.split_on_char ' ' (String.concat " " (String.split_on_char '\t' line))
  |> List.filter (fun s -> s <> "")

let read_lines path =
  let ic = open_in path in
  let rec loop acc =
    match input_line ic with
    | line -> loop (tokens (String.trim line) :: acc)
    | exception End_of_file -> close_in ic; List.rev acc
  in
  loop [] |> List.filter (fun ts -> ts <> [] && List.hd ts <> "#")

let parse_beta (t : string) : Ta.beta =
  if String.length t > 2 && String.sub t 0 2 = "T:" then
    Ta.T (dec (String.sub t 2 (String.length t - 2)))
  else if String.length t > 2 && String.sub t 0 2 = "S:" then
    Ta.S (dec (String.sub t 2 (String.length t - 2)))
  else failwith ("bad rhs entry: " ^ t)

let parse_sigma (t : string) : Cfg.sigma =
  if String.length t > 2 && String.sub t 0 2 = "T:" then
    Cfg.Term (dec (String.sub t 2 (String.length t - 2)))
  else if String.length t > 2 && String.sub t 0 2 = "N:" then
    Cfg.Nt (dec (String.sub t 2 (String.length t - 2)))
  else failwith ("bad rhs entry: " ^ t)

let parse_ta path : Ta.ta =
  let states = ref [] and finals = ref [] and terms = ref [] in
  let tbl : ((Ta.state * Ta.symbol), Ta.beta list) Hashtbl.t = Hashtbl.create 64 in
  let alphabet = ref [] in
  read_lines path
  |> List.iter (fun ts ->
         match ts with
         | "states" :: xs -> states := List.map dec xs
         | "finals" :: xs -> finals := List.map dec xs
         | "terminals" :: xs -> terms := List.map dec xs
         | "trans" :: tgt :: i :: n :: r :: rhs ->
             let sym = (int_of_string i, dec n, int_of_string r) in
             if not (List.mem sym !alphabet) then alphabet := !alphabet @ [ sym ];
             Hashtbl.add tbl (dec tgt, sym) (List.map parse_beta rhs)
         | t :: _ -> failwith ("unknown directive: " ^ t)
         | [] -> ());
  { Ta.states = !states; alphabet = !alphabet; final_states = !finals;
    terminals = !terms; transitions = tbl }

let parse_cfg path : Cfg.cfg =
  let nonterms = ref [] and terms = ref [] and starts = ref [] and prods = ref [] in
  read_lines path
  |> List.iter (fun ts ->
         match ts with
         | "nonterms" :: xs -> nonterms := xs
         | "terms" :: xs -> terms := xs
         | "starts" :: xs -> starts := xs
         | "prod" :: lhs :: rhs -> prods := !prods @ [ (lhs, List.map parse_sigma rhs) ]
         | t :: _ -> failwith ("unknown directive: " ^ t)
         | [] -> ());
  { Cfg.nonterms = !nonterms; terms = !terms; starts = !starts; productions = !prods }

let string_of_beta (b : Ta.beta) =
  match b with Ta.T t -> "T:" ^ enc t | Ta.S s -> "S:" ^ enc s

let string_of_sym ((i, n, r) : Ta.symbol) =
  Printf.sprintf "%d %s %d" i (enc n) r

let uniq l = List.fold_left (fun acc x -> if List.mem x acc then acc else acc @ [ x ]) [] l

let print_ta (a : Ta.ta) =
  let line kw xs = kw ^ " " ^ String.concat " " (List.map enc (List.sort compare (uniq xs))) in
  print_endline (line "states" a.Ta.states);
  print_endline (line "finals" a.Ta.final_states);
  print_endline (line "terminals" a.Ta.terminals);
  let trans =
    Hashtbl.fold
      (fun (st, sym) rhs acc ->
        (Printf.sprintf "trans %s %s%s" (enc st) (string_of_sym sym)
           (String.concat "" (List.map (fun b -> " " ^ string_of_beta b) rhs)))
        :: acc)
      a.Ta.transitions []
  in
  List.iter print_endline (List.sort compare (uniq trans))

(* ---------------------------------------------------------------- commands *)

let cmd_cfg2ta path =
  let g = parse_cfg path in
  let a, _, _, _, _, _ = Converter.cfg_to_ta false g in
  print_ta a

let cmd_obp path =
  let g = parse_cfg path in
  let _, _, obp_tbl, _, _, _ = Converter.cfg_to_ta false g in
  let entries =
    Hashtbl.fold
      (fun ord symlsls acc ->
        let ids = List.concat symlsls |> List.map Ta.id_of_sym |> uniq |> List.sort compare in
        (ord, ids) :: acc)
      obp_tbl []
    |> List.sort compare
  in
  List.iter
    (fun (ord, ids) ->
      print_endline
        (Printf.sprintf "order %d%s" ord
           (String.concat "" (List.map (fun i -> " " ^ string_of_int i) ids))))
    entries

let cmd_intersect ?(debug = false) p1 p2 =
  let a1 = parse_ta p1 in
  let a2 = parse_ta p2 in
  let r = Operation.intersect a1 a2 debug in
  if not debug then print_ta r

let usage =
  "greta-ref — driver for the Greta reference implementation\n\n\
  \  greta-ref cfg2ta GRAMMAR       print A_g, as built by Converter.cfg_to_ta\n\
  \  greta-ref obp GRAMMAR          print the base precedence order it computes\n\
  \  greta-ref intersect TA1 TA2    run Operation.intersect\n\
  \  greta-ref intersect-debug ...  the same, with the reference tracing enabled\n"

(* A watchdog: the reference implementation can loop forever on some inputs (see
   ../docs/reference-defects.md), and we want the trace produced so far when that happens. *)
let install_watchdog () =
  match Sys.getenv_opt "GRETA_REF_TIMEOUT" with
  | None -> ()
  | Some s ->
      let secs = int_of_string s in
      Sys.set_signal Sys.sigalrm
        (Sys.Signal_handle
           (fun _ ->
             flush stdout;
             prerr_endline "greta-ref: timed out";
             exit 124));
      ignore (Unix.alarm secs)

let () =
  install_watchdog ();
  match Array.to_list Sys.argv with
  | _ :: "cfg2ta" :: [ p ] -> cmd_cfg2ta p
  | _ :: "obp" :: [ p ] -> cmd_obp p
  | _ :: "intersect" :: [ p1; p2 ] -> cmd_intersect p1 p2
  | _ :: "intersect-debug" :: [ p1; p2 ] -> cmd_intersect ~debug:true p1 p2
  | _ -> print_string usage
