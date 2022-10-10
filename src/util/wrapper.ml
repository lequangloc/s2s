
open Globals
open Gen.Basic
open VarGen

let wrap_infer_inv f a b =
  let flag = !is_inferring in
  is_inferring := true;
  try
    let res = f a b in
    is_inferring := flag;
    res
  with _ as e ->
    (is_inferring := flag;
     raise e)

let wrap_exception ?(msg="") dval f e =
  try
    f e
  with _ -> 
    begin
      if msg!="" then print_endline_quiet ("Exception :"^msg);
      dval
    end 

let wrap_exc_as_false ?(msg="") f e = wrap_exception ~msg:msg false f e

let wrap_num_disj f n a b c d =
  let old_disj = !fixcalc_disj in
  fixcalc_disj := max n old_disj;
  try
    let res = f a b c d in
    fixcalc_disj := old_disj;
    res
  with _ as e ->
    (fixcalc_disj := old_disj;
     raise e)

let wrap_under_baga f a =
  let flag = !do_under_baga_approx in
  do_under_baga_approx := true;
  try
    let res = f a in
    (* restore flag do_classic_frame_rule  *)
    do_under_baga_approx := flag;
    res
  with _ as e ->
    (do_under_baga_approx := flag;
     raise e)

let wrap_reverify_scc f a b c =
  let flag = !reverify_flag in
  reverify_flag := true;
  try
    let res = f a b c in
    (* restore flag do_classic_frame_rule  *)
    reverify_flag := flag;
    res
  with _ as e ->
    (reverify_flag := flag;
     raise e)

let wrap_norm flag norm f a =
  try
    let res = f a in
    if flag then norm res
    else res
  with _ as e ->
    raise e



let wrap_gen save_fn set_fn restore_fn flags f a =
  (* save old_value *)
  let old_values = save_fn flags in
  let () = set_fn flags in
  try 
    let res = f a in
    (* restore old_value *)
    let () = restore_fn old_values in
    res
  with _ as e ->
    (restore_fn old_values;
     raise e)


let wrap_one_bool flag new_value f a =
  let save_fn flag = (flag,!flag) in
  let set_fn flag = flag := new_value in
  let restore_fn (flag,old_value) = flag := old_value in
  wrap_gen save_fn set_fn restore_fn flag f a

let wrap_after code f a =
  try
    let r = f a in
    let () = code () in
    r
  with e ->
    let () = code () in
    raise e
   
let print_header s =
  print_endline_quiet "\n=====================================";
  print_endline_quiet ("   "^s);
  print_endline_quiet "====================================="


let wrap_dd s f a =
  let s1 = "START -dd "^s in
  let s2 = "END   -dd "^s in
  let () = print_header s1 in
  wrap_after (fun () -> print_header s2) 
    (wrap_one_bool Debug.devel_debug_on true f) a

let wrap_two_bools flag1 flag2 new_value f a =
  let save_fn (flag1,flag2) = (flag1,flag2,!flag1,!flag2) in
  let set_fn (flag1,flag2) = (flag1 := new_value; flag2:=new_value) in
  let restore_fn (flag1,flag2,old1,old2) = flag1 := old1; flag2:=old2 in
  wrap_gen save_fn set_fn restore_fn (flag1,flag2) f a

let wrap_two_bools flag1 flag2 new_value f a =
  let pr r = string_of_bool !r in 
  Debug.no_2 "" pr pr (fun _ -> pr_pair pr pr (flag1,flag2)) (fun _ _ -> wrap_two_bools flag1 flag2 new_value f a) flag1 flag2 



let wrap_silence_output f a =
  wrap_one_bool VarGen.quiet_mode (* Gen.silence_ouput *) true f a
