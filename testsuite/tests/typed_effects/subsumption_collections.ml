(* TEST
setup-ocamlc.byte-build-env;
ocamlc.byte;
check-ocamlc.byte-output;
run;
check-program-output;
*)
type _ Effect.t += Yield : unit Effect.t | Accept : unit Effect.t

let f_pure () = ()
let f_yield () = Effect.perform Yield
let f_both () = Effect.perform Yield; Effect.perform Accept

(* 1. Pure function pushed into list expecting Yield *)
let test_pure_into_eff () =
  let queue : (unit -[ Yield ]-> unit) list = [ f_pure; f_yield ] in
  queue

(* 2. Yield function pushed into list expecting Yield | Accept *)
let test_subsume_into_wider () =
  let queue : (unit -[ Yield, Accept | 'e ]-> unit) list = [ f_yield; f_both ] in
  queue

(* 3. Function arguments expecting effectful callbacks accept pure callbacks *)
let run_worker (w : unit -[ Yield ]-> unit) = ()
let () = run_worker f_pure

(* 4. Record and Tuple fields widen via bidirectional expected type *)
type worker = { step : unit -[ Yield ]-> unit }
let w = { step = f_pure }

let () =
  ignore (test_pure_into_eff ());
  ignore (test_subsume_into_wider ());
  print_endline "6.1 OK"
