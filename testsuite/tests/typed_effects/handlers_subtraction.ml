(* TEST
setup-ocamlc.byte-build-env;
ocamlc.byte;
check-ocamlc.byte-output;
run;
check-program-output;
*)
type _ Effect.t += Yield : unit Effect.t

(* 1. Handler on pure computation does not force Yield *)
let run_pure () =
  match 42 with
  | v -> v
  | effect Yield, k -> Effect.Deep.continue k ()
(* Inferred type: val run_pure : unit -> int (completely pure) *)

(* 2. Handler on computation with rigid univar 'e subtracts Yield cleanly *)
let run_rigid (type e) (f : unit -[ Yield | e ]-> int) : int =
  match f () with
  | v -> v
  | effect Yield, k -> Effect.Deep.continue k ()

(* 3. Multi-effect heterogeneous handler: independent existential scoping *)
type _ Effect.t += State_get : int Effect.t | State_put : int -> unit Effect.t

let run_state init f =
  let s = ref init in
  match f () with
  | v -> v
  | effect State_get, k -> Effect.Deep.continue k !s
  | effect (State_put v), k -> s := v; Effect.Deep.continue k ()
(* Inferred type: val run_state : 'a -> (unit -[ State_get, State_put | 'e ]-> 'b) -['e]-> 'b *)

let () =
  assert (run_pure () = 42);
  let res = run_state 10 (fun () ->
    let v = Effect.perform State_get in
    Effect.perform (State_put (v + 5));
    Effect.perform State_get
  ) in
  assert (res = 15);
  print_endline "6.2 OK"
