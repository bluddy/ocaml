(* TEST
setup-ocamlc.byte-build-env;
ocamlc.byte;
check-ocamlc.byte-output;
run;
check-program-output;
*)
type _ Effect.t += Yield : unit Effect.t

module type PURE_ORD = sig
  type t
  val compare : t -> t -> int
end

(* Unpacking pure first-class module parameter *)
let test_pure_unpack (type a) (module O : PURE_ORD with type t = a) (x : a) (y : a) : int =
  O.compare x y

(* Module with abstract effect equation *)
module type RUNNER = sig
  effect eff
  val step : unit -[ eff ]-> bool
end

let test_effect_unpack (module R : RUNNER with effect eff = -[ Yield ]-) () =
  if R.step () then Effect.perform Yield

(* Destructive substitution erases eff cleanly down to pure -> *)
let test_subst_unpack (module R : RUNNER with effect eff := -[ ]-) () =
  R.step ()
(* Inferred type: val test_subst_unpack : (module RUNNER with effect eff := -[ ]) -> unit -> bool *)

module IntOrd = struct
  type t = int
  let compare = Int.compare
end

module YieldRunner = struct
  effect eff = -[ Yield ]-
  let step () = true
end

module PureRunner = struct
  effect eff = -[ ]-
  let step () = true
end

let () =
  assert (test_pure_unpack (module IntOrd) 3 5 < 0);
  (match test_effect_unpack (module YieldRunner) () with
   | () -> ()
   | effect Yield, k -> Effect.Deep.continue k ());
  assert (test_subst_unpack (module PureRunner) () = true);
  print_endline "6.3 OK"
