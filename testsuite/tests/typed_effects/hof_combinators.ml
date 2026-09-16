(* TEST
setup-ocamlc.byte-build-env;
ocamlc.byte;
check-ocamlc.byte-output;
run;
check-program-output;
*)
type _ Effect.t += Yield : unit Effect.t

(* Explicit polymorphism required on HOF signatures *)
let rec map : 'a 'b 'e. ('a -['e]-> 'b) -> 'a list -['e]-> 'b list =
  fun f -> function
  | [] -> []
  | x :: xs ->
      let y = f x in
      y :: map f xs

(* Pure callbacks instantiate map to a pure function *)
let test_pure_map xs = map (fun x -> x + 1) xs
(* Inferred type: int list -> int list (pure) *)

(* Effectful callbacks propagate their latent row *)
let test_eff_map xs = map (fun x -> Effect.perform Yield; x) xs
(* Inferred type: 'a list -[ Yield | 'e ]-> 'a list *)

let () =
  assert (test_pure_map [1; 2; 3] = [2; 3; 4]);
  let count = ref 0 in
  let run_yield f =
    match f () with
    | v -> v
    | effect Yield, k -> incr count; Effect.Deep.continue k ()
  in
  let res = run_yield (fun () -> test_eff_map [10; 20]) in
  assert (res = [10; 20]);
  assert (!count = 2);
  print_endline "6.4 OK"
