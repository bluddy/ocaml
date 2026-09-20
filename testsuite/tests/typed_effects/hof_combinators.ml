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
  let opt_fun ?loc ~x = function y -> y + x in
  let piped = 5 |> opt_fun ~x:10 in
  assert (piped = 15);
  let local_helper : 'a 'e. ('a -['e]-> int) -> 'a list -['e]-> int = fun f l ->
    let rec aux = function
      | [] -> 0
      | x :: xs -> f x + aux xs
    in
    aux l
  in
  let local_res = run_yield (fun () -> local_helper (fun x -> Effect.perform Yield; x) [1; 2]) in
  assert (local_res = 3);
  assert (!count = 4);
  (* Test multi-callback HOF combining pure and effectful callbacks sharing 'e *)
  let protect : 'a 'e. finally:(unit -['e]-> unit) -> (unit -['e]-> 'a) -['e]-> 'a =
    fun ~finally work ->
      let res =
        try work ()
        with exn ->
          finally ();
          raise exn
      in
      finally ();
      res
  in
  let finally_ran = ref false in
  let prot_res = run_yield (fun () ->
    protect
      ~finally:(fun () -> finally_ran := true)
      (fun () -> Effect.perform Yield; 42)
  ) in
  assert (prot_res = 42);
  assert (!finally_ran);
  assert (!count = 5);
  (* Test mutually recursive type alias with pure arrow thunk *)
  let module Seq_test = struct
    type +'a node = Nil | Cons of 'a * 'a t
    and 'a t = unit -> 'a node
    let empty () = Nil
    let return x () = Cons (x, empty)
  end in
  (match Seq_test.return 99 () with
  | Seq_test.Cons (x, next) ->
      assert (x = 99);
      assert (next () = Seq_test.Nil)
  | Seq_test.Nil -> assert false);
  print_endline "6.4 OK"
