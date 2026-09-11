(* TEST *)

open Effect
open Effect.Deep

type _ eff +=
  | Yield : int -> unit eff
  | Log : string -> unit eff

(* 1. Closed purity assertions: -[ pure ]-> and -[ ]-> *)
let pure_inc : int -[ pure ]-> int = fun x -> x + 1
let pure_dec : int -[ ]-> int = fun x -> x - 1

(* Inferred purity for unannotated lower-order function *)
let inferred_pure x = x * 2

let test_purity () =
  Printf.printf "Purity: %d %d %d\n"
    (pure_inc 10)
    (pure_dec 10)
    (inferred_pure 10)

(* 2. Assignment subsumption (Section 4.2):
   Assigning pure function into an invariant (int -[ Log ]-> int) ref *)
let test_assignment_subsumption () =
  let r : (int -[ Log ]-> int) ref = ref (fun x ->
    perform (Log "default");
    x
  ) in
  (* Subsumption at := assigns a pure function into ref expecting Log *)
  r := (fun x -> x + 42);
  let res = !r 10 in
  Printf.printf "Subsumption :=: %d\n" res

(* 3. Higher-Order Row Transformers (Section 3.5):
   Discharges Yield from callback while propagating ambient 'e *)
let run_yield (type a) (f : unit -[ Yield | 'e ]-> a) : unit -['e]-> (a * int list) =
  fun () ->
    let yielded = ref [] in
    let res =
      match_with f ()
        { retc = (fun v -> v);
          exnc = (fun e -> raise e);
          effc = (fun (type b) (eff : b eff) ->
            match eff with
            | Yield n -> Some (fun (k : (b, _) continuation) ->
                yielded := n :: !yielded;
                continue k ()
              )
            | _ -> None)
        }
    in
    (res, List.rev !yielded)

let test_row_transformer () =
  let comp () =
    perform (Yield 1);
    perform (Yield 2);
    perform (Yield 3);
    "done"
  in
  let transformer = run_yield comp in
  let (res, items) = transformer () in
  Printf.printf "Transformer: %s, [%s]\n"
    res
    (String.concat "; " (List.map string_of_int items))

(* 4. Negative exclusion constraints: -[ ~Yield | 'e ]-> *)
let call_without_yield : 'e. (unit -[ ~Yield | 'e ]-> string) -[ ~Yield | 'e ]-> string =
  fun f -> f ()

let test_exclusion () =
  let pure_fn () = "pure_no_yield" in
  let out1 = call_without_yield pure_fn in
  Printf.printf "Exclusion: %s\n" out1

(* 5. Deep handler vs Shallow handler semantics (Rule A & Rule B) *)
let test_handlers () =
  let deep_res =
    match perform (Yield 100) with
    | () -> 0
    | effect (Yield n), k -> continue k () + n
  in
  Printf.printf "Deep handler: %d\n" deep_res

let () =
  test_purity ();
  test_assignment_subsumption ();
  test_row_transformer ();
  test_exclusion ();
  test_handlers ()
