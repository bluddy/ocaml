(* TEST
setup-ocamlc.byte-build-env;
ocamlc.byte;
check-ocamlc.byte-output;
run;
check-program-output;
*)
type _ Effect.t += Fork : 'e. (unit -['e]-> unit) -> unit Effect.t

(* Recursive scheduler unpacking existential callback using polymorphic recursion *)
let rec run_all : 'e. (unit -['e]-> unit) list -> unit = function
  | [] -> ()
  | task :: rest ->
      let spawned = ref [] in
      (match task () with
       | () -> ()
       | effect (Fork child), k ->
           (* Bidirectional subsumption in type_expect accepts child without (:>) *)
           spawned := child :: !spawned;
           Effect.Deep.continue k ());
      run_all (!spawned @ rest)

let () =
  let trace = ref [] in
  let t1 () =
    trace := "t1_start" :: !trace;
    Effect.perform (Fork (fun () -> trace := "child1" :: !trace));
    trace := "t1_end" :: !trace
  in
  run_all [t1];
  assert (List.rev !trace = ["t1_start"; "t1_end"; "child1"]);
  print_endline "6.6 OK"
