(* TEST
setup-ocamlc.byte-build-env;
ocamlc.byte;
check-ocamlc.byte-output;
run;
check-program-output;
*)
(* 1. Kind/Sort inference: parameter 'e is inferred as row by use in bracket *)
class ['a, 'e] reader (source : unit -['e]-> 'a) = object
  method next : 'a = source ()
end

(* Pure callback produces pure object *)
let pure_r = new reader (fun () -> 42)
(* Inferred type: ('a, -[ ]-) reader *)

(* 2. Locally polymorphic method inside class *)
class ['a] container (x : 'a) = object
  method map : 'e. ('a -['e]-> 'a) -['e]-> 'a =
    fun f -> f x
end

let () =
  assert (pure_r#next = 42);
  let c = new container 10 in
  assert (c#map (fun x -> x * 2) = 20);
  print_endline "6.5 OK"
