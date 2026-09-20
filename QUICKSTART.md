# Getting Started with OCaml Typed Effects

This branch (`typed_effects`) extends OCaml 5.6 with pure-by-default, row-polymorphic algebraic effect typing.

---

## 1. Quick Installation via OPAM

You can install this compiler and its ecosystem in an isolated OPAM switch:

```bash
# 1. Register the typed-effects OPAM repository
opam repo add typed-effects git+https://github.com/bluddy/opam-typed-effects.git --dont-select

# 2. Create an isolated switch with the compiler
opam switch create typed-effects --repositories=typed-effects,default ocaml-variants.5.6.0+typed-effects

# 3. Activate the environment
eval $(opam env)
ocamlc -v  # Output: The OCaml compiler, version 5.6.0+typed-effects

# 4. Install Dune and the standard library overlay
opam install dune stdlib_v2 -y
```

---

## 2. Building Your First Program

### Option A: Standalone File (using `ocamlopt`)

Create `test.ml`:

```ocaml
type _ Effect.t += Say : string -> unit Effect.t

let greet () =
  Effect.perform (Say "Hello, Typed Effects!")

let () =
  match greet () with
  | () -> ()
  | effect (Say msg), k ->
      print_endline msg;
      Effect.Deep.continue k ()
```

Compile and run:
```bash
ocamlopt -o test test.ml
./test
```

---

### Option B: Using Dune & `stdlib-v2`

Create a new directory:
```bash
mkdir my_effect_app && cd my_effect_app
```

Create `dune-project`:
```lisp
(lang dune 3.14)
(name my_effect_app)
```

Create `bin/dune`:
```lisp
(executable
 (name main)
 (libraries stdlib_v2))
```

Create `bin/main.ml`:
```ocaml
open Stdlib_v2

type _ Effect.t += Log : string -> unit Effect.t

let () =
  let handle f =
    match f () with
    | v -> v
    | effect (Log msg), k ->
        Printf.printf "[Effect Log] %s\n%!" msg;
        Effect.Deep.continue k ()
  in
  handle (fun () ->
    let numbers = [1; 2; 3; 4; 5] in
    let evens =
      List.filter (fun x ->
        Effect.perform (Log (Printf.sprintf "Inspecting %d" x));
        x mod 2 = 0
      ) numbers
    in
    List.iter (fun x ->
      Effect.perform (Log (Printf.sprintf "Found even: %d" x))
    ) evens
  )
```

Run your program:
```bash
dune exec ./bin/main.exe
```

---

## 3. Typed Effects Syntax Cheat Sheet

| Feature | Syntax | Explanation |
| :--- | :--- | :--- |
| **Pure arrow (default)** | `'a -> 'b` | Functions are pure by default ($\emptyset$). |
| **Explicit pure arrow** | `'a -[]-> 'b` | Syntactic alias for pure empty row. |
| **Specific effect arrow** | `'a -[ Log ]-> 'b` | Function may perform the `Log` effect. |
| **Effect-polymorphic arrow** | `'a -[ 'e ]-> 'b` | Arrow carrying a row variable `'e`. |
| **Multiple effects** | `'a -[ Log, Yield \| 'e ]-> 'b` | Row with labels and row extension variable `'e`. |
| **Effect declaration** | `type _ Effect.t += Eff : arg -> res Effect.t` | Extensible variant for effect constructors. |
| **Performing an effect** | `Effect.perform (Eff arg)` | Yields control to the enclosing ambient handler. |
| **Handling effects** | `match body () with`<br>`\| v -> v`<br>`\| effect (Eff x), k -> Effect.Deep.continue k res` | Deep pattern matching on effects with continuation `k`. |
| **Effectful Standard Library** | `open Stdlib_v2` | Overlays standard library modules (`List`, `Array`, `Option`, `Result`, `Seq`, `Fun`) with effect-polymorphic HOFs. |
