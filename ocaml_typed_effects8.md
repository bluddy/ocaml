# Architectural Specification: Open-by-Default Row-Polymorphic Algebraic Effects for OCaml

This document outlines the mechanical, type-theoretic, and compiler additions required to integrate an open-by-default, row-polymorphic effect typing system into the upstream OCaml compiler.

---

## 1. Executive Principles & Design Compromises

1. **Ambient Delimited Control, Not Monads:** Avoids the 4-tier function coloring problem (Pure -> Concrete Monad -> Monad-Polymorphic -> MTL). Tier 4 multi-effect composition is the default baseline using direct-style syntax.
2. **Uniform Open-by-Default Arrows:** An unannotated arrow `->` uniformly desugars to an open row variable ($\forall \rho$) across all core terms and higher-order callbacks[cite: 3]. Standard ML libraries compose universally without manual annotations.
3. **Purity as Explicit Restriction:** Purity is never inferred implicitly for arrow syntax; it is an explicit assertion (`-->`, `-[ pure ]->`, or `-[ ]->`) applied to interfaces, critical sections, and invariant boundaries.
4. **Pragmatic Boundary (Zero Breaking Changes):**
   * **Tracked:** Algebraic effect yields (`Effect.perform`), delimited control jumps, fiber scheduling, dynamic keys (`Affect.Dynamic`)[cite: 5].
   * **Untracked / Ambient:** In-place heap mutation (`ref`, `Hashtbl`), native exceptions (`raise`, `try ... with`), memory allocations[cite: 1]. "Pure" means *algebraically closed and non-suspending*.
5. **Deterministic Unification (Lists, Not Sets):** Rows are structured association lists terminated with tail variables ($\rho$). Idempotence is structurally eliminated to preserve linear-time unification and principal types (single MGU).
6. **Rémy Presence/Absence Flags:** Negative constraints (`~Yield`) are modeled using three-point presence flags ($\mathbf{Pre}$, $\mathbf{Abs}$, $\delta$), reusing OCaml's polymorphic variant unification engine.
7. **Two-Tier Handlers (Deep vs. Shallow):** Handlers are distinguished by continuation semantics:
   * **Deep handlers** implicitly re-wrap resumed continuations, discharging effect debt via full row subtraction[cite: 3].
   * **Shallow handlers** detach upon intercepting the first effect, producing bare continuations that retain the effect label unless explicitly re-handled[cite: 3].
8. **Currying and Partial Evaluation Semantics:** Evaluating a function body is effectful; allocating an unapplied closure is pure. In curried pipelines, latent effects belong strictly to the arrow whose evaluation executes the effectful expression.
9. **Phase Distinction & Module Parameterization (`effect e`):** Functor parameters and module signatures cannot rely on floating, unconstrained row variables. Functors parameterized over effects declare abstract effect rows (`effect eff`) that are solved via sharing constraints (`with effect eff = ...`) or destructive substitutions (`with effect eff := ...`). Algorithmic interfaces (e.g. `Set.OrderedType`) and runtime callback references are explicitly annotated with pure arrows (`-->`).
10. **Subsystem Granularity via GADT Hierarchies:** To prevent row explosion and label collisions, complex subsystems (such as filesystems or network stacks) group their command grammar into a dedicated GADT, exposing a single coarse-grained algebraic effect label (`Fs`) carrying that GADT.

---

## 2. Formal Grammar and Calculus

### 2.1 Types, Rows, and Flags

$$\begin{aligned}
\text{Flags } \varphi &::= \mathbf{Pre} \mid \mathbf{Abs} \mid \delta \\
\text{Labels } \ell &\in \mathcal{L} \\
\text{Row Variables } \rho &\in \mathcal{V}_{\text{row}} \\
\text{Effect Rows } R &::= \emptyset \mid \rho \mid \langle \ell : \varphi \mid R \rangle \\
\text{Types } \tau &::= \alpha \mid \text{int} \mid \dots \mid \tau_1 \xrightarrow{R} \tau_2 \mid R
\end{aligned}$$

* $\mathbf{Pre}$: Label is definitely performed.
* $\mathbf{Abs}$: Label is statically forbidden (excluded).
* $\delta$: Presence of label is polymorphic.
* $\emptyset$: The closed, empty row (`pure`, `-[ ]-`, `-[ ]->`, or `-->`).

### 2.2 Syntax Equivalence & Desugaring

* **Pure Arrow Token (`-->`):**
  $$\tau_1 \longrightarrow \tau_2 \quad \equiv \quad \tau_1 \xrightarrow{\emptyset} \tau_2 \quad \equiv \quad \tau_1 \xrightarrow{[\;]} \tau_2 \quad \equiv \quad \tau_1 \xrightarrow{[\text{pure}]} \tau_2$$
* **Standalone Row Syntax (`-[ ... ]-`):**
  Extracts the row definition outside of the arrow constructor:
  $$\text{type } \text{'e db\_eff} = -[\, \text{Read}, \text{Write} \mid \text{'e} \,]-$$
  $$\text{type pure\_eff} = -[\, ]-$$
* **Anonymous Open Rows (`-[> ... ]-` and `-[> ... ]->`):**
  Syntactic sugar generating a fresh, unconstrained row variable $\rho_{\text{fresh}}$:
  $$-[\,> \ell_1, \ell_2 \,]- \quad \equiv \quad -[\, \ell_1, \ell_2 \mid \rho_{\text{fresh}} \,]-$$
  $$\tau_1 -[\,> \ell_1, \ell_2 \,]-> \tau_2 \quad \equiv \quad \tau_1 \xrightarrow{\langle \ell_1, \ell_2 \mid \rho_{\text{fresh}} \rangle} \tau_2$$
* **Separators:**
  * **Comma (`,`)** separates distinct effect labels: `-[ Read, Write ]-`.
  * **Pipe (`|`)** separates concrete labels from the row tail variable: `-[ Read, Write | 'e ]-`.
* **Label Commutativity:**
  $$\langle \ell_1 : \varphi_1 \mid \langle \ell_2 : \varphi_2 \mid R \rangle \rangle \cong \langle \ell_2 : \varphi_2 \mid \langle \ell_1 : \varphi_1 \mid R \rangle \rangle \quad (\text{if } \ell_1 \neq \ell_2)$$

---

## 3. Type Inference & Unification Rules

### 3.1 Higher-Order Auto-Lifting & Curried Arrow Structure

#### 3.1.1 Call-by-Value Currying vs. Closure Allocation
In call-by-value OCaml, partial application can execute arbitrary side effects if an effect expression is evaluated before returning the next closure:
```ocaml
let f = fun x -> Effect.perform Log; fun y -> x + y
```
* Intermediate arrows must **not** be hardcoded to pure (`-->`).
* **Function Definition Inference:** Each arrow $\tau_i \xrightarrow{R_i} \tau_{i+1}$ in a curried lambda chain collects the exact latent effects executed between the receipt of argument $x_i$ and the yield of the subsequent closure or final return value.
* **Callback Parameter Desugaring:** Unannotated arrows in higher-order parameter types generate **independent open row variables**:
  $$(\tau_1 \to \tau_2 \to \tau_3) \quad \Longrightarrow \quad (\tau_1 \xrightarrow{\rho_1} \tau_2 \xrightarrow{\rho_2} \tau_3)$$
  For standard multi-argument functions where closure allocation executes no effects, $\rho_1$ naturally unifies with $\emptyset$ via expression subsumption, while allowing staged or effectful partial applications to preserve their tracked effects.

#### 3.1.2 Class and Object Effect Parameters
Classes and class types explicitly declare their type and effect variables in their parameter list (`class ['a, 'e] reader ...`). The compiler distinguishes ordinary value types ($\star$) from effect rows ($\text{Row}_{\text{eff}}$) **by syntactic use / sort inference**:
* Parameters appearing in argument/return positions are value types ($\star$).
* Parameters appearing inside arrow effect brackets (`-['e]->` or `-[ ... | 'e ]-`) are effect rows ($\text{Row}_{\text{eff}}$).
* Unused phantom parameters default to standard value types.
* Individual object methods can use local universal quantification:
  ```ocaml
  method iter : 'e. ('a -['e]-> unit) -> unit -['e]-> unit
  ```

### 3.2 First-Order Deterministic Closed Rows
First-order computations infer ground, closed effect rows by unioning concrete tags:
$$\frac{\Gamma \vdash e_1 : \tau_1 \ / \ R_1 \quad \Gamma \vdash e_2 : \tau_2 \ / \ R_2}{\Gamma \vdash (e_1; e_2) : \tau_2 \ / \ R_1 \cup_{\text{concrete}} R_2}$$

### 3.3 Flag Unification & Expression Subsumption

#### Symmetric Unification Table ($\mathcal{U}$)
$$\begin{array}{rcccl}
\mathbf{Pre} &\sim& \mathbf{Pre} &\implies& \text{Success} \\
\mathbf{Abs} &\sim& \mathbf{Abs} &\implies& \text{Success} \\
\mathbf{Pre} &\sim& \mathbf{Abs} &\implies& \textbf{Compile Error (Negative Constraint Violated)} \\
\delta &\sim& \varphi &\implies& [\delta \mapsto \varphi]
\end{array}$$

#### Directional Expression Subsumption (`Ctype.effect_subsume`)
At value boundaries (e.g. pattern-match arm balancing, function arguments, functor arguments, and reference assignments `:=`), the compiler permits width subsumption:
$$\frac{R_1 \subseteq R_2}{(\tau_1 \xrightarrow{R_1} \tau_2) \le (\tau_1 \xrightarrow{R_2} \tau_2)}$$
Functions with fewer effects (such as pure `-->`) seamlessly coerce into contexts expecting more effects (such as `-[ Log ]->`), preventing spurious unification failures across distinct match branches and invariant container writes[cite: 4].

### 3.4 Elimination Rules: Deep vs. Shallow Handlers

For a delimited handler construct:
```ocaml
match e with
| x -> ret_body x
| effect (Eff payload) k -> eff_body payload k
```

#### Rule A: Deep Handlers (`Effect.Deep`)
A deep handler re-installs itself around the resumed continuation, enabling **row subtraction** ($R \setminus \ell$) on both the continuation $k$ and the overall match construct[cite: 3]. The continuation $k$ resumes execution of the inner expression until it produces the inner return type $\tau_1$:

$$\frac{\begin{aligned}
\Gamma \vdash e : \tau_1 \ / \ \langle \ell : \tau_{\text{arg}} \to \tau_{\text{res}} \mid R \rangle \quad & \quad k : \tau_{\text{res}} \xrightarrow{R} \tau_1 \\
\Gamma, x : \tau_1 \vdash \text{ret\_body} : \tau_{\text{out}} \ / \ R_{\text{ret}} \quad & \quad \Gamma, \text{payload} : \tau_{\text{arg}}, k : (\tau_{\text{res}} \xrightarrow{R} \tau_1) \vdash \text{eff\_body} : \tau_{\text{out}} \ / \ R_{\text{eff}}
\end{aligned}}{\Gamma \vdash (\text{match } e \text{ with } \dots) : \tau_{\text{out}} \ / \ (R \cup R_{\text{ret}} \cup R_{\text{eff}})}$$

* Label $\ell$ is removed from the continuation $k$ and the outer boundary[cite: 3].
* $k$ evaluates to the inner computation's return type $\tau_1$, which is subsequently transformed by the value clause (`ret_body`) to $\tau_{\text{out}}$.

#### Rule B: Shallow Handlers (`Effect.Shallow`)
A shallow handler intercepts only the initial effect emission and leaves the continuation bare[cite: 3]. Therefore, **label $\ell$ is NOT subtracted from $k$**[cite: 3]:

$$\frac{\begin{aligned}
\Gamma \vdash e : \tau_1 \ / \ \langle \ell : \tau_{\text{arg}} \to \tau_{\text{res}} \mid R \rangle \quad & \quad k : \tau_{\text{res}} \xrightarrow{\langle \ell \mid R \rangle} \tau_1 \\
\Gamma, x : \tau_1 \vdash \text{ret\_body} : \tau_{\text{out}} \ / \ R_{\text{ret}} \quad & \quad \Gamma, \text{payload} : \tau_{\text{arg}}, k : (\tau_{\text{res}} \xrightarrow{\langle \ell \mid R \rangle} \tau_1) \vdash \text{eff\_body} : \tau_{\text{out}} \ / \ R_{\text{eff}}
\end{aligned}}{\Gamma \vdash (\text{shallow\_match } e \text{ with } \dots) : \tau_{\text{out}} \ / \ (R \cup R_{\text{ret}} \cup R_{\text{eff}})}$$

* Resuming $k$ directly emits $\ell$ unless explicitly wrapped in another handler or recursive function[cite: 3].

### 3.5 Typing Higher-Order Functions with Handlers (Row Transformers)

When an HOF takes a callback, executes a handler, or performs its own effects:

$$\text{val transform} : (\alpha \xrightarrow{\langle \ell_{\text{in}} \mid \rho \rangle} \beta) \to \alpha \xrightarrow{\langle \ell_{\text{out}} \mid \rho \rangle} \beta$$

* $\ell_{\text{in}}$ is discharged by an internal deep handler.
* $\ell_{\text{out}}$ is emitted by the HOF.
* Ambient variable $\rho$ propagates undisturbed.

### 3.6 Application Peeling & Delayed Ambient Effect Emission
In multi-argument applications ($f \, a_1 \, a_2 \dots a_n$), premature unification of latent effect rows during argument peeling causes left-to-right constraint leakage (e.g. reverse piping via `|>`), improperly constraining argument expressions $a_i$ against ambient effects:
* The latent effect rows of peeled function arrows must be accumulated into a staging set: `delayed_apply_effects`.
* All argument subexpressions $a_1 \dots a_n$ are type-checked within their local lexical ambient scopes.
* The staged effects in `delayed_apply_effects` are unified into the ambient scope **only after all argument subexpressions have completed type-checking**.

---

## 4. OCaml Subsystems Integration

### 4.1 Covariance & The Relaxed Value Restriction
* The latent effect row on an arrow $\tau_1 \xrightarrow{R} \tau_2$ is strictly in a **covariant position**.
* Under Jacques Garrigue’s Relaxed Value Restriction, any row variable $\rho$ appearing exclusively in positive (covariant) positions within a non-value expression (e.g., partial applications `let f = List.map g`) is **generalized** ($\forall \rho$). It never monomorphizes into a weak row variable `'_e`.

### 4.2 Invariant Mutable State & Global Runtime Hooks
* Mutable containers (`'a ref`, `'a Atomic.t`, mutable record/array fields) are strictly invariant in their type parameter `'a`[cite: 4].
* Storing an unannotated arrow $\tau_1 \xrightarrow{\rho} \tau_2$ inside an invariant container traps row variable $\rho$ in an invariant position, preventing generalization under the relaxed value restriction and collapsing it into a monomorphic weak row variable `'_weak1`[cite: 4].
* **Explicit Annotations for Runtime Hooks:** Global hooks invoked out-of-band by the runtime system (e.g., `Printexc.register_printer`, custom formatters, GC alarm hooks) must be **explicitly annotated with closed pure arrows (`-->` or `-[ pure ]->`)**.
* **Subsumption at Assignment:** Assigning a function with fewer effects into an invariant container expecting more effects (e.g., assigning a pure function to an `(int -[ Log ]-> int) ref`) is sound via expression-level subsumption at the assignment site (`:=`), without altering container invariance[cite: 4].

### 4.3 GADTs, Existential Effect Rows, & Polymorphic Recursion
* When effect constructors wrap unannotated callbacks (e.g., `type _ eff += Spawn : (unit -> unit) -> unit eff`), the open row variable $\rho$ does not appear in the return type and is treated as an **existential type variable** ($\$a$).
* Pattern-matching and unpacking this existential inside a recursive handler (e.g., event loop or fiber scheduler) causes stock ML monomorphic recursion to reject the definition with:
  ```text
  The type constructor $a would escape its scope
  ```
* **Resolution:** Schedulers and runners unpacking existential callback rows must be typed using **explicit polymorphic recursion**:
  ```ocaml
  let rec corun : 'e. (unit -['e]-> unit) -> unit = fun f -> ...
  ```

### 4.4 Module Signatures, Functors, and Abstract Effects (`effect e`)
Module structure items (`struct ... end`) act as invariant boundaries during signature matching. To prevent weak variable pollution (`'_weak1`) during functor application, interfaces rely on explicit annotations, abstract effect declarations, or locally quantified variables:

1. **Abstract Effects in Module Types:**
   Module signatures declare abstract effect rows using the `effect` keyword:
   ```ocaml
   module type LOGGER = sig
     effect eff
     val log : string -[ eff ]-> unit
   end
   ```
2. **Module Equations (`=`) vs. Destructive Substitution (`:=`):**
   Functor constraints support both standard equality and destructive substitution:
   * **Equational Constraint (`with effect eff = ...`):**
     Preserves `eff` in the module type as a concrete manifest row:
     ```ocaml
     module M : LOGGER with effect eff = -[ Log ]-
     ```
   * **Destructive Substitution (`with effect eff := ...`):**
     Replaces all occurrences of `eff` throughout the signature with the target row and completely **erases** the `effect eff` item from the module type:
     ```ocaml
     module PureLogger : LOGGER with effect eff := -[ ]-
     (* Inferred signature: sig val log : string --> unit end *)
     ```
3. **Explicit Pure Algorithmic Interfaces:**
   Functor parameters requiring mathematical determinism (e.g., `Set.OrderedType`, `Map.OrderedType`, `Hashtbl.HashedType`) are **explicitly annotated as pure using `-->`**:
   ```ocaml
   module type OrderedType = sig
     type t
     val compare : t --> t --> int
   end
   ```
4. **Locally Polymorphic Higher-Order Callbacks:**
   When a module signature declares a higher-order combinator, the effect variable is universally quantified locally at the `val` specification:
   ```ocaml
   module type Iterable = sig
     type 'a t
     val iter : ('a -['e]-> unit) -> 'a t -['e]-> unit
   end
   ```

### 4.5 Subsystem Granularity: GADT Command Hierarchies
To prevent label explosion and name collisions in complex domains (e.g., filesystem, network, database), APIs must group operations into a command GADT carried by a single algebraic effect label:
```ocaml
module Fs = struct
  type _ cmd =
    | Open  : string * [ `Read | `Write ] -> int cmd
    | Read  : int * int                   -> bytes cmd
    | Write : int * bytes                 -> int cmd
    | Close : int                         -> unit cmd

  type _ Effect.t += Act : 'a cmd -> 'a Effect.t

  let read fd len = Effect.perform (Act (Read (fd, len)))
end
```

---

## 5. Concrete Compiler File Modifications

### `parsing/parsetree.mli`, `parsing/parser.mly`, & `parsing/lexer.mll`
* In `lexer.mll`:
  * Add token `PURE_ARROW` for `-->`. In type contexts, `-->` maps to `PURE_ARROW`.
  * Add tokens `LBRACKET_MINUS` (`-[`) and `MINUS_RBRACKET` (`]-`).
  * Add keyword `effect`.
* In `parsetree.mli`:
  * Update `core_type_desc` to support standalone effect rows and annotated arrows:
    ```ocaml
    type core_type_desc =
      | ...
      | Ptyp_arrow of arg_label * core_type * core_type * effect_row option
      | Ptyp_effect_row of effect_row
    and effect_row = {
      erow_labels : (string * presence_flag) list;
      erow_tail   : string option;
      erow_closed : bool;
      erow_anon   : bool; (* true for -[> ... ]- *)
    }
    and presence_flag = F_Present | F_Absent | F_Var of string
    ```
  * Update `signature_item_desc` and `with_constraint` to support `Psig_effect`, `Pwith_effect` (equality `=`), and `Pwith_effectsubst` (destructive substitution `:=`):
    ```ocaml
    type with_constraint =
      | ...
      | Pwith_effect of Longident.t Location.loc * effect_row
      | Pwith_effectsubst of Longident.t Location.loc * effect_row
    ```
* In `parser.mly`:
  * Add productions for `-->` (`PURE_ARROW`), desugaring to `{ erow_labels = []; erow_tail = None; erow_closed = true; erow_anon = false }`.
  * Add productions for standalone row syntax `-[ ... ]-` and anonymous open syntax `-[> ... ]-`.
  * Add grammar rules for `effect eff`, `with effect eff = ...`, and `with effect eff := ...`.

### `typing/types.ml` & `typing/btype.ml`
* Represent rows using `Btype.row_map` (reusing polymorphic variant engine).
* Store flags as `Pre`, `Abs`, or flexible flag variables.
* Support standalone row representation in type declarations (`type 'e db_eff = -[ Read | 'e ]-`).
* Add `sig_effect` to `Types.signature_item`.

### `typing/ctype.ml` & `typing/ctype.mli` (Unification Engine)
* Implement `unify_effect_rows`:
  1. Peel shared labels and verify flag compatibility (`Pre` vs `Abs` aborts).
  2. Instantiate open tail variables to remaining counterpart tails.
  3. Expand row aliases seamlessly during unification.
  4. Run occurs-check on row variables to prevent cyclic row constraints.
* Implement `Ctype.effect_subsume`: Directional row subsumption for value coercion at expression boundaries.

### `typing/typecore.ml`, `typing/typetexp.ml`, `typing/typeclass.ml`, & `typing/typemod.ml`
* In `typetexp.ml`:
  * Translate curried arrow sequences by assigning fresh, distinct open effect row variables to each unannotated arrow stage ($\tau_1 \xrightarrow{\rho_1} \tau_2 \xrightarrow{\rho_2} \dots$).
  * Desugar anonymous rows `-[> ... ]-` to fresh open row variables.
  * Translate `PURE_ARROW` (`-->`) to ground empty closed rows ($\emptyset$).
* In `typeclass.ml`:
  * Perform sort inference on class parameters: map parameters occurring in effect brackets to effect row kinds, and those in value positions to type kinds ($\star$).
  * Unused class parameters default to value types.
* In `typemod.ml`:
  * Implement checking and substitution for abstract effect declarations (`effect eff`).
  * Implement signature inclusion and constraint checking for `with effect eff = ...`.
  * Implement destructive substitution for `with effect eff := ...`, substituting the target row in all signature arrows and removing the `effect eff` item from the output signature.
* In `typecore.ml`:
  * On `Effect.perform eff`, extract label $\ell$ and register $\langle \ell : \mathbf{Pre} \mid \dots \rangle$ in current arrow scope.
  * In application peeling (`type_apply`), stage latent arrow effects in `delayed_apply_effects` buffer until all arguments are type-checked.
  * In `type_match`, handle `Effect.Deep` (subtractive $R \setminus \ell$ on continuation and expression) vs `Effect.Shallow` (retaining $\ell$ on continuation)[cite: 3].

### Standard Library Annotations (`stdlib/`)
* In `stdlib/set.mli`, `stdlib/map.mli`, `stdlib/hashtbl.mli`:
  * Explicitly annotate deterministic predicate signatures using pure arrows:
    ```ocaml
    module type OrderedType = sig
      type t
      val compare : t --> t --> int
    end
    ```
* In `stdlib/printexc.ml`, `stdlib/format.ml`:
  * Explicitly annotate out-of-band runtime hooks as pure:
    ```ocaml
    val register_printer : (exn --> string option) --> unit
    ```

### Tooling Integration (`ocamldoc/`, `testsuite/`)
* Extend pattern matching for `Teffect_row` across `odoc_value.ml`, `odoc_misc.ml`, and `odoc_str.ml`.
* Dedicated test suite: `testsuite/tests/typed_effects/` covering full feature matrices.

### `middle_end/flambda2/` (Optimizations)
* Detect tail-resumptive handlers where continuation $k$ is immediately resumed.
* Devirtualize handler frames: eliminate dynamic stack traversal (`caml_perform`) and rewrite operations into direct closure/register passing.
* Stack-allocate local handler state contexts using `@local` modes to eliminate GC heap churn[cite: 5, 6].

---

## 6. Comprehensive Verification & Edge Case Test Matrix

The test suite in `testsuite/tests/typed_effects/` must systematically exercise the combinations below to guard against regressions, weak variable traps, and phase-distinction leaks.

### 6.1 Modular Explicits & First-Class Modules (`modular_explicits.ml`)

```ocaml
(* 1. Unpacking pure first-class module parameter *)
module type PURE_ORD = sig
  type t
  val compare : t --> t --> int
end

let test_pure_unpack (type a) (module O : PURE_ORD with type t = a) (x : a) (y : a) : int =
  O.compare x y
(* Expect: val test_pure_unpack : (module PURE_ORD with type t = 'a) -> 'a --> 'a --> int *)

(* 2. Unpacking module with abstract effect equation *)
module type RUNNER = sig
  effect eff
  val step : unit -[ eff ]-> bool
end

let test_effect_unpack (module R : RUNNER with effect eff = -[ Yield ]-) () =
  if R.step () then Effect.perform Yield
(* Expect: val test_effect_unpack : (module RUNNER with effect eff = -[ Yield ]-) -> unit -[ Yield | 'e ]-> unit *)

(* 3. Destructive substitution on first-class module unpack *)
let test_subst_unpack (module R : RUNNER with effect eff := -[ ]-) () =
  R.step ()
(* Expect: val test_subst_unpack : (module RUNNER with effect eff := -[ ]) -> unit --> bool *)

(* 4. Packing module containing pure arrow with expression subsumption *)
module ConcreteInt = struct
  type t = int
  let compare x y = Int.compare x y
end
let packed_ord = (module ConcreteInt : PURE_ORD with type t = int)
```

### 6.2 Currying, Staging, & Application Peeling (`currying_staging.ml`)

```ocaml
type _ Effect.t += E1 : unit Effect.t | E2 : unit Effect.t

(* 1. True multi-stage effectful curried function *)
let staged = fun x ->
  Effect.perform E1;
  fun y ->
    Effect.perform E2;
    x + y
(* Expect: val staged : int -[ E1 ]-> int -[ E2 ]-> int *)

(* 2. Delayed application effect staging (Reverse Piping) *)
let perform_and_get () = Effect.perform E1; 42
let sink x y = x + y

(* Ensure delayed_apply_effects does not prematurely constrain 'perform_and_get ()' *)
let test_pipe () =
  perform_and_get () |> sink 10
(* Expect: val test_pipe : unit -[ E1 | 'e ]-> int *)

(* 3. Partial application without effects (pure closure allocation) *)
let normal_add x y = x + y
let partial = normal_add 5
(* Expect: val partial : int --> int *)
```

### 6.3 Classes, Objects, & Sort Inference (`class_sorts.ml`)

```ocaml
(* 1. Kind/Sort inference: parameter 'e is inferred as row by use *)
class ['a, 'e] reader (source : unit -['e]-> 'a) = object
  method next : unit -['e]-> 'a = source ()
end

(* Instantiation with pure callback *)
let pure_r = new reader (fun () -> 42)
(* Expect: ('a, -[ ]-) reader *)

(* Instantiation with effectful callback *)
let eff_r = new reader (fun () -> Effect.perform E1; 42)
(* Expect: ('a, -[ E1 | 'e ]-) reader *)

(* 2. Locally polymorphic method inside monomorphic class *)
class ['a] container (x : 'a) = object
  method map : 'e. ('a -['e]-> 'a) -> unit -['e]-> 'a =
    fun f -> f x
end

(* 3. Unused phantom parameter defaults to value type *)
class ['phantom] tagger = object
  method tag = 0
end
let _ = (new tagger : int tagger) (* Valid *)
```

### 6.4 Invariant State & Subsumption Boundaries (`mutable_state.ml`)

```ocaml
type _ Effect.t += Log : string -> unit Effect.t

(* 1. Assignment subsumption: pure function coerced into effectful reference *)
let r : (int -[ Log ]-> int) ref = ref (fun x -> Effect.perform (Log "hi"); x)
let () = r := (fun x -> x + 1) (* Allowed: -[]-> subsumes into -[ Log ]-> *)

(* 2. Invariance safety: must not generalize row variable inside mutable cell *)
let cell = ref (fun x -> x)
(* Expect: cell : ('_a -> '_a) ref (or monomorphic weak row variable, never generalized) *)

(* 3. Pure runtime hook registration *)
let my_printer (exn : exn) : string option = None
let () = Printexc.register_printer my_printer (* Compiles cleanly *)
```

### 6.5 Functors, Destructive Substitution, & Erasure (`functor_subst.ml`)

```ocaml
module type SERVICE = sig
  effect eff
  val compute : int -[ eff ]-> int
end

module Worker (S : SERVICE) = struct
  let run x = S.compute x
end

(* Equational functor application *)
module EffWorker = Worker(struct
  effect eff = -[ E1 ]-
  let compute x = Effect.perform E1; x
end)
(* Expect: val EffWorker.run : int -[ E1 ]-> int *)

(* Destructive substitution eliminates eff from signature *)
module type PURE_SERVICE = SERVICE with effect eff := -[ ]-
(* Expect signature: sig val compute : int --> int end *)

module PureWorker = Worker(struct
  effect eff = -[ ]-
  let compute x = x * 2
end)
(* Expect: val PureWorker.run : int --> int *)
```

### 6.6 Deep Handlers, Shallow Handlers, & Row Subtraction (`handlers_subtraction.ml`)

```ocaml
type _ Effect.t += Yield : unit Effect.t

(* 1. Deep handler: complete row subtraction *)
let comp () = Effect.perform Yield; 42

let test_deep () =
  match comp () with
  | v -> v
  | effect Yield k -> Effect.Deep.continue k ()
(* Expect: val test_deep : unit --> int (Yield completely subtracted) *)

(* 2. Shallow handler: continuation retains Yield *)
let test_shallow () =
  match comp () with
  | v -> None
  | effect Yield k ->
      (* k has type: unit -[ Yield | 'e ]-> int *)
      Some k
(* Expect: val test_shallow : unit --> (unit -[ Yield | 'e ]-> int) option *)

(* 3. Multi-effect peel and transform *)
type _ Effect.t += State_get : int Effect.t | State_put : int -> unit Effect.t

let run_state init f =
  let s = ref init in
  match f () with
  | v -> v
  | effect State_get k -> Effect.Deep.continue k !s
  | effect (State_put v) k -> s := v; Effect.Deep.continue k ()
(* Expect: val run_state : int -> (unit -[ State_get, State_put | 'e ]-> 'a) -['e]-> 'a *)
```

### 6.7 GADTs, Existentials, & Polymorphic Recursion (`gadts_existential.ml`)

```ocaml
type _ Effect.t += Fork : (unit -> unit) -> unit Effect.t

(* Recursive scheduler unpacking existential callback requires polymorphic recursion *)
let rec run_all : 'e. (unit -['e]-> unit) list -> unit = function
  | [] -> ()
  | task :: rest ->
      let spawned = ref [] in
      (match task () with
       | () -> ()
       | effect (Fork child) k ->
           spawned := child :: !spawned;
           Effect.Deep.continue k ());
      run_all (!spawned @ rest)
```

### 6.8 Interaction with Lazy & Recursive Modules (`lazy_rec_modules.ml`)

```ocaml
(* 1. Lazy computations defer effects until forced *)
let deferred = lazy (Effect.perform E1; 100)
let force_deferred () = Lazy.force deferred
(* Expect: val force_deferred : unit -[ E1 | 'e ]-> int *)

(* 2. Recursive module with abstract effect declaration *)
module rec M : sig
  effect eff
  val ping : int -[ eff ]-> int
end = struct
  effect eff = -[ E1 ]-
  let ping n =
    if n <= 0 then 0 else (Effect.perform E1; N.pong (n - 1))
end
and N : sig
  val pong : int -[ E1 ]-> int
end = struct
  let pong n = M.ping n
end
```

---

## 7. End-to-End Syntax Reference

```ocaml
(* 1. Universal Reuse: Compiler infers open polymorphic rows for curried callbacks *)
val fold_left : ('a -['e1]-> 'b -['e2]-> 'a) -> 'a -> 'b list -['e2]-> 'a

(* 2. Pure Arrow Shortcut (-->) *)
val pure_calc : int list --> int
val compare : 'a --> 'a --> int

(* 3. Standalone Row Aliases and Composition *)
type 'e db_eff = -[ Read, Write | 'e ]-
type 'e app_eff = -[ 'e db_eff, Metrics, Log ]-
val query : string -[ 'e db_eff ]-> result

(* 4. Anonymous Open Row Sugar (-[> ... ]-) *)
val send_telemetry : metric -> unit -[> Log, Net ]-> unit

(* 5. Subsystem Command Hierarchy (GADT) *)
module Fs = struct
  type _ cmd =
    | Read  : int * int   -> bytes cmd
    | Write : int * bytes -> int cmd
  type _ Effect.t += Act : 'a cmd -> 'a Effect.t
  val read : int -> int -[ Fs | 'e ]-> bytes
end

(* 6. Abstract Effect in Functor Interface with Destructive Substitution *)
module type LOGGER = sig
  effect eff
  val log : string -[ eff ]-> unit
end

module Make (L : LOGGER) = struct
  let run x =
    L.log "Working";
    x * 2
end

(* Equality Constraint: Preserves L.eff in signature *)
module ManifestInstance : (LOGGER with effect eff = -[ Log ]-) = struct
  effect eff = -[ Log ]-
  let log msg = Effect.perform (Log msg)
end

(* Destructive Substitution: Inlines row and erases 'eff' completely *)
module PureInstance : (LOGGER with effect eff := -[ ]-) = struct
  let log _ = ()
end
(* PureInstance has type: sig val log : string --> unit end *)

(* 7. Class Effect Parameter (Distinguished by Use) *)
class ['a, 'e] reader (source : unit -['e]-> 'a) = object
  method next : unit -['e]-> 'a = source ()
end

(* 8. Negative Exclusion Boundary (Non-Suspending Mode) *)
val run_atomic : (unit -[ ~Yield | 'e ]-> 'a) -['e]-> 'a

(* 9. Runtime Mutable Hook (Explicitly annotated closed pure arrow) *)
val custom_printers : (exn --> string option) list Atomic.t

(* 10. Scheduler Handling Existential Effects (Polymorphic Recursion) *)
val corun : 'e. (unit -['e]-> unit) -> unit

(* 11. Invariant Assignment Subsumption *)
val r : (int -[ Log ]-> int) ref = ref (fun x -> Effect.perform (Log x); x)
let () = r := fun x -> x + 42 (* Coerces pure --> into -[ Log ]-> *)
```