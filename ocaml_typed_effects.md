# Architectural Specification: Pure-by-Default Row-Polymorphic Algebraic Effects for OCaml

This document outlines the mechanical, type-theoretic, and compiler additions required to integrate a pure-by-default, row-polymorphic effect typing system into the upstream OCaml compiler[cite: 1].

---

## 1. Executive Principles & Design Compromises

1. **Ambient Delimited Control, Not Monads:** Avoids the 4-tier function coloring problem (Pure -> Concrete Monad -> Monad-Polymorphic -> MTL)[cite: 1]. Tier 4 multi-effect composition is the default baseline using direct-style syntax[cite: 1].
2. **Pure-by-Default Uniform Arrows:** An unannotated arrow `->` uniformly designates a **closed, pure function** ($\xrightarrow{\emptyset}$) across all expressions, type declarations, signatures, classes, and GADTs[cite: 1]. Purity is the baseline; algebraic effects are tracked capabilities explicitly represented via effect brackets (`-['e]->` or `-[ Eff ]->`)[cite: 1, 4].
3. **Equational Discipline on Higher-Order Signatures:** Because `->` is pure, higher-order combinators (such as `map` or `iter`) must explicitly declare effect polymorphism and variable sharing:
   $$\text{val map} : (\alpha \xrightarrow{\rho} \beta) \to \alpha \text{ list} \xrightarrow{\rho} \beta \text{ list}$$
   This guarantees that effect equality is syntactically manifest at interface boundaries rather than relying on context-dependent heuristic generation[cite: 1].
4. **Pragmatic Boundary (Zero Breaking Changes for Pure Code):**
   * **Tracked:** Algebraic effect yields (`Effect.perform`), delimited control jumps, fiber scheduling, dynamic keys (`Affect.Dynamic`)[cite: 1, 4, 5].
   * **Untracked / Ambient:** In-place heap mutation (`ref`, `Hashtbl`), native exceptions (`raise`, `try ... with`), memory allocations[cite: 1]. "Pure" means *algebraically closed and non-suspending*.
   * Existing pure OCaml code (data structures, math, algorithms, parser logic) compiles completely unchanged with 100% backward compatibility[cite: 1].
5. **Deterministic Unification (Lists, Not Sets):** Rows are structured association lists terminated with tail variables ($\rho$)[cite: 1]. Idempotence is structurally eliminated to preserve linear-time unification and principal types (single MGU)[cite: 1, 8].
6. **Rémy Presence/Absence Flags:** Negative constraints (`~Yield`) are modeled using three-point presence flags ($\mathbf{Pre}$, $\mathbf{Abs}$, $\delta$), reusing OCaml's polymorphic variant unification engine[cite: 1, 8].
7. **Two-Tier Handlers (Deep vs. Shallow):** Handlers are distinguished by continuation semantics:
   * **Deep handlers** implicitly re-wrap resumed continuations, discharging effect debt via row subtraction without forcing handled effects onto the inner computation[cite: 1, 4, 6].
   * **Shallow handlers** detach upon intercepting the first effect, producing bare continuations that retain the effect label unless explicitly re-handled[cite: 1, 4, 6].
8. **Bidirectional Subsumption at All Expected Contexts:** Implicit row subsumption ($R_{\text{actual}} \subseteq R_{\text{expected}}$) is integrated into `type_expect` in `typecore.ml`[cite: 1]. Passing pure or less-effectful functions into collections (`::`, arrays, queues), record fields, tuple positions, and function arguments automatically widens them without requiring explicit `:>` coercions[cite: 1, 9].
9. **Phase Distinction & Module Parameterization (`effect e`):** Functor parameters and module signatures declare abstract effect rows (`effect eff`) solved via sharing constraints (`with effect eff = ...`) or destructive substitutions (`with effect eff := ...`)[cite: 1, 4]. Algorithmic interfaces (e.g. `Set.OrderedType`) use default pure arrows `->` natively[cite: 1].
10. **Subsystem Granularity via GADT Hierarchies:** Complex subsystems group their command grammar into a dedicated GADT carried by a single algebraic effect label (`Fs`), preventing row explosion and label collision[cite: 1, 4].

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

* $\mathbf{Pre}$: Label is definitely performed[cite: 1].
* $\mathbf{Abs}$: Label is statically forbidden (excluded)[cite: 1].
* $\delta$: Presence of label is polymorphic[cite: 1].
* $\emptyset$: The closed, empty row[cite: 1].

### 2.2 Syntax Equivalence & Desugaring

* **Default Arrow (`->`):**
  $$\tau_1 \longrightarrow \tau_2 \quad \equiv \quad \tau_1 \xrightarrow{\emptyset} \tau_2 \quad \equiv \quad \tau_1 \xrightarrow{[\;]} \tau_2 \quad \equiv \quad \tau_1 \xrightarrow{[\text{pure}]} \tau_2$$
* **Effectful Arrow (`-[ ... ]->`):**
  $$\tau_1 -[\, \text{'e} \,]-> \tau_2 \quad \equiv \quad \tau_1 \xrightarrow{\rho} \tau_2$$
  $$\tau_1 -[\, \text{Log} \mid \text{'e} \,]-> \tau_2 \quad \equiv \quad \tau_1 \xrightarrow{\langle \text{Log} : \mathbf{Pre} \mid \rho \rangle} \tau_2$$
* **Standalone Row Syntax (`-[ ... ]-`):**
  Extracts row definitions outside arrow constructors[cite: 1]:
  $$\text{type } \text{'e db\_eff} = -[\, \text{Read}, \text{Write} \mid \text{'e} \,]-$$
  $$\text{type pure\_eff} = -[\, ]-$$
* **Anonymous Open Rows (`-[> ... ]-` and `-[> ... ]->`):**
  Syntactic sugar generating a fresh, unconstrained row variable $\rho_{\text{fresh}}$[cite: 1, 4]:
  $$-[\,> \ell_1, \ell_2 \,]- \quad \equiv \quad -[\, \ell_1, \ell_2 \mid \rho_{\text{fresh}} \,]-$$
  $$\tau_1 -[\,> \ell_1, \ell_2 \,]-> \tau_2 \quad \equiv \quad \tau_1 \xrightarrow{\langle \ell_1, \ell_2 \mid \rho_{\text{fresh}} \rangle} \tau_2$$
* **Separators:**
  * **Comma (`,`)** separates distinct effect labels: `-[ Read, Write ]-`[cite: 1].
  * **Pipe (`|`)** separates concrete labels from the row tail variable: `-[ Read, Write | 'e ]-`[cite: 1].
* **Label Commutativity:**
  $$\langle \ell_1 : \varphi_1 \mid \langle \ell_2 : \varphi_2 \mid R \rangle \rangle \cong \langle \ell_2 : \varphi_2 \mid \langle \ell_1 : \varphi_1 \mid R \rangle \rangle \quad (\text{if } \ell_1 \neq \ell_2)$$

---

## 3. Type Inference & Unification Rules

### 3.1 Function Definition & Purity Inference

1. **Unannotated Arrow Closures:** When typing `fun x -> expr`:
   * If `expr` performs zero effects, the inferred arrow type is closed pure: $\tau_1 \to \tau_2$ ($\tau_1 \xrightarrow{\emptyset} \tau_2$).
   * If `expr` performs effect $\ell$ in an open context, the inferred arrow type is $\tau_1 -[\ell \mid \rho]-> \tau_2$.
2. **Intermediate Closures in Curried Chains:**
   Evaluating a function body is effectful; allocating an intermediate unapplied closure is pure[cite: 1]. Latent effects belong strictly to the arrow whose evaluation executes the effect expression[cite: 1].
3. **Classes and Object Parameters:**
   Classes explicitly declare type and effect parameters (`class ['a, 'e] reader ...`)[cite: 1]. Syntactic sort inference distinguishes value types ($\star$) from effect rows ($\text{Row}_{\text{eff}}$) based on use in effect brackets[cite: 1]. Methods default to pure arrows `->` unless annotated with an effect row (`-['e]->` or universal univar `method m : 'e. ...`)[cite: 1].
4. **Type and GADT Declarations:**
   Because `->` is pure by default, constructors like `Fork : (unit -> unit) -> unit Effect.t` carry explicitly pure closures[cite: 1]. They introduce no unbound, floating existential row variables into the constructor[cite: 1].

### 3.2 Flag Unification & Bidirectional Expression Subsumption

#### Symmetric Unification Table ($\mathcal{U}$)
$$\begin{array}{rcccl}
\mathbf{Pre} &\sim& \mathbf{Pre} &\implies& \text{Success} \\
\mathbf{Abs} &\sim& \mathbf{Abs} &\implies& \text{Success} \\
\mathbf{Pre} &\sim& \mathbf{Abs} &\implies& \textbf{Compile Error (Negative Constraint Violated)} \\
\delta &\sim& \varphi &\implies& [\delta \mapsto \varphi]
\end{array}$$

#### Bidirectional Subsumption in `type_expect` (`typecore.ml`)
Whenever an expression $e$ is typed against an expected type $\tau_{\text{expected}}$ containing latent effect row $R_{\text{expected}}$:
$$\frac{\Gamma \vdash e \Rightarrow \tau_1 \xrightarrow{R_{\text{actual}}} \tau_2 \quad R_{\text{actual}} \subseteq R_{\text{expected}}}{\Gamma \vdash e \Leftarrow \tau_1 \xrightarrow{R_{\text{expected}}} \tau_2}$$

* **Universal Propagation:** Applies automatically to list elements (`x :: xs`, `[a; b]`), array elements, tuple and record fields, function arguments, and assignment expressions (`r := v`)[cite: 1, 9].
* Pure functions ($\emptyset$) and functions with fewer effects seamlessly widen into contexts expecting wider effect rows without requiring explicit `:>` coercions[cite: 1].

### 3.3 Elimination Rules: Deep vs. Shallow Handlers

For a delimited handler construct:
```ocaml
match e with
| x -> ret_body x
| effect (Eff payload), k -> eff_body payload k
```

#### Rule A: Deep Handlers (`Effect.Deep`)
A deep handler re-installs itself around the resumed continuation, enabling **row subtraction** ($R \setminus \ell$) on both the continuation $k$ and the overall match construct[cite: 1, 4]:

$$\frac{\begin{aligned}
\Gamma \vdash e : \tau_1 \ / \ R_{\text{body}} \quad & \quad k : \tau_{\text{res}} \xrightarrow{R_{\text{body}} \setminus \ell} \tau_1 \\
\Gamma, x : \tau_1 \vdash \text{ret\_body} : \tau_{\text{out}} \ / \ R_{\text{ret}} \quad & \quad \Gamma, \text{payload} : \tau_{\text{arg}}, k : (\tau_{\text{res}} \xrightarrow{R_{\text{body}} \setminus \ell} \tau_1) \vdash \text{eff\_body} : \tau_{\text{out}} \ / \ R_{\text{eff}}
\end{aligned}}{\Gamma \vdash (\text{match } e \text{ with } \dots) : \tau_{\text{out}} \ / \ ((R_{\text{body}} \setminus \ell) \cup R_{\text{ret}} \cup R_{\text{eff}})}$$

* **Pure Subtraction (No Forced Unification):** Handlers provide a capability; they do **not** mandate that the inner computation perform it[cite: 1]. The type checker must **never** call `unify_effect_rows` to force handled labels into $R_{\text{body}}$. If $\ell \notin R_{\text{body}}$, subtraction is an identity operation ($R_{\text{body}} \setminus \ell = R_{\text{body}}$)[cite: 1, 4].
* Continuation $k$ returns the inner computation's type $\tau_1$, which is transformed by the value clause (`ret_body`) to $\tau_{\text{out}}$[cite: 1, 4].

#### Rule B: Shallow Handlers (`Effect.Shallow`)
A shallow handler intercepts only the initial effect emission and leaves continuation $k$ bare[cite: 1, 4, 6]. Label $\ell$ is **not** subtracted from $k$[cite: 1, 4, 6]:

$$\frac{\begin{aligned}
\Gamma \vdash e : \tau_1 \ / \ R_{\text{body}} \quad & \quad k : \tau_{\text{res}} \xrightarrow{R_{\text{body}}} \tau_1 \\
\Gamma, x : \tau_1 \vdash \text{ret\_body} : \tau_{\text{out}} \ / \ R_{\text{ret}} \quad & \quad \Gamma, \text{payload} : \tau_{\text{arg}}, k : (\tau_{\text{res}} \xrightarrow{R_{\text{body}}} \tau_1) \vdash \text{eff\_body} : \tau_{\text{out}} \ / \ R_{\text{eff}}
\end{aligned}}{\Gamma \vdash (\text{shallow\_match } e \text{ with } \dots) : \tau_{\text{out}} \ / \ ((R_{\text{body}} \setminus \ell) \cup R_{\text{ret}} \cup R_{\text{eff}})}$$

#### Rule C: Per-Branch Existential Resumption Scoping (`typecore.ml`)
Because `Effect.t` is an extensible GADT indexed by resumption type (`'res Effect.t`)[cite: 1, 4], each pattern branch in `match e with effect ...` introduces an existential type index[cite: 1, 4]:
1. For each branch $i$ matching `effect pat, k`:
   * Allocate a **fresh, independent existential variable** $\alpha_{\text{res}}^{(i)}$[cite: 1, 4].
   * Type pattern `pat` against $\alpha_{\text{res}}^{(i)} \text{ Effect.t}$[cite: 1, 4].
   * Bind continuation $k$ in that branch's local environment with argument type $\alpha_{\text{res}}^{(i)}$[cite: 1, 4]:
     $$k : (\alpha_{\text{res}}^{(i)}, \tau_1) \text{ continuation}$$
2. **No Cross-Case Leakage:** Resumption variables $\alpha_{\text{res}}^{(i)}$ and $\alpha_{\text{res}}^{(j)}$ ($i \neq j$) must **never be unified together**[cite: 1].
3. **Escape Check:** Verify that $\alpha_{\text{res}}^{(i)}$ does not escape into the branch body's return type $\tau_{\text{out}}$ or outer environment[cite: 1].

### 3.4 Application Peeling & Delayed Ambient Effect Emission
In multi-argument applications ($f \, a_1 \, a_2 \dots a_n$), premature unification of latent effect rows during argument peeling causes left-to-right constraint leakage (e.g. reverse piping via `|>`), improperly constraining argument expressions $a_i$ against ambient effects[cite: 1]:
* Latent effect rows of peeled function arrows must be accumulated into a staging set: `delayed_apply_effects`[cite: 1].
* All argument subexpressions $a_1 \dots a_n$ are type-checked within their local lexical ambient scopes[cite: 1].
* Staged effects in `delayed_apply_effects` are unified into the ambient scope **only after all argument subexpressions have completed type-checking**[cite: 1].

---

## 4. OCaml Subsystems Integration

### 4.1 Covariance & The Relaxed Value Restriction
* Latent effect rows on arrows $\tau_1 \xrightarrow{R} \tau_2$ reside strictly in **covariant positions**[cite: 1, 9].
* Under the Relaxed Value Restriction, any row variable $\rho$ appearing exclusively in positive positions within a non-value expression (e.g., `let f = List.map g`) is **generalized** ($\forall \rho$)[cite: 1]. It never monomorphizes into a weak row variable `'_e`[cite: 1].

### 4.2 Invariant Mutable State & Global Runtime Hooks
* Mutable containers (`'a ref`, `'a Atomic.t`, mutable fields) are invariant in `'a`[cite: 1, 9].
* Storing an unannotated arrow `t1 -> t2` in a ref cell stores a closed, pure function ($\emptyset$)[cite: 1]. Because $\emptyset$ contains zero type variables, generalization succeeds completely with zero weak variables[cite: 1].
* **Subsumption at Assignment:** Assigning a pure function to an `(int -[ Log ]-> int) ref` succeeds via bidirectional subsumption in `type_expect`[cite: 1].
* Runtime hooks (`Printexc.register_printer`, formatters) accept pure `->` arrows naturally without special-case annotations[cite: 1].

### 4.3 GADTs, Existential Effect Rows, & Polymorphic Recursion
* Plain arrows inside GADT constructors default to pure (`->` = $\emptyset$), avoiding accidental existential variables[cite: 1].
* When an effect constructor deliberately carries an open callback (`Fork : 'e. (unit -['e]-> unit) -> unit Effect.t`), recursive handlers unpacking this existential are typed using explicit polymorphic recursion:
  ```ocaml
  let rec run_all : 'e. (unit -['e]-> unit) list -> unit = fun tasks -> ...
  ```

### 4.4 Module Signatures, Functors, and Abstract Effects (`effect e`)
* **Pure Default in Interfaces:** Functor parameters requiring determinism (`Set.OrderedType`, `Map.OrderedType`, `Hashtbl.HashedType`) write standard pure arrows `val compare : t -> t -> int`[cite: 1]. They contain zero floating variables, eliminating invariance friction[cite: 1].
* **Abstract Effects in Signatures:**
  ```ocaml
  module type LOGGER = sig
    effect eff
    val log : string -[ eff ]-> unit
  end
  ```
* **Sharing Constraints (`=`) vs. Destructive Substitution (`:=`):**
  * Equational (`with effect eff = ...`): Preserves `eff` in the module type[cite: 1, 4].
  * Destructive (`with effect eff := ...`): Inlines the row and erases `effect eff` completely from the resulting signature, cleanly collapsing arrows to pure `->` when instantiated with `-[ ]-`[cite: 1, 4].

---

## 5. Concrete Compiler File Modifications

### `parsing/parsetree.mli`, `parsing/parser.mly`, & `parsing/lexer.mll`
* In `lexer.mll`:
  * Add tokens `LBRACKET_MINUS` (`-[`) and `MINUS_RBRACKET` (`]-`)[cite: 1].
  * Add keyword `effect`[cite: 1].
* In `parsetree.mli`:
  * Update `core_type_desc` to support annotated arrows and standalone rows[cite: 1]:
    ```ocaml
    type core_type_desc =
      | ...
      | Ptyp_arrow of arg_label * core_type * core_type * effect_row option
      | Ptyp_effect_row of effect_row
    and effect_row = {
      erow_labels : (string * presence_flag) list;
      erow_tail   : string option;
      erow_closed : bool;
      erow_anon   : bool;
    }
    and presence_flag = F_Present | F_Absent | F_Var of string
    ```
  * Update `with_constraint` to support `Pwith_effect` (`=`) and `Pwith_effectsubst` (`:=`)[cite: 1].
* In `parser.mly`:
  * Plain `->` maps to `Ptyp_arrow (..., None)` (desugaring to closed pure row $\emptyset$)[cite: 1].
  * Add grammar rules for `-['e]->`, `-[ Log | 'e ]->`, `-[> ... ]->`, standalone `-[ ... ]-`, `effect eff`, and `with effect eff ...`[cite: 1].

### `typing/ctype.ml` & `typing/ctype.mli` (Unification Engine)
* Implement `unify_effect_rows`:
  1. Peel shared labels and verify flag compatibility (`Pre` vs `Abs` aborts)[cite: 1].
  2. Instantiate open tail variables to remaining counterpart tails[cite: 1].
  3. Expand row aliases during unification[cite: 1].
  4. Run occurs-check on row variables to prevent cyclic rows[cite: 1].
* Implement `Ctype.effect_subsume`: Directional row subsumption checking $R_1 \subseteq R_2$[cite: 1].

### `typing/typecore.ml`, `typing/typetexp.ml`, `typing/typeclass.ml`, & `typing/typemod.ml`
* In `typetexp.ml`:
  * Plain `->` translates to `Btype.empty_pure_row ()`[cite: 1].
  * Annotated arrows `-['e]->` translate to corresponding open/closed row variables[cite: 1].
* In `typecore.ml`:
  * In `type_expect`: Hook `Ctype.effect_subsume` so any expression synthesizing a narrower effect row automatically widens to an expected wider effect row across all checking positions[cite: 1].
  * In `type_effect_cases`:
    * Allocate a fresh, isolated existential type variable $\alpha_{\text{res}}$ for each pattern arm[cite: 1, 4].
    * Never unify the handled computation's row with the handler's effect labels[cite: 1].
    * Perform pure row subtraction ($R \setminus \ell$) on the computation's row[cite: 1, 4].
  * In application peeling (`type_apply`): Stage latent arrow effects in `delayed_apply_effects` buffer until all argument expressions are type-checked[cite: 1].
* In `typeclass.ml`:
  * Perform sort inference on class parameters: map parameters occurring in effect brackets to effect row kinds, and those in value positions to type kinds ($\star$)[cite: 1].
* In `typemod.ml`:
  * Implement signature inclusion and checking for `effect eff`, `with effect eff = ...`, and destructive substitution `with effect eff := ...`[cite: 1].

---

## 6. Comprehensive Verification & Edge Case Test Matrix

The test suite in `testsuite/tests/typed_effects/` must systematically exercise the combinations below[cite: 1].

### 6.1 Bidirectional Subsumption at Collection Boundaries (`subsumption_collections.ml`)

```ocaml
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
```

### 6.2 Pure Handlers & Row Subtraction (`handlers_subtraction.ml`)

```ocaml
type _ Effect.t += Yield : unit Effect.t

(* 1. Handler on pure computation does not force Yield *)
let run_pure () =
  match 42 with
  | v -> v
  | effect Yield, k -> Effect.Deep.continue k ()
(* Inferred type: val run_pure : unit -> int (completely pure) *)

(* 2. Handler on computation with rigid univar 'e subtracts Yield cleanly *)
let run_rigid (type e) (f : unit -[ Yield | e ]-> int) : int -[ e ]-> int =
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
```

### 6.3 Modular Explicits & First-Class Modules (`modular_explicits.ml`)

```ocaml
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
```

### 6.4 Higher-Order Combinators & Effect Equality (`hof_combinators.ml`)

```ocaml
(* Explicit polymorphism required on HOF signatures *)
val map : ('a -['e]-> 'b) -> 'a list -['e]-> 'b list

let rec map f = function
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
```

### 6.5 Classes, Objects, & Sort Inference (`class_sorts.ml`)

```ocaml
(* 1. Kind/Sort inference: parameter 'e is inferred as row by use in bracket *)
class ['a, 'e] reader (source : unit -['e]-> 'a) = object
  method next : unit -['e]-> 'a = source ()
end

(* Pure callback produces pure object *)
let pure_r = new reader (fun () -> 42)
(* Inferred type: ('a, -[ ]-) reader *)

(* 2. Locally polymorphic method inside class *)
class ['a] container (x : 'a) = object
  method map : 'e. ('a -['e]-> 'a) -> 'a -['e]-> 'a =
    fun f -> f x
end
```

### 6.6 GADTs & Existential Callbacks (`gadts_existential.ml`)

```ocaml
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
```

---

## 7. End-to-End Syntax Reference

```ocaml
(* 1. Pure by Default: Standard code is completely pure *)
val add : int -> int -> int
val compare : 'a -> 'a -> int
val pure_calc : int list -> int

(* 2. Higher-Order Effect Polymorphism: Explicit sharing *)
val map : ('a -['e]-> 'b) -> 'a list -['e]-> 'b list
val iter : ('a -['e]-> unit) -> 'a list -['e]-> unit

(* 3. Standalone Row Aliases and Composition *)
type 'e db_eff = -[ Read, Write | 'e ]-
type 'e app_eff = -[ 'e db_eff, Metrics, Log ]-
val query : string -[ 'e db_eff ]-> result

(* 4. Anonymous Open Sugar (-[> ... ]-) *)
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
  let run x = L.log "Working"; x * 2
end

(* Equality Constraint: Preserves L.eff in signature *)
module ManifestInstance : (LOGGER with effect eff = -[ Log ]-) = struct
  effect eff = -[ Log ]-
  let log msg = Effect.perform (Log msg)
end

(* Destructive Substitution: Inlines row and collapses to pure -> *)
module PureInstance : (LOGGER with effect eff := -[ ]-) = struct
  let log _ = ()
end
(* PureInstance has type: sig val log : string -> unit end *)

(* 7. Class Effect Parameter (Distinguished by Use) *)
class ['a, 'e] reader (source : unit -['e]-> 'a) = object
  method next : unit -['e]-> 'a = source ()
end

(* 8. Negative Exclusion Boundary (Non-Suspending Mode) *)
val run_atomic : (unit -[ ~Yield | 'e ]-> 'a) -['e]-> 'a

(* 9. Runtime Mutable Hook (Natural pure -> arrow) *)
val custom_printers : (exn -> string option) list Atomic.t

(* 10. Scheduler Handling Existential Effects (Polymorphic Recursion) *)
val run_all : 'e. (unit -['e]-> unit) list -> unit

(* 11. Bidirectional Container Subsumption *)
let q : (unit -[ Log ]-> unit) list = [ (fun () -> ()) ] (* Pure widens seamlessly *)
```