# Architectural Specification: Open-by-Default Row-Polymorphic Algebraic Effects for OCaml

This document outlines the mechanical, type-theoretic, and compiler additions required to integrate an open-by-default, row-polymorphic effect typing system into the upstream OCaml compiler.

---

## 1. Executive Principles & Design Compromises

1. **Ambient Delimited Control, Not Monads:** Avoids the 4-tier function coloring problem (Pure -> Concrete Monad -> Monad-Polymorphic -> MTL). Tier 4 multi-effect composition is the default baseline using direct-style syntax.
2. **Uniform Open-by-Default Arrows:** An unannotated arrow `->` uniformly desugars to an open row variable ($\forall \rho$) across all core terms and higher-order callbacks. Standard ML libraries compose universally without manual annotations.
3. **Purity as Explicit Restriction:** Purity is never inferred implicitly for arrow syntax; it is an explicit assertion (`-[ pure ]->` or `-[ ]->`) applied to interfaces, critical sections, and invariant boundaries.
4. **Pragmatic Boundary (Zero Breaking Changes):**
   * **Tracked:** Algebraic effect yields (`Effect.perform`), delimited control jumps, fiber scheduling, dynamic keys (`Affect.Dynamic`)[cite: 4].
   * **Untracked / Ambient:** In-place heap mutation (`ref`, `Hashtbl`), native exceptions (`raise`, `try ... with`), memory allocations. "Pure" means *algebraically closed and non-suspending*.
5. **Deterministic Unification (Lists, Not Sets):** Rows are structured association lists terminated with tail variables ($\rho$). Idempotence is structurally eliminated to preserve linear-time unification and principal types (single MGU).
6. **Rémy Presence/Absence Flags:** Negative constraints (`~Yield`) are modeled using three-point presence flags ($\mathbf{Pre}$, $\mathbf{Abs}$, $\delta$), reusing OCaml's polymorphic variant unification engine.
7. **Two-Tier Handlers (Deep vs. Shallow):** Handlers are distinguished by continuation semantics:
   * **Deep handlers** implicitly re-wrap resumed continuations, discharging effect debt via full row subtraction[cite: 2].
   * **Shallow handlers** detach upon intercepting the first effect, producing bare continuations that retain the effect label unless explicitly re-handled[cite: 2].
8. **Currying and Partial Evaluation Semantics:** Evaluating a function body is effectful; allocating an unapplied closure is pure. In curried pipelines, latent effects belong strictly to the arrow whose evaluation executes the effectful expression.
9. **Functors and Invariant Containers via Explicit Annotations:** Because module structure items (`struct ... end`) and mutable references are invariant, floating unconstrained effect rows collapse into weak variables (`'_weak1`). To prevent this, algorithmic functor interfaces (such as `Set.OrderedType`) and runtime callback hooks are **explicitly annotated** as pure (`-[]->`), while expression subsumption (`Ctype.effect_subsume`) permits pure implementations to satisfy them automatically.

---

## 2. Formal Grammar and Calculus

### 2.1 Types, Rows, and Flags

$$\begin{aligned}
\text{Flags } \varphi &::= \mathbf{Pre} \mid \mathbf{Abs} \mid \delta \\
\text{Labels } \ell &\in \mathcal{L} \\
\text{Row Variables } \rho &\in \mathcal{V}_{\text{row}} \\
\text{Effect Rows } R &::= \emptyset \mid \rho \mid \langle \ell : \varphi \mid R \rangle \\
\text{Types } \tau &::= \alpha \mid \text{int} \mid \dots \mid \tau_1 \xrightarrow{R} \tau_2
\end{aligned}$$

* $\mathbf{Pre}$: Label is definitely performed.
* $\mathbf{Abs}$: Label is statically forbidden (excluded).
* $\delta$: Presence of label is polymorphic.
* $\emptyset$: The closed, empty row (`pure` or `-[ ]->`).

### 2.2 Syntax Equivalence & Desugaring

* **Empty Row Alias:**
  $$\tau_1 \xrightarrow{\emptyset} \tau_2 \quad \equiv \quad \tau_1 \xrightarrow{[\;]} \tau_2 \quad \equiv \quad \tau_1 \xrightarrow{[\text{pure}]} \tau_2$$
* **Label Commutativity:**
  $$\langle \ell_1 : \varphi_1 \mid \langle \ell_2 : \varphi_2 \mid R \rangle \rangle \cong \langle \ell_2 : \varphi_2 \mid \langle \ell_1 : \varphi_1 \mid R \rangle \rangle \quad (\text{if } \ell_1 \neq \ell_2)$$
* **Well-Formedness:** Each label $\ell$ occurs at most once per lexical row chain.

---

## 3. Type Inference & Unification Rules

### 3.1 Higher-Order Auto-Lifting & Curried Arrow Structure

#### 3.1.1 Call-by-Value Currying vs. Closure Allocation
In call-by-value OCaml, partial application can execute arbitrary side effects if an effect expression is evaluated before returning the next closure:
```ocaml
let f = fun x -> Effect.perform Log; fun y -> x + y
```
* Intermediate arrows must **not** be artificially forced to pure (`-[]->`).
* **Function Definition Inference:** Each arrow $\tau_i \xrightarrow{R_i} \tau_{i+1}$ in a curried lambda chain collects the exact latent effects executed between the receipt of argument $x_i$ and the yield of the subsequent closure or final return value.
* **Callback Parameter Desugaring:** Unannotated arrows in higher-order parameter types generate **independent open row variables**:
  $$(\tau_1 \to \tau_2 \to \tau_3) \quad \Longrightarrow \quad (\tau_1 \xrightarrow{\rho_1} \tau_2 \xrightarrow{\rho_2} \tau_3)$$
  For standard multi-argument functions where closure allocation executes no effects, $\rho_1$ naturally unifies with $\emptyset$ via expression subsumption, while allowing staged or effectful partial applications to preserve their tracked effects.

#### 3.1.2 Object & Class Methods
Method implementations infer concrete effect rows from their bodies. However, unconstrained ambient effect variables in virtual class method declarations must be closed via `close_unconstrained_effect_rows` before `closed_class` validation runs, ensuring abstract interfaces do not leak unbound row variables.

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
At value boundaries (e.g. pattern-match arm balancing, function arguments, and reference assignments `:=`), the compiler permits width subsumption:
$$\frac{R_1 \subseteq R_2}{(\tau_1 \xrightarrow{R_1} \tau_2) \le (\tau_1 \xrightarrow{R_2} \tau_2)}$$
Functions with fewer effects (such as pure `-[]->`) seamlessly coerce into contexts expecting more effects (such as `-[ Log ]->`), preventing spurious unification failures across distinct match branches and invariant container writes.

### 3.4 Elimination Rules: Deep vs. Shallow Handlers

For a delimited handler construct:
```ocaml
match e with
| x -> ret_body x
| effect (Eff payload) k -> eff_body payload k
```

#### Rule A: Deep Handlers (`Effect.Deep`)
A deep handler re-installs itself around the resumed continuation, enabling **row subtraction** ($R \setminus \ell$) on both the continuation $k$ and the overall match construct[cite: 2]. The continuation $k$ resumes execution of the inner expression until it produces the inner return type $\tau_1$:

$$\frac{\begin{aligned}
\Gamma \vdash e : \tau_1 \ / \ \langle \ell : \tau_{\text{arg}} \to \tau_{\text{res}} \mid R \rangle \quad & \quad k : \tau_{\text{res}} \xrightarrow{R} \tau_1 \\
\Gamma, x : \tau_1 \vdash \text{ret\_body} : \tau_{\text{out}} \ / \ R_{\text{ret}} \quad & \quad \Gamma, \text{payload} : \tau_{\text{arg}}, k : (\tau_{\text{res}} \xrightarrow{R} \tau_1) \vdash \text{eff\_body} : \tau_{\text{out}} \ / \ R_{\text{eff}}
\end{aligned}}{\Gamma \vdash (\text{match } e \text{ with } \dots) : \tau_{\text{out}} \ / \ (R \cup R_{\text{ret}} \cup R_{\text{eff}})}$$

* Label $\ell$ is removed from the continuation $k$ and the outer boundary[cite: 2].
* $k$ evaluates to the inner computation's return type $\tau_1$, which is subsequently transformed by the value clause (`ret_body`) to $\tau_{\text{out}}$.

#### Rule B: Shallow Handlers (`Effect.Shallow`)
A shallow handler intercepts only the initial effect emission and leaves the continuation bare[cite: 2]. Therefore, **label $\ell$ is NOT subtracted from $k$**[cite: 2]:

$$\frac{\begin{aligned}
\Gamma \vdash e : \tau_1 \ / \ \langle \ell : \tau_{\text{arg}} \to \tau_{\text{res}} \mid R \rangle \quad & \quad k : \tau_{\text{res}} \xrightarrow{\langle \ell \mid R \rangle} \tau_1 \\
\Gamma, x : \tau_1 \vdash \text{ret\_body} : \tau_{\text{out}} \ / \ R_{\text{ret}} \quad & \quad \Gamma, \text{payload} : \tau_{\text{arg}}, k : (\tau_{\text{res}} \xrightarrow{\langle \ell \mid R \rangle} \tau_1) \vdash \text{eff\_body} : \tau_{\text{out}} \ / \ R_{\text{eff}}
\end{aligned}}{\Gamma \vdash (\text{shallow\_match } e \text{ with } \dots) : \tau_{\text{out}} \ / \ (R \cup R_{\text{ret}} \cup R_{\text{eff}})}$$

* Resuming $k$ directly emits $\ell$ unless explicitly wrapped in another handler or recursive function[cite: 2].

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
* Mutable containers (`'a ref`, `'a Atomic.t`, mutable record/array fields) are strictly invariant in their type parameter `'a`[cite: 5].
* Storing an unannotated arrow $\tau_1 \xrightarrow{\rho} \tau_2$ inside an invariant container traps row variable $\rho$ in an invariant position, preventing generalization under the relaxed value restriction and collapsing it into a monomorphic weak row variable `'_weak1`[cite: 5].
* **Explicit Annotations for Runtime Hooks:** Global hooks invoked out-of-band by the runtime system (e.g., `Printexc.register_printer`, custom formatters, GC alarm hooks) must be **explicitly annotated with closed pure arrows (`-[]->` or `-[ pure ]->`)**. This eliminates type variables and prevents weak variable formation.
* **Subsumption at Assignment:** Assigning a function with fewer effects into an invariant container expecting more effects (e.g., assigning a pure function to an `(int -[ Log ]-> int) ref`) is sound via expression-level subsumption at the assignment site (`:=`), without altering container invariance[cite: 5].

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
  This instantiates a fresh polymorphic row variable at each recursive call site, preventing existential row escape.

### 4.4 Object & Class Systems
* Unconstrained ambient effect rows in virtual class definitions are closed via `close_unconstrained_effect_rows` before `closed_class` validation runs.
* Prevents spurious unbound type variable errors across virtual method interfaces while preserving effect tracking on concrete object methods.

### 4.5 Functors and Explicitly Annotated Interfaces
Module structure items (`struct ... end`) act as invariant boundaries during signature matching. To prevent weak variable pollution (`'_weak1`) during functor application, interfaces are handled via explicit annotations and locally scoped variables:

1. **Explicitly Pure Algorithmic Interfaces:**
   Functor parameters requiring mathematical determinism (such as `Set.OrderedType`, `Map.OrderedType`, and `Hashtbl.HashedType`) must be **explicitly annotated in the standard library as pure (`-[]->`)**:
   ```ocaml
   module type OrderedType = sig
     type t
     val compare : t -[ ]-> t -[ ]-> int
   end
   ```
   Because these annotations are ground and closed ($\emptyset$), they contain zero type variables, eliminating invariance friction and preventing `'_weak1` variable generation when instantiating functors (e.g. `Set.Make(struct ... end)`). Any standard pure comparison implementation satisfies this interface automatically via `Ctype.effect_subsume`.
2. **Locally Polymorphic Higher-Order Callbacks:**
   When a module signature declares a higher-order combinator, the effect variable is universally quantified locally at the `val` specification:
   ```ocaml
   module type Iterable = sig
     type 'a t
     val iter : ('a -['e]-> unit) -> 'a t -['e]-> unit
   end
   ```
   Because `'e` is quantified per call site, no free variable is trapped in the module struct.

---

## 5. Concrete Compiler File Modifications

### `parsing/parsetree.mli` & `parsing/parser.mly`
* Update `core_type_desc` to include optional effect rows on arrow nodes:
  ```ocaml
  type core_type_desc =
    | ...
    | Ptyp_arrow of arg_label * core_type * core_type * effect_row option
  and effect_row = {
    erow_labels : (string * presence_flag) list;
    erow_tail   : string option;
    erow_closed : bool;
  }
  and presence_flag = F_Present | F_Absent | F_Var of string
  ```
* Parse `-[ ]->` and `-[ pure ]->` as closed empty rows: `{ erow_labels = []; erow_tail = None; erow_closed = true }`.
* Parse `-[ ~Yield | 'e ]->` as negative exclusion (`F_Absent`).

### `typing/types.ml` & `typing/btype.ml`
* Represent rows using `Btype.row_map` (reusing polymorphic variant engine).
* Store flags as `Pre`, `Abs`, or flexible flag variables.

### `typing/ctype.ml` & `typing/ctype.mli` (Unification Engine)
* Implement `unify_effect_rows`:
  1. Peel shared labels and verify flag compatibility (`Pre` vs `Abs` aborts).
  2. Instantiate open tail variables to remaining counterpart tails.
  3. Run occurs-check on row variables to prevent cyclic row constraints.
* Implement `Ctype.effect_subsume`: Directional row subsumption for value coercion at expression boundaries.
* Implement `close_unconstrained_effect_rows`: Closes floating effect rows in class types before closedness checks.

### `typing/typecore.ml`, `typing/typetexp.ml`, & `stdlib/`
* In `typetexp.ml`:
  * Translate curried arrow sequences by assigning fresh, distinct open effect row variables to each unannotated arrow stage ($\tau_1 \xrightarrow{\rho_1} \tau_2 \xrightarrow{\rho_2} \dots$).
  * Remove any ad-hoc hacks that force intermediate callback arrows to `-[]->`, allowing effectful partial applications (`fun x -> Effect; fun y -> ...`) to type soundly.
* In `stdlib/` (e.g. `stdlib/set.mli`, `stdlib/map.mli`, `stdlib/printexc.ml`):
  * **Explicitly annotate** mathematical predicate signatures with closed pure arrows (`val compare : t -[ ]-> t -[ ]-> int`).
  * **Explicitly annotate** runtime callback references with closed pure arrows (`(exn -[ pure ]-> string option) list Atomic.t`).
* On `Effect.perform eff`, extract label $\ell$ and register $\langle \ell : \mathbf{Pre} \mid \dots \rangle$ in current arrow scope.
* In application peeling (`type_apply` / argument dispatch):
  * Introduce `delayed_apply_effects` buffer to stage latent arrow effects until all argument expressions are type-checked.
* Hook `Ctype.effect_subsume` into `unify_exp_types` for arm matching, functor arguments, and assignment (`:=`).
* In `type_match`, differentiate between `Effect.Deep` and `Effect.Shallow`:
  * **Deep:** Assign continuation $k : \tau_{\text{res}} \xrightarrow{R} \tau_1$ and strip label $\ell$ from the outer scope ($R \setminus \ell$)[cite: 2].
  * **Shallow:** Assign continuation $k : \tau_{\text{res}} \xrightarrow{\langle \ell \mid R \rangle} \tau_1$, retaining label $\ell$ on $k$[cite: 2].

### Tooling Integration (`ocamldoc/`, `testsuite/`)
* Extend pattern matching for `Teffect_row` across `odoc_value.ml`, `odoc_misc.ml`, and `odoc_str.ml`.
* Dedicated test suite: `testsuite/tests/typed_effects/` verifying closed purity, assignment subsumption, HOF transformers, negative exclusion, effectful partial applications, functor parameter instantiation (`Set.Make`), and deep handler row subtraction.

### `middle_end/flambda2/` (Optimizations)
* Detect tail-resumptive handlers where continuation $k$ is immediately resumed.
* Devirtualize handler frames: eliminate dynamic stack traversal (`caml_perform`) and rewrite operations into direct closure/register passing.
* Stack-allocate local handler state contexts using `@local` modes to eliminate GC heap churn[cite: 4, 6].

---

## 6. End-to-End Syntax Reference

```ocaml
(* 1. Universal Reuse: Compiler infers open polymorphic rows for curried callbacks *)
val fold_left : ('a -['e1]-> 'b -['e2]-> 'a) -> 'a -> 'b list -['e2]-> 'a

(* 2. Partial Application with Effects *)
val stage_query : db -[ Prepare ]-> query -[ Exec ]-> result

(* 3. Opt-in Closed Purity (Empty row syntax and alias) *)
val pure_calc : int list -[ ]-> int
val pure_calc : int list -[ pure ]-> int

(* 4. Negative Exclusion Boundary (Jane Street Non-Suspending Mode) *)
val run_atomic : (unit -[ ~Yield | 'e ]-> 'a) -['e]-> 'a

(* 5. HOF Row Transformer (Discharging State, Emitting Log) *)
val run_and_log : ('s -> unit -[ State | 'e ]-> 'a) -> 's -[ Log | 'e ]-> 'a

(* 6. Shallow Handler Stepper (k retains Yield unless handled) *)
val step_generator : 
  (unit -[ Yield | 'e ]-> unit) -> 
  (unit -[ Yield | 'e ]-> unit) option

(* 7. Runtime Mutable Hook (Explicitly annotated closed ground pure arrow) *)
val custom_printers : (exn -[ pure ]-> string option) list Atomic.t

(* 8. Functor Predicate Interface (Explicitly annotated closed pure arrows) *)
module type OrderedType = sig
  type t
  val compare : t -[ ]-> t -[ ]-> int
end

(* 9. Locally Quantified Higher-Order Functor Argument *)
module type Iterable = sig
  type 'a t
  val iter : ('a -['e]-> unit) -> 'a t -['e]-> unit
end

(* 10. Scheduler Handling Existential Effects (Polymorphic Recursion) *)
val corun : 'e. (unit -['e]-> unit) -> unit

(* 11. Invariant Assignment Subsumption *)
val r : (int -[ Log ]-> int) ref = ref (fun x -> Effect.perform (Log x); x)
let () = r := fun x -> x + 42 (* Coerces pure -[]-> into -[ Log ]-> *)
```