# Lean, From First Principles — How a Senior Developer Should Answer
*(with code examples)*

The framing throughout: **what problem exists in formal mathematics / verified software (usually solved badly, or not at all, by informal proofs and untyped or weakly-typed code) that this Lean feature exists to fix, and what the type checker is actually doing when it accepts your code.** A junior answer defines the syntax. A senior answer explains what proposition a piece of code *is*, and why the kernel believes it.

---

## 0. The One Sentence First

Rust asks "how do I get memory safety without a GC." Noir asks "how do I compile a program into a zero-knowledge circuit." Lean asks something more fundamental: **"how do I make 'this proof is correct' a mechanically checkable fact, using the same type-checking machinery a programming language already needs to check that a program compiles."** Lean's core move — **propositions are types, and proofs are programs** (Curry–Howard) — means there is no separate "proof language" bolted onto a "programming language." Writing `2 + 2 = 4` and proving it, and writing a sorting function and proving it terminates and is correct, are literally the same activity: constructing a term of a type, checked by the same kernel. Nearly every feature below exists as a specific instance of that one idea.

---

## 1. Lean Fundamentals

**Everything is a term of a type** — `def`, `theorem`, `example`, `lemma` are all, underneath, the same construct: give a name to a term, and let the compiler check the term's type matches the declared type. This exists because Lean draws no hard boundary between "code" and "proof" — `theorem` is really just `def` where the declared type happens to be a `Prop` (see Section 2). A senior answer opens here, because it reframes every other feature: a "proof" is not a separate artifact the compiler verifies against your code — it *is* code, verified the same way.

```lean
def double (n : Nat) : Nat := n + n

theorem double_eq_two_mul (n : Nat) : double n = 2 * n := by
  simp [double, Nat.two_mul]
-- `def` and `theorem` are the same keyword in spirit: both check
-- that the term on the right has the type on the left.
```

**`#check` / `#eval`** — `#check e` asks the elaborator for `e`'s type without running or proving anything; `#eval e` actually *evaluates* `e` (Lean is also a real, compiled, general-purpose programming language, not just a proof assistant). This split exists because in a dependently-typed system, "what type does this have" and "what does this reduce to" are both meaningful, separate questions you constantly need answered while developing — types can themselves contain expressions that need evaluating to be understood.

```lean
#check (double 3)      -- Nat
#eval  (double 3)      -- 6
#check @double         -- Nat → Nat
```

**Variables and `let`** — Like Rust, bindings are immutable by default (`let x := 5` introduces a term, not a mutable memory cell) — but the reason is stronger here than in Rust's "reduce accidental mutation" case: Lean terms are mathematical objects, and mathematical objects don't get reassigned. What looks like "mutation" in tactic-mode proofs (rewriting a hypothesis) is really "produce a new term/goal and discard the old one," exactly like Rust's shadowing, never in-place mutation of a value the type system is reasoning about.

```lean
def example1 : Nat :=
  let x := 5
  let y := x + 1
  x + y  -- 11 — `x` was never "changed," `y` is just a new term built from it
```

**Functions** — Standard-looking, but every function is, underneath, a term built from `fun`/lambda — `def f (n : Nat) : Nat := n + 1` desugars to `def f : Nat → Nat := fun n => n + 1`. This exists because Lean's core calculus (the Calculus of Inductive Constructions) has exactly one function-abstraction mechanism; `def`'s named-argument syntax is convenient sugar over that one primitive, not a separate concept.

```lean
def add1 (n : Nat) : Nat := n + 1
def add1' : Nat → Nat := fun n => n + 1  -- exactly the same term
```

**Expressions vs. tactics — two modes of writing a proof** — Lean lets you build a proof term two ways: **term mode** (write the proof directly, as an expression, the way you'd write any other value) or **tactic mode** (`by ...`, a sequence of goal-transforming commands that *generates* a term for you). This split exists because some proofs are genuinely easier to state directly as a data structure (a short calculation, a direct application of a lemma) while others are easier to build incrementally by chipping away at a goal (case splits, induction, rewriting) — tactic mode is not a different kind of proof, it's a different *authoring interface* to the same underlying term.

```lean
-- term mode: write the proof term directly
theorem add_comm3 (a b : Nat) : a + b = b + a := Nat.add_comm a b

-- tactic mode: describe a sequence of steps; Lean assembles the term for you
theorem add_comm3' (a b : Nat) : a + b = b + a := by
  rw [Nat.add_comm]
```

---

## 2. `Prop`, `Type`, and Curry–Howard ⭐

**The single most important idea in the whole language, and the one a senior candidate must be able to state precisely.** Under Curry–Howard, a **proposition is a type**, and a **proof is a term of that type**. `2 + 2 = 4` is not a boolean-valued expression you evaluate — it is itself a *type*, namely the type of "proofs that 2+2=4," and `rfl` is a term (the trivial proof, "reflexivity") that inhabits it. "Is this proof valid" and "does this term type-check" are, at the kernel level, literally the same question. This exists because it lets Lean reuse its entire type-checking engine — the same one that checks your `Nat → Nat` function is well-typed — as the proof-checking engine, with zero additional machinery.

```lean
-- `2 + 2 = 4` is a Prop — a type. `rfl` is a term that inhabits it — a proof.
theorem two_plus_two : 2 + 2 = 4 := rfl

-- Implication is a function type: a proof of P → Q is literally a function
-- from proofs-of-P to proofs-of-Q.
theorem modus_ponens {P Q : Prop} (h1 : P → Q) (h2 : P) : Q := h1 h2
```

**`Prop` vs. `Type`** — Both are "types of types," but `Prop` is the universe of propositions specifically, with one crucial extra rule: **proof irrelevance** — any two proofs of the same proposition are considered definitionally equal, because *which* proof you have never matters, only *that* one exists. `Type` (and `Type 1`, `Type 2`, ... — see Universes) is for everything else: actual data you compute with, where *which* value you have very much matters. This split exists so the compiler can safely erase all proof terms at compile time (they carry zero runtime information, by proof irrelevance) while still keeping ordinary data around — proofs are free at runtime precisely because `Prop` guarantees they carry no distinguishing information.

```lean
-- Both `h1` and `h2` prove the same Prop, and Lean considers them equal —
-- proof irrelevance means the *content* of a proof term never matters.
example : (2 : Nat) = 2 := rfl
example : (2 : Nat) = 2 := Eq.refl 2
-- these two proofs are interchangeable everywhere; a Nat is not the same —
-- 2 and 3 : Nat are genuinely different data, not proof-irrelevant.
```

**Decidable propositions (`Decidable`)** — Not every `Prop` can be checked by a boolean algorithm (some are undecidable, some are just not yet decided by any instance), but many can — `Decidable p` packages "either a proof of `p` or a proof of `¬p`, computed algorithmically." This exists to bridge `Prop` (mathematical truth) and `Bool` (something you can branch on / evaluate at runtime) — `if h : p then ... else ...` and the `decide` tactic both rely on a `Decidable` instance existing for the proposition in question.

```lean
example (n : Nat) : Decidable (n = 0) := inferInstance

theorem five_ne_zero : (5 : Nat) ≠ 0 := by decide
-- `decide` runs the Decidable instance's algorithm and turns "the boolean came back true"
-- into an actual Prop-level proof — not just an assertion, a checked derivation.
```

---

## 3. Inductive Types

**Framing:** Rust's `enum` and `struct` both trace back to one primitive in Lean: the `inductive` declaration. This exists because Lean needs exactly one uniform mechanism that can express data (`Nat`, `List`), propositions (`And`, `Or`, `Eq` are themselves `inductive`s), *and* the induction principle used to prove things about them, all from the same definition — in a dependently typed system, "the shape of the data" and "the way you're allowed to reason about the data" are generated together, automatically, from one declaration.

```lean
inductive MyBool where
  | myTrue : MyBool
  | myFalse : MyBool

inductive MyList (α : Type) where
  | nil : MyList α
  | cons : α → MyList α → MyList α
-- declaring this ALSO generates MyList.rec, the induction/recursion principle
-- used to define functions on MyList and prove things about all of them —
-- for free, from the same declaration.
```

**`Nat`, recursively defined, all the way down** — Even Lean's natural numbers are just an `inductive` type (`zero` and `succ`), not a hardware-native primitive (though the compiler special-cases them for performance via GMP-backed bignums at runtime). This exists so that proving something about *all* natural numbers reduces to the same induction principle every other inductive type gets — there is no separate "built-in number theory," it's ordinary structural induction over an ordinary inductive type.

```lean
-- Nat is essentially: inductive Nat | zero | succ (n : Nat)
theorem nat_ind_example (n : Nat) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp [ih]
```

**Structures (`structure`)** — Sugar over a single-constructor `inductive`, for the common case of "one shape, several named fields" — exists for the same readability reason as Rust's `struct`, plus automatic generation of field-projection functions (`.x`, `.y`) and a `mk` constructor, so you don't hand-write accessors for what is, underneath, still an ordinary inductive type with one constructor.

```lean
structure Point where
  x : Float
  y : Float

def origin : Point := { x := 0.0, y := 0.0 }
#eval origin.x  -- 0.0 — auto-generated field projection
```

**Pattern matching (`match`)** — Exists for the same exhaustiveness-checking reason as Rust's `match`: every constructor of the inductive type must be handled or the definition doesn't compile — but here it's not just a safety convenience, it's load-bearing for *proof* correctness too: a `match` that silently ignored a case would mean a function (or proof) that's undefined/unsound on that case, and the induction principle's soundness depends on every constructor genuinely being accounted for.

```lean
def listLength {α : Type} : List α → Nat
  | []      => 0
  | _ :: xs => 1 + listLength xs
  -- omit a case, and this fails to compile — exhaustiveness is not optional
```

---

## 4. Dependent Types ⭐

**Why this section has no real Rust or Noir analog.** Rust's generics let a *type* depend on another type (`Vec<T>`). Lean lets a type depend on a **value** — the actual power that makes formal proof possible at all. `Vector α n`, the type of length-`n` lists of `α`, has `n : Nat` — an ordinary runtime value — appearing *inside* a type. This exists because "this function only accepts lists of length 5" or "this proof only applies when n is even" are exactly the kind of precise, value-dependent constraints ordinary generics can't express — dependent types let the type system encode facts about *specific values*, not just shapes of data.

```lean
-- `n` is a value, not just a type parameter, yet it appears in the TYPE.
inductive Vector (α : Type) : Nat → Type where
  | nil  : Vector α 0
  | cons : α → Vector α n → Vector α (n + 1)

-- head is only callable on a vector PROVEN non-empty by its type — no runtime
-- "is this empty?" check needed; the type itself rules out the bad case.
def head {α : Type} {n : Nat} : Vector α (n + 1) → α
  | Vector.cons x _ => x
```

**`Π`-types (dependent function types)** — `(a : α) → β a` — a function whose *return type* depends on the value of its argument. This exists as the single generalization that subsumes ordinary function types (`α → β`, when `β` doesn't mention `a`) *and* `∀`-quantified statements (`∀ n : Nat, n + 0 = n` is exactly this kind of type) — universal quantification in mathematics and dependent function types in programming are, under Curry–Howard, the same construct.

```lean
-- This IS the statement "for all n, n + 0 = n" — a Π-type whose return type
-- (a Prop) depends on the specific n passed in.
theorem add_zero_all : ∀ n : Nat, n + 0 = n := fun n => by simp
```

**`Σ`-types (dependent pairs, `Sigma` / `Subtype`)** — A pair where the *type* of the second component depends on the value of the first (`Σ n : Nat, Vector α n` — "some length, and a vector of exactly that length"). `Subtype` (`{x : α // p x}`, e.g. `{n : Nat // n > 0}`) is the common special case where the second component is a proof rather than more data — "a value, together with evidence it satisfies some property." This exists to let a function return "a value satisfying X" as a single, self-certifying package, rather than a value plus a separate, easily-detached proof obligation.

```lean
def PosNat := {n : Nat // n > 0}

def mkPosNat (n : Nat) (h : n > 0) : PosNat := ⟨n, h⟩
-- the returned value carries its own proof of positivity, permanently attached
-- to the type — you cannot construct a PosNat without also providing the evidence.
```

---

## 5. Tactics

**Framing:** term-mode proofs are precise but tedious to hand-write for anything beyond a one-liner (imagine writing out, by hand, the full nested case-split term for a moderately involved induction). Tactics exist to let you build that same term *interactively and incrementally*, describing the proof at the level of "what should happen to the goal next," while Lean assembles the actual term underneath — the tactic block is a proof-term generator, not a different kind of proof.

**`rfl` / `rw` / `simp`** — `rfl` closes a goal that's true by definitional unfolding alone (the cheapest possible proof — the two sides are, after unfolding definitions, literally the same term). `rw [lemma]` rewrites the goal using an equation, left-to-right, turning the goal into one that (hopefully) closes with `rfl`. `simp` repeatedly applies a curated *set* of rewrite lemmas (tagged `@[simp]`) until nothing more applies — exists because most routine simplification is genuinely routine, and re-deriving it by hand every time would be pure overhead; `simp` automates the boring 80% so proof authors spend effort on the genuinely novel 20%.

```lean
theorem simp_example (a b : Nat) (h : a = b) : a + 1 = b + 1 := by
  rw [h]  -- rewrites `a` to `b` in the goal, leaving `b + 1 = b + 1`, closed by implicit rfl

theorem simp_example2 (l : List Nat) : l ++ [] = l := by
  simp  -- applies List.append_nil (a @[simp] lemma) automatically
```

**`induction` / `cases`** — `cases` performs one case split over an inductive value's constructors (no recursive hypothesis); `induction` does the same *plus* generates an induction hypothesis for recursive cases (the "assume it holds for the smaller case" step). These exist as the tactic-mode interface to exactly the automatically-generated recursion/induction principle from Section 3 — you are, under the hood, applying `Nat.rec` or `List.rec` etc., just without writing out that application by hand.

```lean
theorem list_ind_example {α : Type} (l : List α) : l.reverse.reverse = l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [ih]  -- `ih` is exactly the induction hypothesis, auto-generated
```

**`exact` / `apply`** — `exact e` closes the current goal by providing a complete term `e` directly — the tactic-mode escape hatch back into term mode for the trivial "I already have exactly the proof" case. `apply f` unifies the goal with `f`'s conclusion and leaves `f`'s premises as new goals — exists for backward reasoning ("to prove this, it suffices to prove these sub-things"), the natural direction most informal mathematical proof already reasons in.

```lean
theorem apply_example {P Q R : Prop} (h1 : P → Q) (h2 : Q → R) (hp : P) : R := by
  apply h2
  apply h1
  exact hp
```

**`intro` / `constructor` / `exists`** — `intro x` moves a `∀`/`→`-bound variable or hypothesis from the goal into the local context — the tactic-mode mirror of writing `fun x => ...`. `constructor` applies an inductive type's constructor to build the current goal (e.g., splits an `And` goal into two subgoals). `exists e` (or `use e`) provides a witness for an `∃` goal — these exist because "introduce a hypothesis," "build a structured proposition," and "provide a witness" are extremely common, mechanical moves that deserve one-word tactic names rather than spelled-out term-mode lambdas every time.

```lean
theorem and_example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  · exact hp
  · exact hq

theorem exists_example : ∃ n : Nat, n > 3 := by
  exists 4
```

**`omega` / `decide` / `norm_num`** — Specialized decision procedures: `omega` fully automates linear arithmetic over `Nat`/`Int` (a genuinely decidable fragment of mathematics — the tactic exists because handing this off to a complete algorithm is strictly better than manual `rw`/`simp` chains for anything arithmetic). `decide` evaluates a `Decidable` instance and turns the boolean result into a proof (Section 2). `norm_num` normalizes and closes goals about concrete numerals. These exist as the general pattern: whenever a fragment of mathematics has a *complete, automatable* algorithm, Lean packages it as one tactic instead of asking humans to hand-derive what a machine can just decide.

```lean
theorem omega_example (a b : Nat) (h : a < b) : a + 1 ≤ b := by omega
theorem norm_num_example : (37 : Nat) + 5 = 42 := by norm_num
```

**`sorry`** — A tactic (and term) that closes *any* goal, immediately, while emitting a warning and poisoning the resulting theorem with an axiom marking it as unproven. Exists purely for development ergonomics: it lets you sketch a proof's overall structure and defer the hard subgoals, while making absolutely certain — via a compiler warning that cannot be silently ignored in a completed build — that nothing "proved with `sorry`" is mistaken for an actual theorem.

```lean
theorem hard_theorem (n : Nat) : n = n + 1 - 1 := by
  sorry  -- compiles, but Lean flags this theorem as depending on `sorry` — never actually proven
```

---

## 6. Typeclasses

**Framing:** the same underlying problem Rust's traits solve ("write code generic over *any type with this capability*") — but Lean's typeclasses predate and directly inspired Rust's trait system, and here they carry additional weight: a typeclass instance can encode not just "this type supports `+`" but "this type satisfies this *law*" (associativity, commutativity), making typeclasses the mechanism by which whole hierarchies of mathematical structure (`Monoid`, `Group`, `Ring`, `Field`) get organized and reused across an entire proof library.

```lean
class Monoid (α : Type) where
  mul : α → α → α
  one : α
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  one_mul   : ∀ a, mul one a = a
  mul_one   : ∀ a, mul a one = a

instance : Monoid Nat where
  mul := Nat.mul
  one := 1
  mul_assoc := Nat.mul_assoc
  one_mul := Nat.one_mul
  mul_one := Nat.mul_one
```

**Instance resolution** — Given a goal like `Monoid Nat`, Lean searches registered `instance`s to find (or construct, for compound types) a satisfying term automatically — exists so that writing generic code (`def square [Monoid α] (x : α) : α := Monoid.mul x x`) doesn't require manually threading "which multiplication" through every call site; the compiler infers it from the concrete type at each use, exactly like Rust trait-bound resolution.

```lean
def square {α : Type} [Monoid α] (x : α) : α := Monoid.mul x x
#eval square (3 : Nat)  -- instance for Nat found automatically — no manual wiring
```

**Why this matters more in Lean than in Rust:** because a typeclass can bundle *proof obligations* (`mul_assoc`, etc.) as fields, defining an instance is itself a proof task — you cannot claim a type is a `Monoid` without actually proving associativity holds for it. Typeclasses are simultaneously Lean's polymorphism mechanism and its mechanism for organizing an entire hierarchy of mathematical theorems as reusable, composable facts.

---

## 7. Monads and `do`-notation

**Framing:** Lean is a pure functional language at its core — no ambient mutable state, no implicit exceptions, no implicit I/O — so anything involving sequencing, state, failure, or side effects needs an explicit structure to thread through. Monads exist as that structure, and `do`-notation exists to let code *using* a monad read like ordinary imperative code, hiding the explicit plumbing (exactly analogous to why Rust's `?` operator exists for `Result` — same underlying motivation, more general mechanism).

```lean
def safeDivide (a b : Nat) : Option Nat :=
  if b == 0 then none else some (a / b)

def compute (a b c : Nat) : Option Nat := do
  let x ← safeDivide a b   -- if this is `none`, the whole `do` block short-circuits to `none`
  let y ← safeDivide x c
  pure y
-- desugars to nested Option.bind calls — do-notation is sugar, not a separate feature
```

**`IO` monad** — Real side effects (printing, file access) are represented as values of type `IO α` — "a description of an effectful computation that, when run, produces an `α`." This exists to preserve purity everywhere *except* the boundary explicitly marked `IO` — a function's type honestly tells you whether it can perform side effects, the same transparency guarantee `Result`/`Option` give Rust about failure, just generalized to arbitrary effects.

```lean
def greet (name : String) : IO Unit := do
  IO.println s!"Hello, {name}!"

def main : IO Unit := do
  greet "Lean"
```

**`Except` / error handling** — `Except ε α` (isomorphic to Rust's `Result<α, ε>`) represents a computation that either succeeds with an `α` or fails with an `ε` — same motivation as Rust's `Result`: make failure a value the type signature documents and the compiler forces you to handle, not a hidden exception.

```lean
def safeDiv (a b : Nat) : Except String Nat :=
  if b == 0 then .error "division by zero" else .ok (a / b)

def chain (a b c : Nat) : Except String Nat := do
  let x ← safeDiv a b
  let y ← safeDiv x c
  pure y
```

---

## 8. Termination and Well-Founded Recursion

**Framing:** in a system where "does this type-check" and "is this proof valid" are the same question, an infinite loop is catastrophic in a way it simply isn't in Rust: an unchecked general-recursive function could be used to "prove" `False` (define `f n := f n + 1`, derive a contradiction by unfolding forever) — so **every** recursive definition must be proven to terminate before Lean accepts it, not just as a best practice but as a soundness requirement of the whole logic.

**Structural recursion (the default)** — When a recursive call is made on a syntactically smaller piece of an inductive argument (`n` in `succ n`, `xs` in `x :: xs`), Lean's equation compiler proves termination automatically, for free, via the same structural-decrease argument that justified the inductive type's own recursion principle in Section 3.

```lean
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n
  -- terminates because `n` is structurally smaller than `n + 1` — proven automatically
```

**Well-founded recursion (`termination_by` / `decreasing_by`)** — For recursion that isn't a simple structural decrease (e.g., recursing on a value derived by computation, not just pattern-matched apart), you supply an explicit **measure** — a mapping from the arguments to some well-founded order (usually `Nat` with `<`) that provably decreases on every recursive call. This exists because structural recursion alone can't express many genuinely-terminating algorithms (Euclid's GCD, merge sort splitting a list in half) — well-founded recursion generalizes "gets structurally smaller" to "gets smaller by *any* provably well-founded measure," at the cost of having to supply and prove that measure yourself.

```lean
def gcd (a b : Nat) : Nat :=
  if h : b = 0 then a
  else gcd b (a % b)
termination_by b
decreasing_by simp_wf; exact Nat.mod_lt a (Nat.pos_of_ne_zero h)
-- explicitly proves `a % b < b`, the measure that guarantees this eventually hits b = 0
```

**Partial functions (`partial def`)** — An explicit opt-out: `partial def` skips the termination proof entirely, at the cost of the function no longer being usable inside proofs the way a total function is (its equations aren't unfolded by the kernel the same way) — exists as a pressure-release valve for genuinely general-purpose programming (an interpreter's eval loop, a server's request loop) where "prove this terminates" isn't the point and may not even be true.

```lean
partial def loop (n : Nat) : Nat :=
  if n == 0 then 0 else loop (n - 1)
  -- accepted without a termination proof — but can't be reasoned about
  -- inside a Prop the way a structurally-recursive def can
```

---

## 9. Equality, `Eq.mpr`, and Rewriting

**Framing:** Rust's `==` is a runtime `bool`-returning method; Lean's `Eq` (`=`) is a genuine `Prop` — a *type of proofs that two things are equal* — with real internal structure the compiler exploits, not just a comparison you branch on.

**`rfl` and definitional equality** — Two terms are **definitionally equal** if they reduce to the same normal form by unfolding definitions/computation alone, with no extra proof needed — `rfl : a = a` is accepted whenever Lean's kernel can verify this by computation. This exists because a huge fraction of "trivial" equalities in ordinary programming (`2 + 2 = 4`, `List.length [] = 0`) really are just computation, and forcing an explicit multi-step proof for them would be needless ceremony.

```lean
example : 2 + 2 = 4 := rfl          -- true by pure computation
example : List.length ([] : List Nat) = 0 := rfl
```

**`Eq.subst` / `▸` (rewriting via substitution)** — Given `h : a = b`, you can transport a proof about `a` into a proof about `b` (substitute equals for equals) — this is the formal justification underlying the `rw` tactic: rewriting isn't a special primitive, it's `Eq.subst`/`Eq.mpr` applied automatically, exists because "substitute equal things for each other" is *the* fundamental operation mathematics performs constantly, and Lean makes it a first-class, kernel-checked term rather than an informal step taken on faith.

```lean
theorem subst_example (a b : Nat) (h : a = b) (p : a > 0) : b > 0 :=
  h ▸ p  -- transports the proof `p : a > 0` along `h : a = b` into `b > 0`
```

**`HEq` (heterogeneous equality)** — Ordinary `Eq` requires both sides to already have the *same type*; but dependent types (Section 4) sometimes produce two values whose types are only equal *after* some other proof is applied (`Vector α n` and `Vector α m` when `n = m` is itself something you're mid-proof of establishing) — `HEq` exists specifically to state "these are equal" even when the type-checker can't yet see the two types as syntactically identical, a genuinely dependent-types-specific problem with no analog in a simply-typed language.

---

## 10. Metaprogramming and Tactic Extension

**Framing:** Rust's macros generate code from syntax at compile time; Lean's metaprogramming framework does the same, but because Lean's compiler and its own metaprogramming API are written *in Lean itself*, "extend the language" and "write an ordinary Lean program" are much closer to the same activity than in almost any other language — this exists to make Lean genuinely extensible by its own users (most of Mathlib's specialized tactics were built this way, not by patching the compiler).

**`macro` / `syntax`** — Define new notation/syntax and how it expands, analogous to `macro_rules!` — exists for the same reason: some domain-specific notation (custom operators, DSL-like syntax for a particular area of math) is clearer written directly than spelled out with existing syntax every time.

```lean
syntax "twice " term : term
macro_rules | `(twice $x) => `($x + $x)

#eval twice 5  -- 10
```

**`elab` / tactic-writing in Lean itself** — New tactics are written as ordinary Lean programs operating over the current proof state (goals, local context) via Lean's own metaprogramming monads (`TacticM`, `MetaM`) — exists so that when the built-in tactic library doesn't cover a repeated pattern in some domain, a user can write a new automated tactic *without leaving Lean or learning a separate plugin language*, which is a large part of why Mathlib's proof-automation ecosystem grew as large as it did.

```lean
-- conceptual shape: a tactic is a Lean function operating on the goal state
elab "double_intro" : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| intro; intro))
```

**`#eval`-time metaprogramming vs. proof-time tactics** — Worth distinguishing explicitly: ordinary metaprogramming (`elab`, `macro`) runs *while Lean is elaborating your file*, generating terms/tactics; this is a compile-time-only concern, fully analogous to how Rust macros never appear in the compiled binary — the generated proof terms are what the kernel ultimately checks, not the tactic code that produced them.

---

## 11. Universes

**Framing:** `Type` itself needs a type, or you'd get the paradox that sank naive set theory (a "type of all types" containing itself). Lean's answer is a strict **hierarchy**: `Type 0` (`Type`, ordinary data), `Type 1` (the type of `Type 0` and things quantifying over it), `Type 2`, and so on, with `Sort u` the fully general form parametrized by a universe variable `u`. This exists purely to keep the logic consistent — a `Type`-of-all-`Type`s would let you construct Russell's-paradox-style self-referential contradictions inside the proof system itself, which would make every proof Lean ever checks worthless.

```lean
#check Nat          -- Nat : Type          (Type 0)
#check Type         -- Type : Type 1
#check Type 1        -- Type 1 : Type 2

universe u
def identity {α : Type u} (x : α) : α := x
-- `identity` works at EVERY universe level simultaneously via the universe
-- variable `u` — this is why `id` in Lean can be applied to a Nat, a Type, or
-- a Type of Types, without three separate definitions.
```

**`Prop` sits below `Type 0`, specially** — Not simply "`Type 0`'s little sibling" — `Prop` (`Sort 0`) gets its own dedicated proof-irrelevance and erasure rules (Section 2) that ordinary `Type`s don't. This exists because propositions and data genuinely need different rules (erase-at-runtime vs. keep-at-runtime), and the universe hierarchy is the mechanism that keeps that distinction principled rather than ad hoc.

---

## 12. Tooling: Lake, `elan`, Mathlib

**Framing:** same "one standard way to build/test/depend on code" motivation as Cargo and Nargo — Lake exists because a growing proof-assistant ecosystem has exactly the same dependency-management and reproducible-build needs any other language does, plus the extra wrinkle that a project's dependencies (especially Mathlib) can themselves take a long time to compile, making incremental, cached builds unusually important.

**`elan`** — Toolchain manager (installs/switches Lean versions per project, reading a `lean-toolchain` file) — exists for the identical reason `rustup` does: different projects (especially ones depending on Mathlib, which pins a specific Lean version) need different, precisely-pinned compiler versions, and a moving target here would silently break proofs that depended on now-changed elaboration behavior.

```bash
elan install leanprover/lean4:v4.9.0
elan default leanprover/lean4:v4.9.0
```

**`lake build` / `lake exe` / `lakefile.toml`** — `lake build` compiles the project (and, transitively, its dependencies, with build caching); `lakefile.toml`/`lakefile.lean` declares dependencies (often a specific Mathlib commit) — exists as Lean's Cargo.toml equivalent, with the same "pin exact versions so a proof that compiled yesterday still compiles today" motivation, made sharper by how expensive Mathlib re-verification can be if versions drift.

```toml
# lakefile.toml
name = "my_project"
defaultTargets = ["MyProject"]

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4"
```

```bash
lake build     # compiles the project and its pinned dependencies, with caching
lake exe cache get   # fetches prebuilt Mathlib .olean files instead of recompiling from source
```

**Mathlib and caching** — Mathlib is large enough that recompiling it from source is impractical for routine development, so the tooling ships a binary-cache mechanism (`lake exe cache get`) to fetch precompiled `.olean` files — exists purely as a pragmatic scaling response to "a from-scratch build of the standard library everyone depends on would otherwise take hours."

---

## 13. Style and Proof Organization Conventions (Mathlib-influenced)

**Naming conventions (`Nat.add_comm`, `List.length_append`, ...)** — Lemma names systematically encode *what they state*, in a fairly rigid, greppable pattern (`add_comm` = "addition is commutative," `length_append` = "a statement about `length` of an `append`") — this exists because a library with tens of thousands of lemmas is only navigable if names are predictable enough to *guess* — a senior Lean/Mathlib contributor can often correctly guess an unfamiliar lemma's name from the statement alone, which is the entire point of the convention.

```lean
-- naming encodes structure: `mul_comm`, `mul_assoc`, `zero_mul`, `mul_zero`, ...
-- predictable enough that `exact?`/`apply?` (see below) can search effectively too.
```

**`exact?` / `apply?` / `hint`** — Search tactics that scan the (enormous) library for a lemma that closes the current goal exactly or via `apply` — exists as a direct, practical consequence of the naming-convention point above: a library this large is more efficiently searched by tooling than memorized, and these tactics exist to make "does a proof of this already exist" a fast, automatable question rather than a manual grep.

```lean
example (a b : Nat) : a + b = b + a := by exact?  -- suggests: exact Nat.add_comm a b
```

**Golfing vs. legibility trade-off** — Worth flagging as a genuine, recurring judgment call in this community, analogous to Rust's idiomatic-vs-clever trade-off: a one-line `simp`/`omega`-heavy proof compiles and closes the goal, but a longer, structured tactic proof (or well-commented term-mode proof) is often preferred in a shared library specifically because a future maintainer needs to understand *why* something is true, not just that the kernel accepted it.

---

### The one meta-answer a senior candidate should give if asked "what is Lean's core idea, in one sentence"

**Lean is built on the observation that a proof and a program are the same kind of object — a term whose type the compiler checks — so every feature in the language, from inductive types to dependent function types to tactics to typeclasses, exists to make that one idea (Curry–Howard: propositions are types, proofs are programs) practical to work with at the scale of real mathematics and real software, rather than to bolt a separate "proof mode" onto an otherwise ordinary programming language.**
