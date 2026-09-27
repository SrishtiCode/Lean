import Mathlib.Tactic

/-
# Functions

Notation for functions is the usual in mathematics: given two
types `X` and `Y`, `f : X → Y`
denotes a function from `X` to `Y`.

Internally, `X → Y` denotes the type of functions from `X` to `Y`,
and `f : X → Y` means that `f`
is a term of type `X → Y`, that is, a function from `X` to `Y`.

NOTATION : given `x : X` and `f : X → Y`, to denote the evaluation
`f(x)` we can (and usually do)
omit the parenthesis, and write `f x`. However, the parenthesis are
needed for more complicated expressions. For instance, given `x : X`, `f : X → Y` and
`g : Y → Z`, to evaluate the composition `g(f(x))` we need at least the exterior parenthesis
are needed for more complicated expressions. For instance, given `x : X`, `f: X → Y` and `g : Y → Z`,
to evaluate the composition `g(f(x))` we need at least the exterior parenthesis: `g(f x)`.

WARNING : Given `a b : X` and `f : X → Y`, if we write `f a + b`,
Lean will interpret this as `f(a) + b` (which in general will cause a type error). If we mean `f(a + b)`,
we need to write the parentheses.
-/

section

variable(X Y Z : Type) [AddMonoid X] (a b : X) (f : X → Y) (g : Y → Z)
#check f a
#check g (f a)
#check f (a + b)

end

/-
## Injectivity and Surjectivity

Lean knows the definition of injective function (`Function.Injective`)
and sujective function (`Function.Surjective`). Given any function `f : X → Y`, `Function.Injective f`
and `Function.Surjective f` are propositions (whose truth value depends on `f`).

-/

/-
If we open the "Function" `namespace`, we can omit `Function.`
and simply write `Injective f` and `Surjective f`.
-/

open Function

/-
We fix three types `X`,`Y`,`Z` (we can think of them as sets)
and two functions
`f : X → Y` , `g : Y → Z`.
-/

variable {X Y Z : Type} {f : X → Y} {g : Y → Z}

/- Let `a,b,x` be elements of `X` , `y ∈ Y`, `z ∈ Z`. -/
variable (a b x : X) (y : Y) (z : Z)

-- We open a `namespace` to avoid name clashes with existing Mathlib lemmas.

namespace functions

/-
# Injective functions
-/

/- We check Lean's definition of injective functions -/

lemma injective_def : Injective f ↔ ∀ a b : X, f a = f b → a = b
:= by
   rfl --true by definition

-- The instruction `rw [injective_def]` replaces `Injective f` by
-- its by definition

/- We check that the identity function `id : X → X` is given by `id(x) = x`.-/
lemma id_eval : id x = x := by
   rfl -- true by definition

-- Function composition is denoted by `∘`. By definition, `(g ∘ f)x = g(f(x))`.

lemma comp_eval : (g ∘ f) x = g (f x) := by
   rfl

/-
We are proving these lemmas that are true "by definition" (`rfl`) so that we can
use the `rw` tactic to replace these terms by their definition.
-/

/-
For example, we can start this proof with `rw [injective_def]`,
and later use `rw[id_eval]`.-/

lemma injective_id : Injective (id : X → X) := by
    rw [injective_def]
    intro a b hab
    simp only [id] at hab
    exact hab

lemma injective_comp (hf : Injective f) (hg : Injective g) :
Injective (g ∘ f) := by
    sorry --exercise

example (f : X → Y) (g : Y → Z):
    Injective (g ∘ f) → Injective f := by
    sorry --exercise

/-!

### Surjective functions

-/

/- We check Lean's definition of surjective function.-/

lemma surjective_def : Surjective f ↔ ∀ y : Y, ∃ x : X, f x = y :=
by
    rfl

/-- The identity function is surjective--/
lemma surjective_id : Surjective (id : X → X) := by
    sorry --exercise

/- A composition of surjective functions in surjective.-/
lemma surjective_comp (hf : Surjective f) (hg : Surjective g):
Surjective (g ∘ f) := by
  rw [surjective_def] at *
  intro z
  obtain ⟨y, hy⟩  := hg z
  obtain ⟨x, hx⟩ := hf y
  use x
  rw [comp_eval, hx, hy]

/-Example-/
example (f : X → Y) (g : Y → Z) :
    Surjective (g ∘ f) → Surjective g := by
    sorry --exercise

/-
### Bijective functions
-/

/-
A bijective function is, by definition, a function that is both
injective and surjective
-/

lemma bijective_def : Bijective f ↔ Injective f ∧ Surjective f :=
by
    rfl

lemma bijective_id : Bijective (id : X → X) := by
    sorry --exercise

/- A composition of bijective functions isbijective. -/
lemma bijective_comp (hf : Bijective f) (hg : Bijective g) :
Bijective (g ∘ f) := by
    sorry --exercise

/- ### λ notation :
In Lean, functions are defined using `λ` expressions:
`λ x ↦ f x` is a function that maps `x` to `f(x)`
-/

def α : ℕ → ℕ := λ n ↦ n^2 + 3 --`f(n) = n^2 + 3`

-- We can also use the keyword `fun` instead of `λ`

def α' : ℕ → ℕ := fun n ↦ n^2 + 3

example : α 3 = 12 := by
  rw [α]
  rfl

/-
### Working with a concrete example

Some useful  lemmas to complete the following examples are:
* **not_forall** : `(¬∀ x, p x) ↔ ∃ x, ¬p x`
* **add_left_inj** : `∀ x y z, x + z = y + z ↔ x = y`
* **Nat.succ_ne_zero** : `∀ (n : ℕ), n.succ ≠ 0` : here it is crucial to understand
that `x ≠ y` is *defined* as the implication `(x = y) → false`, `n.succ = n + 1`
*by definition* (whereas `1 + n = n.succ` is a *theorem*).
-/

def s : ℕ → ℕ := fun n ↦ n + 1

example : Injective s := by
    sorry --exercise

example : ¬ Surjective s := by
    sorry --exercise

end functions
