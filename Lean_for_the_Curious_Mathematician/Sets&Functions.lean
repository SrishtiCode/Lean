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
