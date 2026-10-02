/-
  ============================================================
  BASIC RING DEFINITIONS AND THEOREMS
  ============================================================

  We import some basic algebraic definitions and theorems.

  `Mathlib.Algebra.Ring.Defs`
      Gives us definitions and basic facts about rings.

  `Mathlib.Data.Real.Basic`
      Gives us basic facts about the real numbers ℝ.

  `MIL.Common`
      Common imports used by the Mathematics in Lean course.
-/

import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import MIL.Common


/-
  ============================================================
  SECTION 1: LOOKING AT BASIC RING THEOREMS
  ============================================================

  We introduce an abstract type `R`.

  `R : Type*`
      Means R is some type.

  `[Ring R]`
      Means we assume R has a Ring structure.

  Therefore elements of R have:
      +   addition
      *   multiplication
      0   additive identity
      1   multiplicative identity
      -a  additive inverse

  And they satisfy the ring laws.
-/

section

variable (R : Type*) [Ring R]


/-
  `add_assoc` = associativity of addition.

  Mathematically:

      (a + b) + c = a + (b + c)

  Lean's notation `a + b + c` is parsed as:

      (a + b) + c
-/
#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))


/-
  `add_comm` = commutativity of addition.

      a + b = b + a
-/
#check (add_comm : ∀ a b : R, a + b = b + a)


/-
  `zero_add`:

      0 + a = a
-/
#check (zero_add : ∀ a : R, 0 + a = a)


/-
  `neg_add_cancel`:

      -a + a = 0

  An element and its additive inverse cancel.
-/
#check (neg_add_cancel : ∀ a : R, -a + a = 0)


/-
  `mul_assoc` = associativity of multiplication.

      (a * b) * c = a * (b * c)

  Again, `a * b * c` is parsed as:

      (a * b) * c
-/
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))


/-
  `mul_one`:

      a * 1 = a
-/
#check (mul_one : ∀ a : R, a * 1 = a)


/-
  `one_mul`:

      1 * a = a
-/
#check (one_mul : ∀ a : R, 1 * a = a)


/-
  `mul_add` = left distributivity of multiplication over addition.

      a * (b + c) = a * b + a * c
-/
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)


/-
  `add_mul` = right distributivity.

      (a + b) * c = a * c + b * c
-/
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)

end



/-
  ============================================================
  SECTION 2: USING `ring`
  ============================================================

  Here we assume R is a COMMUTATIVE ring.

  `[CommRing R]`
      A commutative ring has all the usual ring laws plus
      commutativity of multiplication:

          a * b = b * a

  We also introduce four elements of R.
-/

section

variable (R : Type*) [CommRing R]
variable (a b c d : R)


/-
  Example 1:

      c * b * a = b * (a * c)

  `ring` automatically normalizes both sides using the
  algebraic laws of a commutative ring.

  In particular, it can handle:
      - associativity of multiplication
      - commutativity of multiplication
-/
example : c * b * a = b * (a * c) := by
  ring


/-
  Example 2:

      (a + b) * (a + b)
        = a*a + 2*(a*b) + b*b

  This is the usual expansion of (a+b)^2.

  `ring` performs all the distributive expansion and
  rearrangement automatically.
-/
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  ring


/-
  Example 3:

      (a + b) * (a - b) = a^2 - b^2

  This is the difference-of-squares identity.

  `ring` understands subtraction as addition of a negation
  and normalizes the resulting polynomial expression.
-/
example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring


/-
  Example 4:

  Hypotheses:

      hyp  : c = d * a + b
      hyp' : b = a * d

  Goal:

      c = 2 * a * d

  First:
      rw [hyp, hyp']

  replaces:
      c
  by:
      d * a + b

  and then:
      b
  by:
      a * d

  `ring` then rearranges the multiplication and combines
  the two identical terms.
-/
example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by

  -- Replace c using hyp, and b using hyp'.
  rw [hyp, hyp']

  -- Now the remaining equality is a polynomial identity.
  ring

end



/-
  ============================================================
  NAMESPACE MyRing
  ============================================================

  We now create our own namespace called `MyRing`.

  This lets us define theorems with names such as:

      MyRing.add_zero

  without interfering with the existing theorem:

      add_zero
-/

namespace MyRing

variable {R : Type*} [Ring R]


/-
  ------------------------------------------------------------
  Our own version of `add_zero`
  ------------------------------------------------------------

  Goal:

      a + 0 = a

  The standard theorem `zero_add` says:

      0 + a = a

  We use commutativity to turn:

      a + 0

  into:

      0 + a

  and then use `zero_add`.
-/
theorem add_zero (a : R) : a + 0 = a := by

  -- Step 1:
  -- a + 0  →  0 + a
  rw [add_comm, zero_add]


/-
  ------------------------------------------------------------
  `add_neg_cancel`
  ------------------------------------------------------------

  Goal:

      a + (-a) = 0

  `neg_add_cancel` already gives:

      -a + a = 0

  We first swap the order using commutativity:

      a + -a
        ↓
      -a + a
        ↓
      0
-/
theorem add_neg_cancel (a : R) : a + -a = 0 := by

  rw [add_comm, neg_add_cancel]


/-
  `MyRing.add_zero` refers to OUR theorem.

  `add_zero` inside the namespace also resolves to our theorem.
-/
#check MyRing.add_zero
#check add_zero

end MyRing



namespace MyRing

variable {R : Type*} [Ring R]


/-
  ============================================================
  neg_add_cancel_left
  ============================================================

  Goal:

      -a + (a + b) = b

  We want `-a + a` to become visible.

  Starting expression:

      -a + (a + b)

  `← add_assoc` changes:

      x + (y + z)
          ↓
      (x + y) + z

  so:

      -a + (a + b)
          ↓
      (-a + a) + b

  Then:

      -a + a = 0

  giving:

      0 + b

  and finally:

      b
-/
theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by

  -- Regroup the addition:
  -- -a + (a + b)  →  (-a + a) + b
  rw [← add_assoc, neg_add_cancel, zero_add]



/-
  ============================================================
  add_neg_cancel_right
  ============================================================

  Goal:

      a + b + -b = a

  Because addition is left-associative, Lean reads this as:

      (a + b) + -b

  First use associativity:

      (a + b) + -b
          ↓
      a + (b + -b)

  Then use commutativity to put the terms into a form
  where `add_neg_cancel` can cancel them.

  Finally:
      0 + a = a
-/
theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by

  -- ((a + b) + -b) → a + (b + -b)
  rw [add_assoc]

  -- Rearrange so b and -b can cancel.
  rw [add_comm]

  -- b + -b → 0
  rw [add_neg_cancel]

  -- 0 + a → a
  rw [zero_add]


/-
  `sub_add_cancel` is a standard theorem related to subtraction.
-/
#check sub_add_cancel



/-
  ============================================================
  add_left_cancel
  ============================================================

  If:

      a + b = a + c

  then:

      b = c

  This is cancellation on the LEFT.

  We already know:

      -a + (a + b) = b

  from our theorem `neg_add_cancel_left`.

  The strategy is to add `-a` to the equality.

  Starting goal:

      b = c

  We rewrite b using:

      b = -a + (a + b)

  This lets us use the hypothesis:

      h : a + b = a + c
-/
theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by

  -- Replace b by an equal expression:
  --
  -- b → -a + (a + b)
  rw [← neg_add_cancel_left a b]

  -- Use h to replace a + b by a + c.
  rw [h]

  -- Now:
  --
  -- -a + (a + c)
  --
  -- becomes:
  --
  -- c
  rw [neg_add_cancel_left]



/-
  ============================================================
  add_right_cancel
  ============================================================

  If:

      a + b = c + b

  then:

      a = c

  This is cancellation on the RIGHT.

  We transform the problem into one where
  `add_left_cancel`-style reasoning can be used.
-/
theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by

  -- Replace a using:
  --
  -- a = -b + (b + a)
  --
  -- from neg_add_cancel_left.
  rw [← neg_add_cancel_left b a]

  -- b + a → a + b
  rw [add_comm b a]

  -- Use:
  --
  -- a + b = c + b
  --
  -- from h.
  rw [h]

  -- c + b → b + c
  rw [add_comm c b]

  -- -b + (b + c) → c
  rw [neg_add_cancel_left]



/-
  ============================================================
  mul_zero
  ============================================================

  Goal:

      a * 0 = 0

  We prove this without directly using the standard theorem.

  The key idea is to show:

      a*0 + a*0 = a*0 + 0

  and then cancel `a*0` from both sides.

  The hypothesis `h` has exactly the form required by
  `add_left_cancel`.
-/
theorem mul_zero (a : R) : a * 0 = 0 := by

  -- Construct an equality in which the same term occurs
  -- on both left sides:
  --
  -- a*0 + a*0 = a*0 + 0
  have h : a * 0 + a * 0 = a * 0 + 0 := by

    /*
      `← mul_add` works backwards from:

          a * (0 + 0) = a * 0 + a * 0

      So it combines:

          a * 0 + a * 0

      into:

          a * (0 + 0)

      Then `add_zero` changes:

          0 + 0 → 0

      and the second `add_zero` changes:

          a * 0 + 0 → a * 0
    */
    rw [← mul_add, add_zero, add_zero]

  -- From:
  --
  -- a*0 + a*0 = a*0 + 0
  --
  -- cancel the common `a*0`.
  rw [add_left_cancel h]



/-
  ============================================================
  zero_mul
  ============================================================

  Goal:

      0 * a = 0

  Again we prove this through additive cancellation.

  We first construct:

      0*a + 0*a = 0*a + 0

  and then cancel `0*a`.
-/
theorem zero_mul (a : R) : 0 * a = 0 := by

  -- Construct the equality needed for cancellation.
  have h : 0 * a + 0 * a = 0 * a + 0 := by

    /*
      `← add_mul` changes:

          0*a + 0*a

      into:

          (0 + 0) * a

      Then `add_zero` simplifies the zero addition.
    */
    rw [← add_mul, add_zero, add_zero]

  -- Cancel 0*a from both sides.
  rw [add_left_cancel h]



/-
  ============================================================
  neg_eq_of_add_eq_zero
  ============================================================

  If:

      a + b = 0

  then:

      -a = b

  We use our theorem:

      -a + (a + b) = b

  backwards.

  So the right side `b` is replaced with:

      -a + (a + b)

  Then the hypothesis tells us:

      a + b = 0

  giving:

      -a + 0

  and finally:

      -a
-/
theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by

  -- b → -a + (a + b)
  rw [← neg_add_cancel_left a b]

  -- a + b → 0
  rw [h]

  -- -a + 0 → -a
  rw [add_zero]



/-
  ============================================================
  eq_neg_of_add_eq_zero
  ============================================================

  If:

      a + b = 0

  then:

      a = -b

  We use the previous theorem.

  First `symm` changes:

      a = -b

  into:

      -b = a

  Then `apply neg_eq_of_add_eq_zero` says:

      To prove -b = a,
      it is enough to prove b + a = 0.

  Finally:
      b + a → a + b
  using commutativity,
  and then use h.
-/
theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by

  -- Reverse the equality:
  --
  -- a = -b
  -- ↓
  -- -b = a
  symm

  -- Apply the theorem that proves:
  --
  -- if x + y = 0, then -x = y
  apply neg_eq_of_add_eq_zero

  -- b + a → a + b → 0
  rw [add_comm, h]



/-
  ============================================================
  neg_zero
  ============================================================

  Goal:

      -0 = 0

  We use `neg_eq_of_add_eq_zero`.

  To prove:

      -0 = 0

  it is enough to prove:

      0 + 0 = 0

  which follows from `add_zero`.
-/
theorem neg_zero : (-0 : R) = 0 := by

  apply neg_eq_of_add_eq_zero

  rw [add_zero]



/-
  ============================================================
  neg_neg
  ============================================================

  Goal:

      -(-a) = a

  We use `neg_eq_of_add_eq_zero`.

  To prove:

      -(-a) = a

  it is enough to prove:

      -a + a = 0

  which is exactly `neg_add_cancel`.
-/
theorem neg_neg (a : R) : - -a = a := by

  apply neg_eq_of_add_eq_zero

  rw [neg_add_cancel]

end MyRing



/-
  ============================================================
  EXAMPLES
  ============================================================
-/

section

variable {R : Type*} [Ring R]


/-
  In any ring:

      a - b = a + (-b)

  This is simply the definition/property of subtraction.
-/
example (a b : R) : a - b = a + -b :=
  sub_eq_add_neg a b

end



/-
  For real numbers, subtraction is definitionally represented
  in a way that makes this equality reducible to `rfl`.

  `rfl` proves definitional equality.
-/
example (a b : ℝ) : a - b = a + -b :=
  rfl


/-
  The same proof can be written using `by`.
-/
example (a b : ℝ) : a - b = a + -b := by
  rfl



namespace MyRing

variable {R : Type*} [Ring R]


/-
  ============================================================
  self_sub
  ============================================================

  Goal:

      a - a = 0

  First change subtraction into addition of a negation:

      a - a
      ↓
      a + -a

  Then use:

      a + -a = 0
-/
theorem self_sub (a : R) : a - a = 0 := by

  rw [sub_eq_add_neg, add_neg_cancel]



/-
  ============================================================
  one_add_one_eq_two
  ============================================================

  Goal:

      1 + 1 = 2

  `norm_num` handles numerical normalization.
-/
theorem one_add_one_eq_two : 1 + 1 = (2 : R) := by
  norm_num



/-
  ============================================================
  two_mul
  ============================================================

  Goal:

      2 * a = a + a

  We know:

      2 = 1 + 1

  So first replace 2:

      2 * a
      ↓
      (1 + 1) * a

  Then distribute:

      (1 + 1) * a
      ↓
      1*a + 1*a

  Finally:

      1*a → a
-/
theorem two_mul (a : R) : 2 * a = a + a := by

  -- Replace 2 with 1 + 1.
  rw [← one_add_one_eq_two]

  -- Distribute multiplication over addition,
  -- then simplify 1 * a.
  rw [add_mul, one_mul]

end MyRing



/-
  ============================================================
  SECTION: ADDITIVE GROUP
  ============================================================

  Now we use a weaker structure than a ring.

  `[AddGroup A]`
      means A has addition, zero, additive inverses,
      associativity, etc.

  Multiplication is NOT assumed here.

  Therefore we can still use:
      +, 0, -, add_assoc, neg_add_cancel
  but not ring-specific multiplication theorems.
-/

section

variable (A : Type*) [AddGroup A]

#check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))

#check (zero_add : ∀ a : A, 0 + a = a)

#check (neg_add_cancel : ∀ a : A, -a + a = 0)

end



/-
  ============================================================
  SECTION: GROUP
  ============================================================

  `[Group G]`
      gives us multiplication, identity `1`, and inverses.

  A group does NOT require commutativity.

  Therefore:

      a * b = b * a

  is NOT generally true.

  But associativity and inverse laws still hold.
-/

section

variable {G : Type*} [Group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))

#check (one_mul : ∀ a : G, 1 * a = a)

#check (inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1)



namespace MyGroup


/-
  ============================================================
  mul_inv_cancel
  ============================================================

  Goal:

      a * a⁻¹ = 1

  We are given only:

      a⁻¹ * a = 1

  because `inv_mul_cancel` is available.

  Since groups do not necessarily have commutative
  multiplication, we carefully use associativity instead
  of simply swapping factors.
-/
theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by

  /*
    We first prove:

      (a * a⁻¹)⁻¹ * (a * a⁻¹ * (a * a⁻¹)) = 1

    The expression is constructed so that inverse cancellation
    can eventually reduce it.
  */
  have h : (a * a⁻¹)⁻¹ * (a * a⁻¹ * (a * a⁻¹)) = 1 := by

    /*
      `mul_assoc` changes grouping.

      `← mul_assoc a⁻¹ a` allows the expression involving
      a⁻¹ * a to become visible.

      `inv_mul_cancel` gives:

          a⁻¹ * a = 1

      and then `one_mul` simplifies:

          1 * x = x

      Finally `inv_mul_cancel` is used again.
    */
    rw [mul_assoc, ← mul_assoc a⁻¹ a, inv_mul_cancel, one_mul,
        inv_mul_cancel]

  /*
    Now rewrite the goal using h.

    The rest is a sequence of associativity and cancellation
    steps that reduce the expression to a * a⁻¹ = 1.
  */
  rw [← h, ← mul_assoc, inv_mul_cancel, one_mul]



/-
  ============================================================
  mul_one
  ============================================================

  Goal:

      a * 1 = a

  We prove it from inverse laws.

  Start by introducing:

      a⁻¹ * a = 1

  backwards.

  Then use associativity and the theorem we just proved:

      a * a⁻¹ = 1
-/
theorem mul_one (a : G) : a * 1 = a := by

  /*
    Start with:

      a

    and rewrite it backwards using:

      a⁻¹ * a = 1
  */
  rw [← inv_mul_cancel a, ← mul_assoc, mul_inv_cancel, one_mul]



/-
  ============================================================
  mul_inv_rev
  ============================================================

  Goal:

      (a * b)⁻¹ = b⁻¹ * a⁻¹

  This is the reverse-order rule for inverses.

  Notice the order:

      (a*b)⁻¹
          =
      b⁻¹*a⁻¹

  The factors appear in REVERSE order.
-/
theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by

  /*
    We introduce 1 on the left:

        b⁻¹ * a⁻¹
        ↓
        1 * (b⁻¹ * a⁻¹)

    using `one_mul` backwards.
  */
  rw [← one_mul (b⁻¹ * a⁻¹),

      /*
        Introduce the expression:

            (a*b)⁻¹ * (a*b)

        using `inv_mul_cancel`.
      */
      ← inv_mul_cancel (a * b),

      /*
        Rearrange the grouping of the products.
      */
      mul_assoc,
      mul_assoc,

      /*
        Make `b * b⁻¹` visible.
      */
      ← mul_assoc b b⁻¹,

      /*
        Cancel:
            b * b⁻¹ = 1
      */
      mul_inv_cancel,

      /*
        Simplify:
            1 * a⁻¹ = a⁻¹
      */
      one_mul,

      /*
        Cancel the remaining inverse/product.
      */
      mul_inv_cancel,

      /*
        Finally:
            a * 1 = a
      */
      mul_one]

end MyGroup

end

