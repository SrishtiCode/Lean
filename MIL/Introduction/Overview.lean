import MIL.Common

-- Import the common definitions, theorems, and tools used in
-- Mathematics in Lean.
import MIL.Common

-- Open the Nat namespace so we can use natural-number declarations
-- without writing Nat. before every name.
open Nat


/-!
SECTION 1: DATA AND DEFINITIONS

Data consists of objects such as numbers and functions.
Lean checks the type of each expression.
-/

-- #check asks Lean to display the type of an expression.
-- The expression 2 + 2 is a natural number.
#check 2 + 2

-- Define a function named f.
-- It takes an input x of type ℕ (the natural numbers)
-- and returns x + 3.
-- The symbol := introduces the definition.
def f (x : ℕ) :=
  x + 3

-- Check the type of f.
-- Lean reports that f is a function from ℕ to ℕ.
#check f


/-!
SECTION 2: PROPOSITIONS

A proposition is a statement that can be proved.
In Lean, propositions have type Prop.
-/

-- This expression is a proposition:
-- "2 + 2 is equal to 4."
-- Lean reports its type as Prop.
#check 2 + 2 = 4

-- Define the proposition called FermatLastTheorem.
-- ∀ means "for all".
-- ℕ means natural numbers.
-- ∧ means "and".
-- → means "implies".
-- > means "greater than".
-- ≠ means "not equal to".
-- ^ means exponentiation.
--
-- In this formulation, for all natural numbers x, y, z, n,
-- if n > 2 and x * y * z ≠ 0, then
-- x^n + y^n ≠ z^n.
def FermatLastTheorem :=
  ∀ x y z n : ℕ,
    n > 2 ∧ x * y * z ≠ 0 →
      x ^ n + y ^ n ≠ z ^ n

-- Check the type of the definition.
-- FermatLastTheorem is itself a proposition, so its type is Prop.
#check FermatLastTheorem


/-!
SECTION 3: PROOFS OF PROPOSITIONS

A proof is a term that has the proposition it proves as its type.
Theorem declarations give names to proofs.
-/

-- State that 2 + 2 = 4.
theorem easy : 2 + 2 = 4 :=
  -- rfl proves an equality when both sides reduce
  -- to the same expression according to Lean's definitional equality.
  rfl

-- Check the type of easy.
-- Its type is the proposition 2 + 2 = 4.
#check easy

-- Declare a theorem with the statement FermatLastTheorem.
theorem hard : FermatLastTheorem :=
  -- sorry is a placeholder for a missing proof.
  -- Lean accepts it in ordinary development, but it does NOT
  -- provide a completed, verified proof of the theorem.
  sorry

-- Check the type of hard.
#check hard


/-!
SECTION 4: PROVING THAT A PRODUCT IS EVEN

The theorem we want to prove is:

For every pair of natural numbers m and n,
if n is even, then m * n is even.

The mathematical idea is:
  If n = k + k,
  then m * n = m * (k + k) = m * k + m * k.
Therefore m * n is even.
-/


/-!
PROOF 1: USING fun, have, and show

This proof explicitly names an intermediate equality.
-/

example : ∀ m n : Nat, Even n → Even (m * n) :=
  -- fun introduces the inputs m and n, followed by a proof
  -- that n is even.
  --
  -- Even n means there exists a natural number k such that
  -- n = k + k.
  --
  -- ⟨k, hk⟩ unpacks this existential proof:
  -- k  : Nat
  -- hk : n = k + k
  fun m n ⟨k, (hk : n = k + k)⟩ ↦

    -- have proves an intermediate fact and gives it a name.
    -- Here we want to establish:
    -- m * n = m * k + m * k.
    have hmn : m * n = m * k + m * k := by

      -- rw [hk] replaces n with k + k.
      -- rw [mul_add] applies distributivity:
      -- m * (k + k) = m * k + m * k.
      rw [hk, mul_add]

    -- State the final goal explicitly:
    -- there exists a natural number l such that
    -- m * n = l + l.
    --
    -- This is the existential form of Even (m * n).
    show ∃ l, m * n = l + l from

      -- Construct the existential proof.
      -- The underscore _ asks Lean to infer the witness l.
      -- Lean infers l = m * k.
      -- hmn supplies the proof of the required equality.
      ⟨_, hmn⟩


/-!
PROOF 2: A SHORTER TERM-STYLE PROOF

The same reasoning, but without naming the intermediate equality.
-/

example : ∀ m n : Nat, Even n → Even (m * n) :=
  -- Introduce m and n, and unpack the proof that n is even.
  fun m n ⟨k, hk⟩ ↦

    -- Construct the existential proof directly.
    -- First choose m * k as the witness.
    -- Then prove m * n = m * k + m * k by rewriting.
    ⟨m * k, by rw [hk, mul_add]⟩


/-!
PROOF 3: USING TACTICS STEP BY STEP

The by keyword begins a tactic proof.
Each tactic transforms the current goal or uses information
available in the proof context.
-/

example : ∀ m n : Nat, Even n → Even (m * n) := by

  -- Introduce m, n, and the assumption that n is even.
  -- Unpack Even n into a witness k and a proof hk : n = k + k.
  rintro m n ⟨k, hk⟩

  -- Choose m * k as the witness showing that m * n is even.
  -- The remaining goal is:
  -- m * n = m * k + m * k.
  use m * k

  -- Replace n using hk : n = k + k.
  -- The goal becomes:
  -- m * (k + k) = m * k + m * k.
  rw [hk]

  -- Prove the remaining polynomial equality.
  -- ring normalizes both sides using algebraic rules.
  ring


/-!
PROOF 4: THE SAME TACTICS ON ONE LINE

Semicolons allow several tactics to be written on one line.
They are executed in sequence.
-/

example : ∀ m n : Nat, Even n → Even (m * n) := by

  -- Introduce the variables and unpack evenness;
  -- choose m * k as the witness;
  -- substitute n = k + k;
  -- prove the resulting algebraic identity.
  rintro m n ⟨k, hk⟩; use m * k; rw [hk]; ring


/-!
PROOF 5: USING SIMPLIFICATION

This version asks Lean's simplifier to solve the goal
using the available hypotheses and parity simplification rules.
-/

example : ∀ m n : Nat, Even n → Even (m * n) := by

  -- Introduce the variables and the assumption.
  -- Lean creates a context containing m, n, and h : Even n,
  -- with the goal Even (m * n).
  intros

  -- simp simplifies expressions and can close goals using
  -- known simplification rules.
  --
  -- * tells simp to use the hypotheses in the context.
  -- parity_simps supplies additional parity-related rules
  -- available in this Mathematics in Lean environment.
  simp [*, parity_simps]


**Important:** `import MIL.Common` should appear only once in the actual file; it is repeated above only to introduce the first section's explanation. In your working file, keep the import at the very top and remove the duplicate line inside the comments.
