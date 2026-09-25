import Mathlib

open Real

-- # Intro

-- Lean is a dependently-typed language.

-- Every expression has a type, and `#check` can tell you the type

#check 2 -- 2 : ℕ
#check 17 + 4 --17 + 4 : ℕ
#check π --π : ℝ
#check rexp 1 -- rexp 1 : ℝ

-- Types are expression too!

#check ℕ   -- ℕ : Type
#check ℝ   -- ℝ : Type

-- We can also make our own expressions, and give them names
def myFavouriteNumber : ℕ := 18

def yourFavouriteNumber : ℕ := sorry
-- sorry works as a placeholder where you put sorry if you don't sure about it or know it yet

#check  myFavouriteNumber --myFavouriteNumber : ℕ

-- or not give a name
example : ℕ := 2

-- # But this not a math!

-- The type `Prop` contains `Prop`ositions..

#check 2 + 2 = 4 --  2 + 2 = 4 : Prop
#check rexp 1 < π  --  rexp 1 < π : Prop

-- including false propositions

#check 2 + 2 = 5 --2 + 2 = 5 : Prop

-- and open questions
#check Irrational (rexp 1 + π) --Irrational (rexp 1 + π) : Prop
#check myFavouriteNumber = yourFavouriteNumber -- myFavouriteNumber = yourFavouriteNumber : Prop

def MyDifficultProposition : Prop := ∀ n : ℕ, ∃ p, n ≤ p ∧ Prime p ∧ Prime (p+2)
def MyEasyProposition : Prop := ∀ n : ℕ, ∃ p, n ≤ p ∧ Prime p ∧ Prime (p+2) ∧ Prime (p+4)
def MyVeryEasyProposition : Prop := ∀ n : ℕ , ∃ p, n ≤ p

-- Key! If `p : Prop`, an expression of type `p` is a proof of `p`.

--rfl = the two sides compute to the same thing.
example : 2+2=4 := rfl  --reflexivity

-- simp = simplify the goal using known simplification rules.
example : 2+2≠5 := by simp --simplifies/proves this automatically.

--Erdős–Straus conjecture (not solved yet)
-- Universal version -  For every n, if 2 ≤ n, then there exist x, y, z such that...
example : ∀ n : ℕ, 2 ≤ n →
  ∃ x y z : ℕ , 4 * x * y * z = n * ( x * y + x * z + y * z) :=
  sorry

--Assumption already provided
example (n : ℕ ) (hn : 2 ≤ n) : -- already introduced n and the proof hn as local assumptions
  ∃ x y z : ℕ , 4 * x * y * z = n * ( x * y + x * z + y * z) :=
  sorry

--so in universal we have to introduce n to give the proof for that n and in the assumption n and hm is already given in the context you just need to proof

-- # How can we make these expressions?

-- Simple proof terms

example : True := trivial
example : 2 = 2 := rfl
example (a b : ℕ ) : a + b = b + a := Nat.add_comm a b
example (a b : ℕ ) : a * b = b * a := Nat.mul_comm a b

#print MyVeryEasyProposition -- def MyVeryEasyProposition : Prop := ∀ (n : ℕ), ∃ p, n ≤ p
theorem my_proof : MyVeryEasyProposition := fun n => ⟨n, le_rfl⟩ --For every n, choose p = n, and prove n ≤ n using le_rfl (“less-than-or-equal reflexivity”)

#check MyVeryEasyProposition --MyVeryEasyProposition : Prop
#check my_proof --my_proof : MyVeryEasyProposition

-- my proposition "has type Proposition", or "is a Proposition"
-- my proof "has  type my proposition", or "has type ∀ (n : ℕ), ∃ p, n ≤ p",
-- or "is a proof ∀ (n : ℕ), ∃ p, n ≤ p"

-- But just proof system get ugly...
example (a b : ℕ ) : a + a * b = (b + 1) * a :=
  (add_comm a (a * b)).trans ((mul_add_one a b).symm.trans (mul_comm a (b + 1)))


-- Very clever tactics

example (a b : ℕ ) : a + a * b = (b + 1) * a := by ring

example : 2 + 2 ≠ 5 := by simp --simplifies/proves this automatically.
example : 4 ^ 25 < 3 ^ 39 := by norm_num --normalizing numerical expressions and proving numerical facts.

open Nat

-- Simple tactics

example (a b : ℕ ) : a + b = b + a := by exact Nat.add_comm a b
example : 3 = 3 := by rfl

#check  add_mul (R := ℕ )

-- In practice we write tactic proofs, and write them with help of the infovi
example (a b : ℕ ) : a + a * b = (b + 1) * a := by
  rw [add_mul, one_mul, add_comm, mul_comm]
  --> S01_Calculating.lean has many examples and some more information

theorem Euclid_Thm (n : ℕ) : ∃ p, n ≤ p ∧ Nat.Prime p := by
  let p := minFac (Nat.factorial n + 1)
  have f1 : factorial n + 1 ≠ 1 := Nat.ne_of_gt <| Nat.succ_lt_succ <| factorial_pos _
  have pp : Nat.Prime p := minFac_prime f1
  have np : n ≤ p :=
    le_of_not_ge fun h =>
      have h₁ : p ∣ factorial n := dvd_factorial (minFac_pos _) h
      have h₂ : p ∣ 1 := (Nat.dvd_add_iff_right h₁).2 (minFac_dvd _)
      pp.not_dvd_one h₂
  exact ⟨p, np, pp⟩

theorem Ugly_Euclid_Thm (n : ℕ) : ∃ p, n ≤ p ∧ Nat.Prime p := by
  have h1 : n ! + 1 ≠ 1 := by
    have := Nat.factorial_pos n
    omega
  have pp := Nat.minFac_prime h1
  refine ⟨(n ! + 1).minFac, ?_, pp⟩
  by_contra h
  push Not at h
  have hdvd1 : (n ! + 1).minFac ∣ n ! := Nat.dvd_factorial pp.pos h.le
  have hdvd2 : (n ! + 1).minFac ∣ n ! + 1 := Nat.minFac_dvd _
  exact pp.not_dvd_one ((Nat.dvd_add_right hdvd1).1 hdvd2)
  
-- The proof does not matter
example : Euclid_Thm = Ugly_Euclid_Thm := rfl
-- *to Lean*

--> S02_Overview.lean has more examples of tactic proofs

-- Some tactics can self-replace

theorem Easy_Euclid_Thm (n : ℕ ) : ∃ p, n ≤ p ∧ Nat.Prime p := by exact?

example (a b : ℕ) : a + a * b = (b + 1) * a := by
  rw [Nat.add_mul, Nat.one_mul]
  ring

def MySet : Set ℕ := {1,1}
example : 1 ∈ MySet := by
  rw [MySet]
  simp only [Set.mem_singleton_iff, Set.mem_insert_iff]
  simp
  -- rw [Myset]
  -- rw [@Set.mem_singleton_iff]
#check Set.mem_singleton

-- # Some more difficult proofs
def myFactorial : ℕ → ℕ
  | 0 => 1
  | (n + 1) => (n + 1) * myFactorial n

#check (myFactorial : ℕ → ℕ)

-- Lean can compute too!

#eval myFactorial 10

theorem myFactorial_add_one (n : ℕ) : myFactorial (n + 1) = (n + 1) * myFactorial n := rfl
theorem myFactorial_zero : myFactorial 0 = 1 := rfl

theorem myFactorial_pos (n : ℕ) : 0 < myFactorial n := by
  induction' n with n ih
  · rw [myFactorial_zero]
    simp
  · rw [myFactorial_add_one]
    apply mul_pos
    · exact succ_pos n
    · exact ih

theorem myFactorial_pos' (n : ℕ ) : 0 < myFactorial n := by
  induction n
  case zero =>
    rw [myFactorial_zero]
    simp
  case succ n ih =>
    rw [myFactorial_add_one]
    apply mul_pos
    · exact succ_pos n
    · exact ih
