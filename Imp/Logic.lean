import Mathlib

/- **Logic** -/

/-**1. Implication_and_the_Universal_Quantifier **-/

#check ∀ x : ℝ, 0 ≤ x → |x| = x 
#check ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε


/-- If `|x|` and `|y|` are both below `ε ≤ 1`, so is `|x * y|`. -/
theorem my_lemma : ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  calc |x * y| = |x| * |y| := abs_mul x y
    _ ≤ |x| * ε := by gcongr
    _ < 1 * ε := by gcongr; exact xlt.trans_le ele1
    _ = ε := one_mul ε

/-- `my_lemma` with the variables made implicit. -/
theorem my_lemma2 {x y ε : ℝ} (epos : 0 < ε) (ele1 : ε ≤ 1) (xlt : |x| < ε) (ylt : |y| < ε) :
    |x * y| < ε :=
  my_lemma x y ε epos ele1 xlt ylt

variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma a b δ  -- my_lemma a b δ : 0 < δ → δ ≤ 1 → |a| < δ → |b| < δ → |a * b| < δ
#check my_lemma a b δ h₀ h₁  -- my_lemma a b δ h₀ h₁ : |a| < δ → |b| < δ → |a * b| < δ
#check my_lemma a b δ h₀ h₁ ha hb  -- my_lemma a b δ h₀ h₁ ha hb : |a * b| < δ

section
variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma2 h₀ h₁ ha hb --my_lemma2 h₀ h₁ ha hb : |a * b| < δ

/-**2. Negation Lean**-/

#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)

end
