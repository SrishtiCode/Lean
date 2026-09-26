import Mathlib.Data.Real.Basic

/-
# Logics

* Get used to be precise about logical connective, phrases like "to prove
  `A ^ B` we have to prove `A` and `B`." are awkward but necessary.

Overview of the most important connectives:

→  \to    if ... then ...         implication
∀  \all   for all                 universal quantification
∃  \ex    there exists            existential quantification
¬  \not   not                     negation
∧  \and   and                     conjuction
∨  \or    or                      disjunction
↔  \iff   ... if and only iff...  biimplication
False     contradiction!          falsity
True      this is trivial         truth

... and how to use them:

            appearing as hypothesis `h`                  appearing as goal
`A → B`     `have h' := h ha`, `apply h`                 `intro ha`
`∀ x, P x`  `have h' := x`, `apply h`, `specialize`      `intro x`
`A ∧ B`     `rcases h with ⟨ha, hb⟩`, `h.1`, `h.2`       `constructor`
`A ∨ B`     `rcases h with (ha | hb)`                    `left` or `right`
`∃ x. P x ` `rcases h with ⟨x, hx⟩`                      `constructor` or `use x`
`False`     `contradiction`                               --
`True`      --                                           `trivial`
`¬ A`       `contradiction`                              `intro ha`
`A ↔ B`     `rcases h with ⟨h₁, h₂⟩`                     `constructor`

* `by_contra` for proofs by contradiction
* Note that logical connectives can be hidden under other definitions:
  `a | b` is existential, `s ⊆ t` is universal.
-/

/-!
## implication and universal quantifiers
-/

theorem my_add_le_add (x y z w : ℝ) (h₁ : x ≤ y) (h₂ : z ≤ w) :
    x + z ≤ y + w :=
  add_le_add h₁ h₂

section

variable (a b c d : ℝ )
variable (h₁ : a ≤ b) (h₂ : c ≤ d)

#check @my_add_le_add
#check my_add_le_add a b
#check my_add_le_add a b c d h₁
#check my_add_le_add _ _ _ _ h₁
#check my_add_le_add _ _ _ _ h₁ h₂


