/-  **Basics**  -/

/-**1. Calculating**-/
import Mathlib.Data.Real.Basic

#check a -- a : ℝ  
#check a + b -- a + b : ℝ   
#check (a : ℝ) -- a : ℝ
#check mul_comm a b -- mul_comm a b : a * b = b * a  
#check (mul_comm a b : a * b = b * a) -- mul_comm a b : a * b = b * a
#check mul_assoc c a b -- mul_assoc c a b : c * a * b = c * (a * b)   
#check mul_comm a -- mul_comm a : ∀ (b : ℝ), a * b = b * a
#check mul_comm -- mul_comm.{u_1} {G : Type u_1} [CommMagma G] (a b : G) : a * b = b * a

#check pow_two a -- pow_two a : a ^ 2 = a * a
#check mul_sub a b c -- mul_sub a b c : a * (b - c) = a * b - a * c
#check add_mul a b c -- add_mul a b c : (a + b) * c = a * c + b * c
#check add_sub a b c -- add_sub a b c : a + (b - c) = a + b - c
#check sub_sub a b c -- sub_sub a b c : a - b - c = a - (b + c)
#check add_zero a -- add_zero a : a + 0 = a

/-**2. Proving_Identites_in_Algebraic_Structures**-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))  -- add_assoc : ∀ (a b c : R), a + b + c = a + (b + c)
#check (add_comm : ∀ a b : R, a + b = b + a) -- add_comm : ∀ (a b : R), a + b = b + a 
#check (zero_add : ∀ a : R, 0 + a = a) -- zero_add : ∀ (a : R), 0 + a = a
#check (neg_add_cancel : ∀ a : R, -a + a = 0) -- neg_add_cancel : ∀ (a : R), -a + a = 0
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c)) -- mul_assoc : ∀ (a b c : R), a * b * c = a * (b * c)
#check (mul_one : ∀ a : R, a * 1 = a) -- mul_one : ∀ (a : R), a * 1 = a
#check (one_mul : ∀ a : R, 1 * a = a) -- one_mul : ∀ (a : R), 1 * a = a
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c) -- mul_add : ∀ (a b c : R), a * (b + c) = a * b + a * c
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c) -- add_mul : ∀ (a b c : R), (a + b) * c = a * c + b * c

#check MyRing.add_zero -- MyRing.add_zero.{u_1} {R : Type u_1} [Ring R] (a : R) : a + 0 = a
#check add_zero -- MyRing.add_zero.{u_1} {R : Type u_1} [Ring R] (a : R) : a + 0 = a

#check sub_add_cancel -- sub_add_cancel.{u_1} {G : Type u_1} [AddGroup G] (a b : G) : a - b + b = a

#check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c)) -- add_assoc : ∀ (a b c : A), a + b + c = a + (b + c) 
#check (zero_add : ∀ a : A, 0 + a = a) -- zero_add : ∀ (a : A), 0 + a = a
#check (neg_add_cancel : ∀ a : A, -a + a = 0) -- neg_add_cancel : ∀ (a : A), -a + a = 0

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)) --mul_assoc : ∀ (a b c : G), a * b * c = a * (b * c) 
#check (one_mul : ∀ a : G, 1 * a = a) -- one_mul : ∀ (a : G), 1 * a = a
#check (inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1) -- inv_mul_cancel : ∀ (a : G), a⁻¹ * a = 1

/-**3. Using_Theorems_and_Lemmas**-/
import MIL.Common

#check (le_refl : ∀ a : ℝ, a ≤ a) -- le_refl : ∀ (a : ℝ), a ≤ a
#check (le_trans : a ≤ b → b ≤ c → a ≤ c) -- le_trans : a ≤ b → b ≤ c → a ≤ c

section
variable (h : a ≤ b) (h' : b ≤ c)

#check (le_refl : ∀ a : Real, a ≤ a) 
#check (le_refl a : a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (le_trans h : b ≤ c → a ≤ c)
#check (le_trans h h' : a ≤ c)

#check (le_refl : ∀ a, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (lt_of_le_of_lt : a ≤ b → b < c → a < c)
#check (lt_of_lt_of_le : a < b → b ≤ c → a < c)
#check (lt_trans : a < b → b < c → a < c)

#check (exp_le_exp : exp a ≤ exp b ↔ a ≤ b)
#check (exp_lt_exp : exp a < exp b ↔ a < b)
#check (log_le_log : 0 < a → a ≤ b → log a ≤ log b)
#check (log_lt_log : 0 < a → a < b → log a < log b)
#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (add_le_add_right : a ≤ b → ∀ c, c + a ≤ c + b)
#check (add_le_add_left : a ≤ b → ∀ c, a + c ≤ b + c)
#check (add_lt_add_of_le_of_lt : a ≤ b → c < d → a + c < b + d)
#check (add_lt_add_of_lt_of_le : a < b → c ≤ d → a + c < b + d)
#check (add_lt_add_right : a < b → ∀ c, c + a < c + b)
#check (add_lt_add_left : a < b → ∀ c, a + c < b + c)
#check (add_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a + b)
#check (add_pos : 0 < a → 0 < b → 0 < a + b)
#check (add_pos_of_pos_of_nonneg : 0 < a → 0 ≤ b → 0 < a + b)
#check (exp_pos : ∀ a, 0 < exp a)
#check add_le_add_right --add_le_add_right.{u_1} {α : Type u_1} [Add α] [LE α] [AddLeftMono α] {b c : α} (bc : b ≤ c) (a : α) : a + b ≤ a + c

#check abs_le'.mpr --abs_le'.mpr : ?m.4 ≤ ?m.5 ∧ -?m.4 ≤ ?m.5 → |?m.4| ≤ ?m.5

/-**4. More_on_Order_and_Divisibility**-/
import Mathlib.Data.Real.Basic

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

#check (abs_add_le : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

/-**5. Proving_Facts_about_Algebraic_Structures**-/
import Mathlib.Topology.MetricSpace.Basic

#check x ≤ y -- x ≤ y : Prop
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)

#check x < y
#check (lt_irrefl x : ¬ (x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

-- ⊓ = infimum / meet
-- ⊔ = supremum / join
variable {α : Type*} [Lattice α]
variable (x y z : α)
#check x ⊓ y -- x ⊓ y : α
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

variable {α : Type*} [DistribLattice α]
variable (x y z : α)
#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))

variable {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable (a b c : R)
#check (add_le_add_right : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)
#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

variable {X : Type*} [MetricSpace X]
variable (x y z : X)
#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)








