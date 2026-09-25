-- Additional Conveniences

--Normally you might write:

--def length {α : Type} (xs : List α) : Nat :=

--But Lean can infer α, so you can write:

--def length (xs : List α) : Nat :=

--Lean automatically creates {α : Type} as an implicit parameter when it can determine its type.

/-
If you have:

set_option autoImplicit false

then you must write:

{α : Type}

explicitly.
-/


-- Pattern-matching definitions
--Instead of:
def length (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | y :: ys => Nat.succ (length ys)

-- you can put the patterns directly after the type:

def length : List α → Nat
  | [] => 0
  | y :: ys => Nat.succ (length ys)

--Local definitions with let


--Instead:

let unzipped := unzip xys

--and then:

unzipped.fst
unzipped.snd

--Now the recursive result is computed once and reused.

