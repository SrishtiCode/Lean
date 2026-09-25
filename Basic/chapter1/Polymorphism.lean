-- Polymorphism

-- In functional programming, the term polymorphism typically refers to datatypes and definitions that take types as arguments.

-- The Point structure requires that both the x and y fields are Floats. There is, however, nothing about points that require a specific representation for each coordinate. A polymorphic version of Point, called PPoint, can take a type as an argument, and then use that type for both fields:

structure PPoint (α : Type) where
  x : α
  y : α

def natOrigin : PPoint Nat :=
  { x := Nat.zero, y := Nat.zero }

-- Write a function to find the last entry in a list. It should return an Option.

set_option autoImplicit true

def last? : List α → Option α
  | [] => none --empty list, so there is no last element → none
  | [x] => some x --one-element list, so x is the last element → some x
  |  _:: xs => last? xs --more than one element, ignore the first element and search xs, here function calling itself last? until it gets last element.

#eval last? [1, 2, 3, 4]

-- Write a function that finds the first entry in a list that satisfies a given predicate.
-- Start the definition with def List.
-- findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α := ….

def List.findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α :=
  match xs with
  | [] => none
  | x :: xs =>
    if predicate x then
      some x
    else
      List.findFirst? xs predicate


-- Write a function Prod.switch that switches the two fields in a pair for each other. Start the definition with def Prod.switch {α β : Type} (pair : α × β) : β × α := ….

def Prod.switch {α β : Type} (pair : α × β) : β × α :=
  match pair with
  | (a, b) => (b, a)

#eval Prod.switch (10, "hello")

-- Rewrite the PetName example to use a custom datatype and compare it to the version that uses Sum.

inductive PetName : Type where
  | dog : String → PetName
  | cat : String → PetName

def animals : List PetName :=
  [PetName.dog "Spot",
   PetName.cat "Tiger",
   PetName.dog "Fifi",
   PetName.dog "Rex",
   PetName.cat "Floof"]

def howManyDogs (pets : List PetName) : Nat :=
  match pets with
  | [] => 0
  | PetName.dog _ :: morePets =>
      howManyDogs morePets + 1
  | PetName.cat _ :: morePets =>
      howManyDogs morePets

#eval howManyDogs animals

-- Write a function zip that combines two lists into a list of pairs. The resulting list should be as long as the shortest input list. Start the definition with def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) := ….

def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
  match xs, ys with
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys =>
      (x, y) :: zip xs ys

#eval zip [1, 2, 3] ["a", "b"]


-- Write a polymorphic function take that returns the first nn entries in a list, where nn is a Nat. If the list contains fewer than nn entries, then the resulting list should be the entire input list. #eval take 3 ["bolete", "oyster"] should yield ["bolete", "oyster"], and #eval take 1 ["bolete", "oyster"] should yield ["bolete"].

def take {α : Type} (n : Nat) (xs : List α) : List α :=
  match n, xs with
  | 0, _ => []
  | _, [] => []
  | n + 1, x :: xs =>
      x :: take n xs

#eval take 3 ["bolete", "oyster"]


#eval take 1 ["bolete", "oyster"]

-- Using the analogy between types and arithmetic, write a function that distributes products over sums. In other words, it should have type α × (β ⊕ γ) → (α × β) ⊕ (α × γ).

def distribute {α β γ : Type} (x : α × (β ⊕ γ)) :
    (α × β) ⊕ (α × γ) :=
  match x with
  | (a, Sum.inl b) => Sum.inl (a, b)
  | (a, Sum.inr c) => Sum.inr (a, c)


--  Using the analogy between types and arithmetic, write a function that turns multiplication by two into a sum. In other words, it should have type Bool × α → α ⊕ α.

def boolToSum {α : Type} (pair : Bool × α) : α ⊕ α :=
  match pair with
  | (false, x) => Sum.inl x
  | (true, x) => Sum.inr x
