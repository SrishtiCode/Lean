/- Define some constants. -/

def m : Nat := 1       -- m is a natural number
def n : Nat := 0
def b1 : Bool := true  -- b1 is a Boolean
def b2 : Bool := false

/- Check their types. -/

#check m#check n#check n + 0#check m * (n + 0)#check b1-- "&&" is the Boolean and
#check b1 && b2-- Boolean or
#check b1 || b2-- Boolean "true"
#check true/- Evaluate -/

#eval 5 * 4
#eval m + 2
#eval b1 && b2

#check Nat → Nat      -- type the arrow as “\to” or "\r"
#check Nat -> Nat     -- alternative ASCII notation
#check Nat × Nat      -- type the product as "\times"
#check Prod Nat Nat   -- alternative notation
#check Nat → Nat → Nat
#check Nat → (Nat → Nat)  -- same type as above
#check Nat × Nat → Nat
#check (Nat → Nat) → Nat -- a "functional"


#check Nat.succ#check (0, 1)
#check Nat.add
#check Nat.succ 2
#check Nat.add 3
#check Nat.add 5 2
#check (5, 9).1
#check (5, 9).2
#eval Nat.succ 2
#eval Nat.add 5 2
#eval (5, 9).1
#eval (5, 9).2
