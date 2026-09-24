-- Every program in Lean must have a type.

-- In particular, every expression must have a type before it can be evaluated.
-- In the examples so far, Lean has been able to discover a type on its own,
-- but it is sometimes necessary to provide one. This is done using the colon operator inside parentheses

#eval (1+2 : Nat) --Nat is the type of natural numbers, which are arbitrary-precision unsigned integers.

-- In Lean, Nat is the default type for non-negative integer literals.

#eval (1-2 : Nat) -- 0

-- evaluates to 0 rather than -1

-- To use a type that can represent the negative integers, provide it directly:

#eval (1-2 : Int) -- -1
-- With this type, the result is -1, as expected.


-- To check the type of an expression without evaluating it, use #check instead of #eval
#check (1-2 : Int)
-- reports 1 - 2 : Int without actually performing the subtraction.


