/-Evaluating expressions-/

-- Evaluation is the process of finding the value of an expression, just as one does in arithmetic

#eval 1+2

-- Lean obeys the ordinary rules of precedence and associativity for arithmetic operators.

#eval 1 + 2 * 5 -- yields the value 11 rather than 15

--Lean simply writes the function next to its arguments (e.g. f x).

#eval String.append "Hello, " "Lean!"


#eval String.append "great " (String.append "oak " "tree")


/-#eval String.append "it is "

yields a quite long error message:

Could not synthesize a `ToExpr`, `Repr`, or `ToString` instance for type
  String → String

This message occurs because Lean functions that are applied to only some of their arguments return new functions that are waiting for the rest of the arguments. Lean cannot display functions to users, and thus returns an error when asked to do so.-/

-- Exercises
-- What are the values of the following expressions? Work them out by hand, then enter them into Lean to check your work.

-- 42 + 19
#eval 42 + 19 --61

-- String.append "A" (String.append "B" "C")

#eval String.append "A" (String.append "B" "C") -- "ABC"

-- String.append (String.append "A" "B") "C"

#eval String.append (String.append "A" "B") "C" -- "ABC"

-- if 3 == 3 then 5 else 7

#eval if 3==3 then 5 else 7 -- 5

-- if 3 == 4 then "equal" else "not equal"

#eval if 3 == 4 then "equal" else "not equal"  --"not equal"


