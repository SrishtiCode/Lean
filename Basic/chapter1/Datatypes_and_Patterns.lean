-- Datatypes and Patterns

-- Datatypes that allow choices between different constructors
-- are called sum types.

-- Datatypes that can contain instances of themselves are called
-- recursive datatypes.

-- Recursive sum types are called inductive datatypes.
-- They are called "inductive" because mathematical induction
-- can be used to prove properties about values of these types.

-- When programming with inductive datatypes:

--   1. Pattern matching is used to inspect the value.
--   2. Recursive functions are used to process recursive data.

-- Pattern Matching

-- Pattern matching allows us to determine which constructor
-- was used to create a value and then run the corresponding code.

-- For example, Nat has two constructors:

--   Nat.zero       -- represents 0
--   Nat.succ n     -- represents the successor of n

-- Pattern matching does two things at the same time:
--
--   1. It determines which kind of value we have.
--   2. It gives us access to the data contained inside that value.

-- For example:

--   Nat.succ k

-- means that the number is a successor, and `k` is the number
-- inside the constructor.

-- isZero

-- Input:
--   n : Nat
-- Output:
--   Bool
-- If n is Nat.zero, return true.
-- If n is Nat.succ k, return false.
-- Examples:
--
--   isZero 0 = true
--   isZero 1 = false
--   isZero 10 = false

def isZero (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => false

-- pred

-- `pred` means "predecessor".
-- It returns the number immediately before n.
-- For zero, we return zero because Nat does not contain
-- negative numbers.

--   pred 0 = 0
--   pred 1 = 0
--   pred 2 = 1
--   pred 3 = 2
--
-- In the second pattern:
--   Nat.succ k
-- `k` is the predecessor, so we simply return k.

def pred (n : Nat) : Nat :=
  match n with
  | Nat.zero => Nat.zero
  | Nat.succ k => k

-- Evaluate the predecessor of 0.
-- Expected result: 0
#eval pred 0

-- Evaluate the predecessor of 839.
-- Expected result: 838
#eval pred 839

-- even
-- `even` checks whether a natural number is even.
--
-- The important idea here is recursion.
--
-- Base case:
--
--   0 is even.
--
-- Recursive case:
--
--   If n = Nat.succ k, then n is even exactly when k is odd.
--   Therefore we negate the result of `even k`.
--
-- Examples:
--
--   even 0 = true
--   even 1 = false
--   even 2 = true
--   even 3 = false
--   even 4 = true
--
-- The function repeatedly reduces the number:
--
--   even 4
--     -> not (even 3)
--     -> not (not (even 2))
--     -> ...
--     -> true

def even (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => not (even k)


-- plus

-- `plus` adds two natural numbers.
--
-- We perform pattern matching on the SECOND argument, `k`.
--
-- Base case:
--
--   n + 0 = n
--
-- Recursive case:
--
--   n + (k + 1) = (n + k) + 1
--
-- In Lean, `Nat.succ k'` represents k' + 1.
--
-- So:
--
--   plus n (Nat.succ k')
--
-- becomes:
--
--   Nat.succ (plus n k')
--
-- Example:
--
--   plus 3 2
--
--   -> Nat.succ (plus 3 1)
--   -> Nat.succ (Nat.succ (plus 3 0))
--   -> Nat.succ (Nat.succ 3)
--   -> 5

def plus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => n
  | Nat.succ k' => Nat.succ (plus n k')



-- times


-- `times` multiplies two natural numbers.
--
-- Multiplication can be defined using repeated addition.
--
-- Base case:
--
--   n * 0 = 0
--
-- Recursive case:
--
--   n * (k + 1) = n + (n * k)
--
-- Therefore, when k is a successor, we:
--
--   1. Recursively calculate n * k'
--   2. Add n to the result
--
-- Example:
--
--   times 3 2
--
--   -> plus 3 (times 3 1)
--   -> plus 3 (plus 3 (times 3 0))
--   -> plus 3 (plus 3 0)
--   -> 6

def times (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => Nat.zero
  | Nat.succ k' => plus n (times n k')


-- minus


-- `minus` performs natural-number subtraction.
--
-- Again, we pattern match on the SECOND argument, `k`.
--
-- Base case:
--
--   n - 0 = n
--
-- Recursive case:
--
--   n - (k + 1) = pred (n - k)
--
-- We repeatedly apply `pred` to subtract one.
--
-- Because we are working with Nat, subtraction cannot produce
-- a negative number.
--
-- For example:
--
--   minus 5 2
--
--   -> pred (minus 5 1)
--   -> pred (pred (minus 5 0))
--   -> pred (pred 5)
--   -> 3
--
-- And:
--
--   minus 2 5
--
-- eventually becomes 0 rather than -3.

def minus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => n
  | Nat.succ k' => pred (minus n k')

