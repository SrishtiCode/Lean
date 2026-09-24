-- Functions and Definitions

--In Lean, definitions are introduced using the def keyword.

--For instance, to define the name hello to refer to the string "Hello", write:
def hello := "Hello"

--In Lean, new names are defined using the colon-equal operator := rather than =.
--This is because = is used to describe equalities between existing expressions, and using two different operators helps prevent confusion.

--In the definition of hello, the expression "Hello" is simple enough that Lean is able to determine the definition's type automatically

--However, most definitions are not so simple, so it will usually be necessary to add a type. This is done using a colon after the name being defined:
def lean : String := "Lean"

#eval String.append hello (String.append " " lean) -- "Hello Lean"

--  Defining Functions

--There are a variety of ways to define functions in Lean.
--The simplest is to place the function's arguments before the definition's type, separated by spaces.
--For instance, a function that adds one to its argument can be written:

def add1 (n: Nat) : Nat := n+1
#eval add1 7

--Just as functions are applied to multiple arguments by writing spaces between each argument, functions that accept multiple arguments are defined with spaces between the arguments' names and types.
--The function maximum, whose result is equal to the greatest of its two arguments, takes two Nat arguments n and k and returns a Nat.

def maximum (n : Nat) (k : Nat) : Nat :=
    if n < k then
        k
    else n

-- Similarly, the function spaceBetween joins two strings with a space between them.

def spaceBetween (before : String) (after : String) : String :=
    String.append before (String.append " " after)

-- Exercises
-- Define the function joinStringsWith with type String → String → String → String that creates a new string by placing its first argument between its second and third arguments. joinStringsWith ", " "one" "and another" should evaluate to "one, and another".
def joinStringsWith (separator : String) (first : String) (second : String) : String :=
  String.append first (String.append separator second)

#eval joinStringsWith ", " "one" "and another"

-- What is the type of joinStringsWith ": "? Check your answer with Lean.
#check joinStringsWith ": "

-- Define a function volume with type Nat → Nat → Nat → Nat that computes the volume of a rectangular prism with the given height, width, and depth.

def rectvolume (height width depth : Nat) : Nat :=
    height * width * depth
#eval rectvolume 2 3 4
#check rectvolume

