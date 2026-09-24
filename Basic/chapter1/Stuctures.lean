-- Structures

-- Defining a structure introduces a completely new type to Lean that can't be reduced to any other type.

-- Lean's floating-point number type is called Float, and floating-point numbers are written in the usual notation.

#check 1.2

#check -454.2123215

#check 0.0

-- When floating point numbers are written with the decimal point, Lean will infer the type Float. If they are written without it, then a type annotation may be necessary.

#check 0

#check (0 : Float)

-- A Cartesian point is a structure with two Float fields, called x and y. This is declared using the structure keyword.

structure Point where
    x: Float
    y: Float

-- After this declaration, Point is a new structure type.
-- The typical way to create a value of a structure type is to provide values for all of its fields inside of curly braces. The origin of a Cartesian plane is where x and y are both zero:

def origin : Point := { x := 0.0, y := 0.0}
#eval origin -- { x := 0.000000, y := 0.000000 }
#eval origin.x -- 0.000000
#eval origin.y -- 0.000000

def addPoints (p1 : Point) (p2 : Point) : Point :=
    { x:= p1.x + p2.x , y := p1.y + p2.y}


#eval addPoints { x := 1.5, y := 32 } { x := -8, y := 0.2 }


def distance (p1 : Point) (p2 : Point) : Float :=
  Float.sqrt (((p2.x - p1.x) ^ 2.0) + ((p2.y - p1.y) ^ 2.0))

#eval distance { x := 1.0, y := 2.0 } { x := 5.0, y := -1.0 }

structure Point3D where
  x : Float
  y : Float
  z : Float

def origin3D : Point3D := { x := 0.0, y := 0.0, z := 0.0 }

--his means that the structure's expected type must be known in order to use the curly-brace syntax. If the type is not known, Lean will not be able to instantiate the structure. For example,
-- #check { x := 0.0, y := 0.0 } leads to the error

#check ({ x := 0.0, y := 0.0 } : Point)

#check { x := 0.0, y := 0.0 : Point}

-- Updating Structures
--  One way to write zeroX is to follow this description literally, filling out the new value for x and manually transferring y:

--This style of programming has drawbacks, however. First off, if a new field is added to a structure, then every site that updates any field at all must be updated, causing maintenance difficulties. Secondly, if the structure contains multiple fields with the same type, then there is a real risk of copy-paste coding leading to field contents being duplicated or switched. Finally, the program becomes long and bureaucratic.

/-
def zeroX (p : Point) : Point :=
  { x := 0, y := p.y }
-/

--Remember that this structure update syntax does not modify existing values—it creates new values that share some fields with old values. Given the point fourAndThree:

-- Lean provides a convenient syntax for replacing some fields in a structure while leaving the others alone.
-- This is done by using the with keyword in a structure initialization.
-- The source of unchanged fields occurs before the with, and the new fields occur after.
--For example, zeroX can be written with only the new x value:


def zeroX (p : Point) : Point :=
  { p with x := 0 }

def fourAndThree : Point :=
  { x := 4.3, y := 3.4 }

#eval fourAndThree -- { x := 4.300000, y := 3.400000 }
#eval zeroX fourAndThree -- { x := 0.000000, y := 3.400000 }
#eval fourAndThree -- { x := 4.300000, y := 3.400000 }

-- One consequence of the fact that structure updates do not modify the original structure is that it becomes easier to reason about cases where the new value is computed from the old one.

-- Behind the Scenes

-- Constructors simply gather the data to be stored in the newly-allocated data structure. It is not possible to provide a custom constructor that pre-processes data or rejects invalid arguments.

-- By default, the constructor for a structure named S is named S.mk
-- Here, S is a namespace qualifier, and mk is the name of the constructor itself. Instead of using curly-brace initialization syntax, the constructor can also be applied directly.
-- However, this is not generally considered to be good Lean style, and Lean even returns its feedback using the standard structure initializer syntax.
#check Point.mk 1.5 2.8 -- { x := 1.5, y := 2.8 } : Point

#check (Point.mk) --Point.mk : Float → Float → Point

-- To override a structure's constructor name, write it with two colons at the beginning. For instance, to use Point.point instead of Point.mk, write:

-- In addition to the constructor, an accessor function is defined for each field of a structure. These have the same name as the field, in the structure's namespace. For Point, accessor functions Point.x and Point.y are generated.

#check (Point.x) --Point.x : Point → Float

#check (Point.y) --Point.y : Point → Float

#eval "one string".append " and another"

def Point.modifyBoth (f : Float → Float) (p : Point) : Point :=
  { x := f p.x, y := f p.y }

#eval fourAndThree.modifyBoth Float.floor -- { x := 4.000000, y := 3.000000 }


-- Exercises

-- Define a structure named RectangularPrism that contains the height, width, and depth of a rectangular prism, each as a Float.

structure RectangularPrism where
    Height : Float
    Width : Float
    Depth : Float

-- Define a function named volume : RectangularPrism → Float that computes the volume of a rectangular prism.

def volume (p: RectangularPrism) : Float :=
    p.Height * p.Width * p.Depth

def box : RectangularPrism :=
  { Height := 2.0
    Width := 3.0
    Depth := 4.0 }

#eval volume box

-- Define a structure named Segment that represents a line segment by its endpoints, and define a function length : Segment → Float that computes the length of a line segment. Segment should have at most two fields.

structure Segment where
    start : Float × Float
    finish : Float × Float

def length (s : Segment) : Float :=
    let dx := s.finish.1 - s.start.1
    let dy := s.finish.2 - s.finish.2
    Float.sqrt (dx * dx + dy * dy)

def s : Segment :=
  { start := (0.0, 0.0)
    finish := (3.0, 4.0) }

#eval length s

-- Which names are introduced by the declaration of RectangularPrism?

#check RectangularPrism
#check RectangularPrism.mk
#check RectangularPrism.Height
#check RectangularPrism.Width
#check RectangularPrism.Depth

--  Which names are introduced by the following declarations of Hamster and Book? What are their types?

structure Hamster where
  name : String
  fluffy : Bool

structure Book where
  title : String
  author : String
  price : Float

#check Hamster
#check Hamster.mk
#check Hamster.name
#check Hamster.fluffy
#check Book
#check Book.mk
#check Book.title
#check Book.author
#check Book.price

/-
Hamster : Type
Hamster.mk : String → Bool → Hamster
Hamster.name : Hamster → String
Hamster.fluffy : Hamster → Bool

Book : Type
Book.mk : String → String → Float → Book
Book.title : Book → String
Book.author : Book → String
Book.price : Book → Float
-/
