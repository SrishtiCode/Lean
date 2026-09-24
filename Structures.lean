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
