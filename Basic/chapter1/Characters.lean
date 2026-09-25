-- Characters, Strings, and Slices

#eval "Hello, " ++ "world"
-- "Hello, world"

#eval String.push "Hello" '!'
-- "Hello!"

#eval "Hello".push '!'
-- "Hello!"


-- Slices

/-
Strings are represented by their UTF-8 encoding as an array of bytes paired with a cached character count.
This means that removing even a single character from a string can result in copying the remaining characters to a new string.
-/

-- String.drop and String.dropEnd, which drop the specified number of characters from the start or end of a string; and String.dropWhile and String.dropEndWhile, which respectively remove all the characters that match a pattern from the beginning or end of a string.
#eval (("small tortoiseshell".drop 6).dropEnd 5).copy
-- "tortoise"


-- Matching

#eval "red admiral".dropEndWhile 'l'
-- red admira

#eval "the the butterfly".dropWhile "the "
-- butterfly

#eval ("a gray grayling".drop 2).dropWhile "gray "
-- grayling

#eval ("red admiral".dropEndWhile Char.isAlpha).copy
-- "red "


