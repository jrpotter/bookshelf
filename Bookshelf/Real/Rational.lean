import Bookshelf.Real.Basic

/--
Assert that a real number is irrational.
-/
def irrational (x : ℝ) := x ∉ Set.range RatCast.ratCast

/--
Assert that a real number is rational.

Note this does *not* require the found rational to be in reduced form. Members
of `ℚ` expect this (by proving the numerator and denominator are co-prime).
-/
def rational (x : ℝ) := ¬ irrational x
