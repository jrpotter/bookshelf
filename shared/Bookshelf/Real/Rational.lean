import Bookshelf.Real.Basic

/--
Assert that a real number is rational.

Note this does *not* require the found rational to be in reduced form. Members
of `ℚ` expect this (by proving the numerator and denominator are coprime).
-/
def rational (x : ℝ) := ∃ a : ℤ, ∃ b : ℕ, b ≠ 0 ∧ x = a / b

/--
Assert that a real number is irrational.
-/
def irrational (x : ℝ) := ¬ rational x