import Common.Real.Basic

/-! # Common.Real.Rational

Additional theorems and definitions useful in the context of rational numbers.
Most of these will likely be deleted once the corresponding functions in
`Mathlib` are ported to Lean 4.
-/

/--
Assert that a real number is irrational.
-/
def irrational (x : ℝ) := x ∉ Set.range RatCast.ratCast

/--
Assert that a real number is rational.
-/
def rational (x : ℝ) := ¬ irrational x
