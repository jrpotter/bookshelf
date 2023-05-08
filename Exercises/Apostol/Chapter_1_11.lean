import Bookshelf.Real.Int
import Mathlib.Data.Real.Basic

/-! # Exercises.Apostol.Exercises_1_11 -/

namespace Exercises.Apostol.Exercises_1_11

/-! ## Exercise 4

Prove that the greatest-integer function has the properties indicated.
-/

/-- ### Exercise 4a

`⌊x + n⌋ = ⌊x⌋ + n` for every integer `n`.
-/
theorem exercise_4a (x : ℝ) (n : ℤ) : ⌊x + n⌋ = ⌊x⌋ + n := by
  sorry

/-- ### Exercise 4b

`⌊-x⌋ = -⌊x⌋` if `x` is an integer.
`⌊-x⌋ = -⌊x⌋ - 1` otherwise.
-/
theorem exercise_4b (x : ℝ)
  : (Real.isInt x → ⌊-x⌋ = -⌊x⌋)
  ∨ (¬Real.isInt x → ⌊-x⌋ = -⌊x⌋ - 1) := by
  sorry

/-- ### Exercise 4c

`⌊x + y⌋ = ⌊x⌋ + ⌊y⌋` or `⌊x⌋ + ⌊y⌋ + 1`.
-/
theorem exercise_4c (x y : ℝ)
  : ⌊x + y⌋ = ⌊x⌋ + ⌊y⌋ ∨ ⌊x + y⌋ = ⌊x⌋ + ⌊y⌋ + 1 := by
  sorry

/-- ### Exercise 4d

`⌊2x⌋ = ⌊x⌋ + ⌊x + 1/2⌋`
-/
theorem exercise_4d (x : ℝ)
  : ⌊2 * x⌋ = ⌊x⌋ + ⌊x + 1/2⌋ := by
  sorry

/-- ### Exercise 4e

`⌊3x⌋ = ⌊x⌋ + ⌊x + 1/3⌋ + ⌊x + 2/3⌋`
-/
theorem exercise_4e (x : ℝ)
  : ⌊3 * x⌋ = ⌊x⌋ + ⌊x + 1/3⌋ + ⌊x + 2/3⌋ := by
  sorry

/-- ### Exercise 5

The formulas in Exercises 4(d) and 4(e) suggest a generalization for `⌊nx⌋`.
State and prove such a generalization.
-/
theorem exercise_5 (n : ℕ) (x : ℝ)
  : ⌊n * x⌋ = 10 := by
  sorry

/-- ### Exercise 7b

If `a` and `b` are positive integers with no common factor, we have the formula
`Σ_{n=1}^{b-1} ⌊na / b⌋ = ((a - 1)(b - 1)) / 2`. When `b = 1`, the sum on the
left is understood to be `0`.

Derive the result analytically as follows: By changing the index of summation,
note that `Σ_{n=1}^{b-1} ⌊na / b⌋ = Σ_{n=1}^{b-1} ⌊a(b - n) / b⌋`. Now apply
Exercises 4(a) and (b) to the bracket on the right.
-/
theorem exercise_7b : True := sorry

end Exercises.Apostol.Exercises_1_11
