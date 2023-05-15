import Mathlib.Data.Complex.Basic

/-! # Fraleign.Chapter1

Introduction and Examples
-/

namespace Fraleign.Chapter1

open Complex
open HPow

/-! ## Exercises 1 Through 9

In Exercises 1 through 9 compute the given arithmetic expression and give the
answer in the form `a + bi` for `a, b ∈ ℝ`.
-/

theorem exercise1 : I^3 = 0 + (-1) * I := calc
  I^3
    = I * (I * hPow I 1) := rfl
  _ = 0 + (-1) * I := by simp

end Fraleign.Chapter1