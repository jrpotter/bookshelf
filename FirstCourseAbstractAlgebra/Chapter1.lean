/-
Chapter 1

Introduction and Examples
-/

import Mathlib.Data.Complex.Basic

open Complex
open HPow

-- In Exercises 1 through 9 compute the given arithmetic expression and give the
-- answer in the form $a + bi$ for $a, b ∈ ℝ$.

theorem ex1_1 : I^3 = 0 + (-1) * I := calc
  I^3
    = I * (I * hPow I 1) := rfl
  _ = 0 + (-1) * I := by simp
