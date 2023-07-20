import Mathlib.Data.Set.Basic

/-! # Enderton.Set.Chapter_4

Natural Numbers
-/

namespace Enderton.Set.Chapter_4

/-- #### Theorem 4C

Every natural number except `0` is the successor of some natural number.
-/
theorem theorem_4c (n : ℕ)
  : n = 0 ∨ (∃ m : ℕ, n = m.succ) := by
  match n with
  | 0 => simp
  | m + 1 => simp

/-- #### Exercise 4.1

Show that `1 ≠ 3` i.e., that `∅⁺ ≠ ∅⁺⁺⁺`.
-/
theorem exercise_4_1 : 1 ≠ 3 := by
  simp

end Enderton.Set.Chapter_4