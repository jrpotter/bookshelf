import Common.Logic.Basic
import Mathlib.Data.Set.Intervals.Basic

namespace Set

/-! # Common.Set.Intervals

Additional theorems around intervals.
-/

theorem Iio_nat_lt_ssubset {m n : ℕ} (h : m < n)
  : Iio m ⊂ Iio n := by
  rw [ssubset_def]
  apply And.intro
  · unfold Iio
    simp only [setOf_subset_setOf]
    intro x hx
    calc x
      _ < m := hx
      _ < n := h
  · show ¬ ∀ x, x < n → x < m
    simp only [not_forall, not_lt, exists_prop]
    exact ⟨m, h, by simp⟩

end Set