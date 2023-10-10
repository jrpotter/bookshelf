import Common.Logic.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Intervals.Basic

namespace Set

/-! # Common.Set.Intervals

Additional theorems around intervals.
-/

/--
If `m < n` then `{0, …, m - 1} ⊂ {0, …, n - 1}`.
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

/--
It is never the case that the emptyset is surjective
-/
theorem SurjOn_emptyset_Iio_iff_eq_zero {n : ℕ} {f : α → ℕ}
  : SurjOn f ∅ (Set.Iio n) ↔ n = 0 := by
  apply Iff.intro
  · intro h
    unfold SurjOn at h
    rw [subset_def] at h
    simp only [mem_Iio, image_empty, mem_empty_iff_false] at h
    by_contra nh
    exact h 0 (Nat.pos_of_ne_zero nh)
  · intro hn
    unfold SurjOn
    rw [hn, subset_def]
    intro x hx
    exact absurd hx (Nat.not_lt_zero x)

end Set