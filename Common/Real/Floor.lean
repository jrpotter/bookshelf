import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.LibrarySearch

/-! # Common.Real.Floor

A collection of useful definitions and theorems around the floor function.
-/

namespace Real.Floor

/--
The fractional portion of any real number is always in `[0, 1)`.
-/
theorem fract_mem_Ico_zero_one (x : ℝ)
  : Int.fract x ∈ Set.Ico 0 1 :=
  ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩

/-! ## Hermite's Identity

Definitions and theorems in support of proving Hermite's identity.
-/

namespace Hermite

/--
A partition of `[0, 1)` that looks as follows:

```
[0, 1/n), [1/n, 2/n), ..., [(n-1)/n, 1)
```

This is expected to be used as an indexing function of a union of sets, e.g.
`⋃ i ∈ Finset.range n, partition n i`.
-/
def partition (n : ℕ) (i : ℕ) : Set ℝ := Set.Ico (↑i / n) ((↑i + 1) / n)

/--
The fractional portion of any real number always exists in some member of the
indexed family of sets formed by any `partition`.
-/
theorem fract_mem_partition (r : ℝ) (hr : r ∈ Set.Ico 0 1)
  : ∀ n : ℕ, ∃ j : ℕ,
      j < n ∧ r ∈ Set.Ico (((j : ℕ) : ℝ) / n) ((↑j + 1) / n) := by
  sorry

/--
The indexed union of the family of sets of a `partition` is a subset of `[0, 1)`.
-/
theorem partition_subset_Ico_zero_one
  : (⋃ i ∈ Finset.range n, partition n i) ⊆ Set.Ico 0 1 := by
  simp only [
    Finset.mem_range,
    gt_iff_lt,
    zero_lt_one,
    not_true,
    ge_iff_le,
    Set.unionᵢ_subset_iff
  ]
  intro i hi x hx
  have hn : (0 : ℝ) < n := calc (0 : ℝ)
    _ ≤ i := Nat.cast_nonneg i
    _ < n := Nat.cast_lt.mpr hi
  apply And.intro
  · have h_zero_le_i_div_n : (0 : ℝ) ≤ i / n := by
      rw [← mul_le_mul_right hn, zero_mul, div_mul, div_self, div_one]
      · exact Nat.cast_nonneg i
      · exact ne_iff_lt_or_gt.mpr (Or.inr hn)
    calc (0 : ℝ)
      _ ≤ i / n := h_zero_le_i_div_n
      _ ≤ x := hx.left
  · have h_succ_div_n_le_one : (i + 1) / n ≤ (1 : ℝ) := by
      rw [div_le_one_iff]
      refine Or.inl ?_
      exact ⟨hn, by norm_cast⟩
    calc x
      _ < (i + 1) / n := hx.right
      _ ≤ 1 := h_succ_div_n_le_one

/--
`[0, 1)` is a subset of the indexed union of the family of sets of a `partition`.
-/
theorem Ico_zero_one_subset_partition
  : Set.Ico 0 1 ⊆ (⋃ i ∈ Finset.range n, partition n i) := by
  intro x hx
  simp only [Finset.mem_range, Set.mem_unionᵢ, exists_prop]
  unfold partition
  exact fract_mem_partition x hx n

/--
The indexed union of the family of sets of a `partition` is equal to `[0, 1)`.
-/
theorem partition_eq_Ico_zero_one
  : (⋃ i ∈ Finset.range n, partition n i) = Set.Ico 0 1 :=
  Set.Subset.antisymm_iff.mpr
    ⟨partition_subset_Ico_zero_one, Ico_zero_one_subset_partition⟩

end Hermite

open BigOperators

/-- ### Hermite's Identity

The following decomposes the floor of a multiplication into a sum of floors.
-/
theorem floor_mul_eq_sum_range_floor_add_index_div (n : ℕ) (x : ℝ)
  : ⌊n * x⌋ = ∑ i in Finset.range n, ⌊x + i / n⌋ := by
  let r := Int.fract x

  -- Here we see there exists some `j` such that `r ∈ [j / n, (j + 1) / n]`.
  have hx : x = ⌊x⌋ + r := Eq.symm (add_eq_of_eq_sub' rfl)
  have ⟨j, ⟨hj, hr⟩⟩ :=
    Hermite.fract_mem_partition r (fract_mem_Ico_zero_one x) n

  -- With the above definitions established, we now show the left- and
  -- right-hand sides of the goal evaluate to the same number.

  have hlhs : ⌊n * x⌋ = n * ⌊x⌋ + j := by
    have hn : (0 : ℝ) < n := calc (0 : ℝ)
      _ ≤ j := Nat.cast_nonneg j
      _ < n := Nat.cast_lt.mpr hj
    -- We prove that `nr ∈ [j, j + 1)`. It must then follow `⌊nr⌋ = j`.
    have hnr : n * r ∈ Set.Ico ((j : ℕ) : ℝ) (j + 1) := by
      apply And.intro
      · have := hr.left
        rw [← mul_le_mul_right hn, div_mul, div_self, div_one] at this
        · rwa [mul_comm]
        · exact ne_of_gt hn
      · have := hr.right
        rw [← mul_lt_mul_right hn, div_mul, div_self, div_one] at this
        · rwa [mul_comm]
        · exact ne_of_gt hn
    have hnr_eq_j : ⌊n * r⌋ = j := by
      have := Int.floor_eq_on_Ico' j (n * r) hnr
      norm_cast at this
    conv =>
      lhs
      rw [hx, mul_add, add_comm]
      norm_cast
      rw [Int.floor_add_int, hnr_eq_j, add_comm]

  have hrhs : ∑ i in Finset.range n, ⌊x + i / n⌋ = n * ⌊x⌋ + j := by
    sorry

  -- Close out goal by showing left- and right-hand side equal a common value.
  rw [hlhs, hrhs]

end Real.Floor