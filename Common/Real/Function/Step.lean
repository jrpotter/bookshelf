import Common.Real.Basic
import Common.Real.Set.Partition

/-! # Common.Real.Function.Step

A characterization of step functions.
-/

namespace Real.Function

open Partition

/--
Any member of a subinterval of a partition `P` must also be a member of `P`.
-/
lemma mem_open_subinterval_imp_mem_partition {p : Partition}
  (hI : I ∈ p.xs.pairwise (fun x₁ x₂ => Set.Ioo x₁ x₂))
  (hy : y ∈ I) : y ∈ p := by
  cases h : p.xs with
  | nil =>
    -- By definition, a partition must always have at least two points in the
    -- interval. Discharge the empty case.
    rw [h] at hI
    cases hI
  | cons x ys =>
    have ⟨i, x₁, ⟨x₂, ⟨hx₁, ⟨hx₂, hI'⟩⟩⟩⟩ :=
      List.mem_pairwise_imp_exists_adjacent hI
    have hx₁ : x₁ ∈ p.xs := by
      rw [hx₁]
      let j : Fin (List.length p.xs) := ⟨i.1, Nat.lt_of_lt_pred i.2⟩
      exact List.mem_iff_exists_get.mpr ⟨j, rfl⟩
    have hx₂ : x₂ ∈ p.xs := by
      rw [hx₂]
      let j : Fin (List.length p.xs) := ⟨i.1 + 1, lt_tsub_iff_right.mp i.2⟩
      exact List.mem_iff_exists_get.mpr ⟨j, rfl⟩
    rw [hI'] at hy
    apply And.intro
    · calc p.left
        _ ≤ x₁ := (subdivision_point_mem_partition hx₁).left
        _ ≤ y := le_of_lt hy.left
    · calc y
        _ ≤ x₂ := le_of_lt hy.right
        _ ≤ p.right := (subdivision_point_mem_partition hx₂).right

/--
A function `f` is a `Step` function if there exists a `Partition` `p` such that
`f` is constant on every open subinterval of `p`.
-/
structure Step where
  p : Partition
  f : ∀ x ∈ p, ℝ
  const_open_subintervals :
    ∀ (hI : I ∈ p.xs.pairwise (fun x₁ x₂ => Set.Ioo x₁ x₂)),
      ∃ c : ℝ, ∀ (hy : y ∈ I),
        f y (mem_open_subinterval_imp_mem_partition hI hy) = c

namespace Step

/--
The set definition of a `Step` function is the region between the constant
values of the function's subintervals and the real axis.
-/
def set_def (f : Step) : Set ℝ² := sorry

end Step

end Real.Function