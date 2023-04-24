import Bookshelf.Real.Basic
import OneVariableCalculus.Real.Set.Partition

namespace Real.Function

open Partition

/--
Any member of a subinterval of a partition `P` must also be a member of `P`.
-/
lemma mem_open_subinterval_imp_mem_partition {p : Partition}
  (hI : I ∈ p.xs.pairwise (fun x₁ x₂ => i(x₁, x₂)))
  (hy : y ∈ I) : y ∈ p := by
  -- By definition, a partition must always have at least two points in the
  -- interval. We can disregard the empty case.
  cases h : p.xs with
  | nil => rw [h] at hI; cases hI
  | cons x ys =>
    have ⟨x₁, ⟨x₂, ⟨hx₁, ⟨hx₂, hI'⟩⟩⟩⟩ := List.mem_pairwise_imp_exists hI
    rw [hI'] at hy
    refine ⟨?_, ?_⟩
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
    ∀ (hI : I ∈ p.xs.pairwise (fun x₁ x₂ => i(x₁, x₂))),
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