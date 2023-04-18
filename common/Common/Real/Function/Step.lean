import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.NormNum

import Common.Real.Basic
import Common.Real.Set.Partition

namespace Real.Function

/--
Any member of a subinterval of a partition `P` must also be a member of `P`.
-/
lemma mem_open_subinterval_imp_mem_partition {p : Partition}
  (hI : I ∈ p.xs.pairwise (fun x₁ x₂ => i(x₁, x₂)))
  (hy : y ∈ I) : y ∈ p := by
  unfold List.pairwise at hI
  have ⟨ys, hys⟩ : ∃ ys, List.tail? p.xs = some ys := sorry
  conv at hI => arg 2; rw [hys]; simp only
  sorry

/--
A `Step` function is a function `f` along with a proof of the existence of some
partition `P` such that `f` is constant on every open subinterval of `P`.
-/
structure Step where
  p : Partition
  f : ∀ x ∈ p, ℝ
  const_open_subintervals :
    ∀ (hI : I ∈ p.xs.pairwise (fun x₁ x₂ => i(x₁, x₂))),
      ∃ c : ℝ, ∀ (hy : y ∈ I),
        f y (mem_open_subinterval_imp_mem_partition hI hy) = c

namespace Step

def set_def (f : Step) : Set ℝ² := sorry

-- TODO: Fill out

end Real.Function.Step