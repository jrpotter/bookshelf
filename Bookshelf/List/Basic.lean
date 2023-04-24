import Mathlib.Logic.Basic

namespace List

/--
The length of any empty list is definitionally zero.
-/
theorem nil_length_eq_zero : @length α [] = 0 := rfl

/--
If the length of a list is greater than zero, it cannot be `List.nil`.
-/
theorem length_gt_zero_imp_not_nil : xs.length > 0 → xs ≠ [] := by
  intro h
  by_contra nh
  rw [nh] at h
  have : 0 > 0 := calc 0
    _ = length [] := by rw [←nil_length_eq_zero]
    _ > 0 := h
  simp at this

/--
Given a list `xs` of length `k`, produces a list of length `k - 1` where the
`i`th member of the resulting list is `f xs[i] xs[i + 1]`.
-/
def pairwise (xs : List α) (f : α → α → β) : List β :=
  match xs.tail? with
  | none => []
  | some ys => zipWith f xs ys

/--
If `x` is a member of the pairwise'd list, there must exist two (adjacent)
elements of the list, say `x₁` and `x₂`, such that `x = f x₁ x₂`.
-/
theorem mem_pairwise_imp_exists {xs : List α} (h : x ∈ xs.pairwise f)
  : ∃ x₁ x₂, x₁ ∈ xs ∧ x₂ ∈ xs ∧ x = f x₁ x₂ := by
  unfold pairwise at h
  cases h' : tail? xs with
  | none => rw [h'] at h; cases h
  | some ys =>
    rw [h'] at h
    simp only at h
    sorry

end List