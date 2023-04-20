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

end List