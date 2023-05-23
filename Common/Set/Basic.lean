import Mathlib.Data.Set.Basic

import Common.Logic.Basic

/-! # Common.Set.Basic

Additional theorems and definitions useful in the context of `Set`s.
-/

namespace Set

/-! ## Minkowski Sum -/

/-
The Minkowski sum of two `Set`s `s` and `t` is the set
`s + t = { a + b : a ∈ s, b ∈ t }`.
-/
def minkowskiSum {α : Type u} [Add α] (s t : Set α) :=
  { x | ∃ a ∈ s, ∃ b ∈ t, x = a + b }

/--
The sum of two `Set`s is nonempty **iff** the summands are nonempty.
-/
theorem nonempty_minkowski_sum_iff_nonempty_add_nonempty {α : Type u} [Add α]
  {s t : Set α}
  : (minkowskiSum s t).Nonempty ↔ s.Nonempty ∧ t.Nonempty := by
  apply Iff.intro
  · intro h
    have ⟨x, hx⟩ := h
    have ⟨a, ⟨ha, ⟨b, ⟨hb, _⟩⟩⟩⟩ := hx
    apply And.intro
    · exact ⟨a, ha⟩
    · exact ⟨b, hb⟩
  · intro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨a + b, ⟨a, ⟨ha, ⟨b, ⟨hb, rfl⟩⟩⟩⟩⟩

/-! ## Characteristic Function -/

/--
The characteristic function of a `Set` `S`.

It returns `1` if the specified input belongs to `S` and `0` otherwise.
-/
def characteristic (S : Set α) (x : α) [Decidable (x ∈ S)] : Nat :=
  if x ∈ S then 1 else 0

/-! ## Subsets -/

/--
Every `Set` is a subset of itself.
-/
theorem subset_self (S : Set α) : S ⊆ S := by
  intro _ hs
  exact hs

/--
If `Set` `A` is a subset of `Set` `B`, then `A ∪ B = B`.
-/
theorem left_subset_union_eq_self {A B : Set α} (h : A ⊆ B)
  : A ∪ B = B := by
  rw [Set.ext_iff]
  intro x
  apply Iff.intro
  · intro hU
    apply Or.elim hU
    · intro hA
      exact h hA
    · simp
  · intro hB
    exact Or.inr hB

/--
If `Set` `B` is a subset of `Set` `A`, then `A ∪ B = B`.
-/
theorem right_subset_union_eq_self {A B : Set α} (h : B ⊆ A)
  : A ∪ B = A := by
  rw [Set.union_comm]
  exact left_subset_union_eq_self h

/--
If `x` and `y` are members of `Set` `A`, it follows `{x, y}` is a subset of `A`.
-/
theorem mem_mem_imp_pair_subset {x y : α}
  (hx : x ∈ A) (hy : y ∈ A) : ({x, y} : Set α) ⊆ A := by
  intro a ha
  apply Or.elim ha
  · intro hx'
    rwa [hx']
  · intro hy'
    rwa [hy']

/-! ## Symmetric Difference -/

/--
`x` is a member of the `symmDiff` of `A` and `B` **iff** `x ∈ A ∧ x ∉ B` or
`x ∉ A ∧ x ∈ B`.
-/
theorem mem_symm_diff_iff_exclusive_mem {A B : Set α}
  : x ∈ (A ∆ B) ↔ (x ∈ A ∧ x ∉ B) ∨ (x ∉ A ∧ x ∈ B) := by
  unfold symmDiff
  apply Iff.intro
  · intro hx
    simp at hx
    conv => arg 2; rw [and_comm]
    exact hx
  · intro hx
    simp
    conv => arg 2; rw [and_comm]
    exact hx

/--
`x` is not a member of the `symmDiff` of `A` and `B` **iff** `x ∈ A ∩ B` or
`x ∉ A ∪ B`.

This is the contraposition of `mem_symm_diff_iff_exclusive_mem`.
-/
theorem not_mem_symm_diff_inter_or_not_union {A B : Set α}
  : x ∉ (A ∆ B) ↔ (x ∈ A ∩ B) ∨ (x ∉ A ∪ B) := by
  unfold symmDiff
  simp
  rw [
    not_or_de_morgan,
    not_and_de_morgan, not_and_de_morgan,
    not_not, not_not,
    not_or_de_morgan
  ]
  apply Iff.intro
  · intro hx
    apply Or.elim hx.left
    · intro nA
      exact Or.elim hx.right
        (fun nB => Or.inr ⟨nA, nB⟩)
        (fun hA => absurd hA nA)
    · intro hB
      apply Or.elim hx.right
        (fun nB => absurd hB nB)
        (fun hA => Or.inl ⟨hA, hB⟩)
  · intro hx
    apply Or.elim hx
    · intro hy
      exact ⟨Or.inr hy.right, Or.inr hy.left⟩
    · intro hy
      exact ⟨Or.inl hy.left, Or.inl hy.right⟩

end Set