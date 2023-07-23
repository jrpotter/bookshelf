import Common.Logic.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Prod

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

/-! ## Pair Sets -/

/--
If `{x, y} = {x}` then `x = y`.
-/
theorem pair_eq_singleton_mem_imp_eq_self {x y : α}
  (h : {x, y} = ({x} : Set α)) : y = x := by
  rw [Set.ext_iff] at h
  have := h y
  simp at this
  exact this

/--
If `{x, y} = {z}` then `x = y = z`.
-/
theorem pair_eq_singleton_mem_imp_eq_all {x y z : α}
  (h : {x, y} = ({z} : Set α)) : x = z ∧ y = z := by
  have h' := h
  rw [Set.ext_iff] at h'
  have hz := h' z
  simp at hz
  apply Or.elim hz
  · intro hzx
    rw [← hzx] at h
    have := pair_eq_singleton_mem_imp_eq_self h
    exact ⟨hzx.symm, this⟩
  · intro hzy
    rw [← hzy, Set.pair_comm] at h
    have := pair_eq_singleton_mem_imp_eq_self h
    exact ⟨this, hzy.symm⟩

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

/-! ## Powerset -/

/--
Every `Set` is a member of its own powerset.
-/
theorem self_mem_powerset_self {A : Set α}
  : A ∈ 𝒫 A := subset_self A

/-! ## Cartesian Product -/

/--
For any `Set` `A`, `∅ × A = ∅`.
-/
theorem prod_left_emptyset_eq_emptyset {A : Set α}
  : Set.prod (∅ : Set β) A = ∅ := by
  unfold prod
  simp only [mem_empty_iff_false, false_and, setOf_false]

/--
For any `Set` `A`, `A × ∅ = ∅`.
-/
theorem prod_right_emptyset_eq_emptyset {A : Set α}
  : Set.prod A (∅ : Set β) = ∅ := by
  unfold prod
  simp only [mem_empty_iff_false, and_false, setOf_false]

/--
For any `Set`s `A` and `B`, if both `A` and `B` are nonempty, then `A × B` is
also nonempty.
-/
theorem prod_nonempty_nonempty_imp_nonempty_prod {A : Set α} {B : Set β}
  : A ≠ ∅ ∧ B ≠ ∅ ↔ Set.prod A B ≠ ∅ := by
  apply Iff.intro
  · intro nAB h
    have ⟨a, ha⟩ := nonempty_iff_ne_empty.mpr nAB.left
    have ⟨b, hb⟩ := nonempty_iff_ne_empty.mpr nAB.right
    rw [Set.ext_iff] at h
    exact (h (a, b)).mp ⟨ha, hb⟩
  · intro h
    rw [← nonempty_iff_ne_empty] at h
    have ⟨(a, b), ⟨ha, hb⟩⟩ := h
    rw [← nonempty_iff_ne_empty, ← nonempty_iff_ne_empty]
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩⟩

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
  show ¬(x ∈ A ∧ ¬x ∈ B ∨ x ∈ B ∧ ¬x ∈ A) ↔ x ∈ A ∧ x ∈ B ∨ ¬(x ∈ A ∨ x ∈ B)
  rw [
    not_or_de_morgan,
    not_and_de_morgan, not_and_de_morgan,
    not_not, not_not,
    not_or_de_morgan
  ]
  apply Iff.intro
  · intro nx
    apply Or.elim nx.left
    · intro nA
      exact Or.elim nx.right (Or.inr ⟨nA, ·⟩) (absurd · nA)
    · intro hB
      exact Or.elim nx.right (absurd hB ·) (Or.inl ⟨·, hB⟩)
  · intro hx
    apply Or.elim hx
    · intro hy
      exact ⟨Or.inr hy.right, Or.inr hy.left⟩
    · intro hy
      exact ⟨Or.inl hy.left, Or.inl hy.right⟩

end Set