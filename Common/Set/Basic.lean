import Common.Logic.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Prod
import Mathlib.Tactic.LibrarySearch

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
There exists no proper subset of `∅`.
-/
theorem ssubset_empty_iff_false (S : Set α)
  : S ⊂ ∅ ↔ False := by
  apply Iff.intro
  · intro h
    rw [ssubset_iff_subset_ne, subset_empty_iff] at h
    exact absurd h.left h.right
  · simp only [IsEmpty.forall_iff]

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
  : A ∈ 𝒫 A := fun _ => mem_preimage.mp

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

/-! ## Difference -/

/--
For any sets `A ⊂ B`, if `x ∈ A` then `A - {x} ⊂ B - {x}`.
-/
theorem diff_ssubset_diff_left {A B : Set α} (h : A ⊂ B)
  : x ∈ A → A \ {x} ⊂ B \ {x} := by
  intro hx
  rw [Set.ssubset_def]
  apply And.intro
  · exact diff_subset_diff_left (subset_of_ssubset h)
  · by_contra nh
    have : {x} ⊆ A := singleton_subset_iff.mpr hx
    rw [diff_subset_iff, union_diff_cancel this] at nh
    exact LT.lt.false (Set.ssubset_of_ssubset_of_subset h nh)

/--
For any sets `A ⊂ B`, `B \ A` is nonempty.
-/
theorem diff_ssubset_nonempty {A B : Set α} (h : A ⊂ B)
  : Set.Nonempty (B \ A) := by
  have : B = A ∪ (B \ A) := by
    simp only [Set.union_diff_self]
    exact (Set.left_subset_union_eq_self (subset_of_ssubset h)).symm
  rw [this, Set.ssubset_def] at h
  have : ¬ ∀ x, x ∈ A ∪ (B \ A) → x ∈ A := h.right
  simp only [Set.mem_union, not_forall, exists_prop] at this
  have ⟨x, hx⟩ := this
  apply Or.elim hx.left
  · intro nx
    exact absurd nx hx.right
  · intro hx
    exact ⟨x, hx⟩

/--
If an element `x` is not a member of a set `A`, then `A - {x} = A`. 
-/
theorem not_mem_diff_eq_self {A : Set α} (h : a ∉ A)
  : A \ {a} = A := by
  ext x
  apply Iff.intro
  · exact And.left
  · intro hx
    refine ⟨hx, ?_⟩
    simp only [mem_singleton_iff]
    by_contra nx
    rw [nx] at hx
    exact absurd hx h

/--
Given two sets `A` and `B`, `(A - {a}) - (B - {b}) = (A - B) - {a}`.
-/
theorem diff_mem_diff_mem_eq_diff_diff_mem {A B : Set α} {a : α}
  : (A \ {a}) \ (B \ {a}) = (A \ B) \ {a} := by
  calc (A \ {a}) \ (B \ {a})
    _ = { x | x ∈ A \ {a} ∧ x ∉ B \ {a} } := rfl
    _ = { x | x ∈ A \ {a} ∧ ¬(x ∈ B \ {a}) } := rfl
    _ = { x | (x ∈ A ∧ x ≠ a) ∧ ¬(x ∈ B ∧ x ≠ a) } := rfl
    _ = { x | (x ∈ A ∧ x ≠ a) ∧ (x ∉ B ∨ x = a) } := by
      ext x
      rw [mem_setOf_eq, not_and_de_morgan]
      simp
    _ = { x | (x ∈ A ∧ x ≠ a ∧ x ∉ B) ∨ (x ∈ A ∧ x ≠ a ∧ x = a) } := by
      ext x
      simp only [mem_setOf_eq]
      rw [and_or_left, and_assoc, and_assoc]
    _ = { x | x ∈ A ∧ x ≠ a ∧ x ∉ B } := by simp
    _ = { x | x ∈ A ∧ x ∉ B ∧ x ≠ a } := by
      ext x
      simp only [ne_eq, sep_and, mem_inter_iff, mem_setOf_eq]
      apply Iff.intro <;>
      · intro ⟨⟨_, hx₂⟩, hx₃, hx₄⟩
        exact ⟨⟨hx₃, hx₄⟩, ⟨hx₃, hx₂⟩⟩
    _ = { x | x ∈ A ∧ x ∉ B ∧ x ∉ ({a} : Set α) } := rfl
    _ = { x | x ∈ A \ B ∧ x ∉ ({a} : Set α) } := by
      ext x
      simp only [
        mem_singleton_iff,
        sep_and,
        mem_inter_iff,
        mem_setOf_eq,
        mem_diff,
        and_congr_right_iff,
        and_iff_right_iff_imp,
        and_imp
      ]
      intro hx _ _
      exact hx
    _ = (A \ B) \ {a} := rfl

/--
For any set `A`, the difference between the sample space and `A` is the
complement of `A`.
-/
theorem univ_diff_self_eq_compl (A : Set α) : Set.univ \ A = A.compl := by
  unfold Set.compl SDiff.sdiff instSDiffSet Set.diff
  simp only [mem_univ, true_and]

/--
For any set `A`, the difference between the sample space and the complement of
`A` is `A`.
-/
theorem univ_diff_compl_eq_self (A : Set α) : Set.univ \ A.compl = A := by
  unfold Set.compl SDiff.sdiff instSDiffSet Set.diff
  simp only [mem_univ, mem_setOf_eq, not_not, true_and, setOf_mem_eq]

/-! ## Symmetric Difference -/

/--
If `x ∈ A` and `x ∉ B`, then `x ∈ A ∆ B`.
-/
theorem symm_diff_mem_left {A B : Set α} (hA : x ∈ A) (hB : x ∉ B)
  : x ∈ A ∆ B := by
  left
  exact ⟨hA, hB⟩

/--
If `x ∉ A` and `x ∈ B`, then `x ∈ A ∆ B`.
-/
theorem symm_diff_mem_right {A B : Set α} (hA : x ∉ A) (hB : x ∈ B)
  : x ∈ A ∆ B := by
  right
  exact ⟨hB, hA⟩

/--
If `x ∈ A` and `x ∈ B`, then `x ∉ A ∆ B`.
-/
theorem symm_diff_mem_both_not_mem {A B : Set α} (hA : x ∈ A) (hB : x ∈ B)
  : x ∉ A ∆ B := by
  intro h
  apply Or.elim h
  · intro ⟨_, nB⟩
    exact absurd hB nB
  · intro ⟨_, nA⟩
    exact absurd hA nA

/--
If `x ∉ A` and `x ∉ B`, then `x ∉ A ∆ B`.
-/
theorem symm_diff_not_mem_both_not_mem {A B : Set α} (nA : x ∉ A) (nB : x ∉ B)
  : x ∉ A ∆ B := by
  intro h
  apply Or.elim h
  · intro ⟨hA, _⟩
    exact absurd hA nA
  · intro ⟨hB, _⟩
    exact absurd hB nB

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