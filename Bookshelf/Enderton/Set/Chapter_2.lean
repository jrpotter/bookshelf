import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice

import Bookshelf.Enderton.Set.Chapter_1
import Common.Set.Basic

/-! # Enderton.Chapter_2

Axioms and Operations
-/

namespace Enderton.Set.Chapter_2


/-- ### Exercise 3.1

Assume that `A` is the set of integers divisible by `4`. Similarly assume that
`B` and `C` are the sets of integers divisible by `9` and `10`, respectively.
What is in `A ∩ B ∩ C`?
-/
theorem exercise_3_1 {A B C : Set ℤ}
  (hA : A = { x | Dvd.dvd 4 x })
  (hB : B = { x | Dvd.dvd 9 x })
  (hC : C = { x | Dvd.dvd 10 x })
  : ∀ x ∈ (A ∩ B ∩ C), (4 ∣ x) ∧ (9 ∣ x) ∧ (10 ∣ x) := by
  intro x h
  rw [Set.mem_inter_iff] at h
  have ⟨⟨ha, hb⟩, hc⟩ := h
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · rw [hA] at ha
    exact Set.mem_setOf.mp ha
  · rw [hB] at hb
    exact Set.mem_setOf.mp hb
  · rw [hC] at hc
    exact Set.mem_setOf.mp hc

/-- ### Exercise 3.2

Give an example of sets `A` and `B` for which `⋃ A = ⋃ B` but `A ≠ B`.
-/
theorem exercise_3_2 {A B : Set (Set ℕ)}
  (hA : A = {{1}, {2}}) (hB : B = {{1, 2}})
  : Set.sUnion A = Set.sUnion B ∧ A ≠ B := by
  apply And.intro
  · show ⋃₀ A = ⋃₀ B
    ext x
    show (∃ t, t ∈ A ∧ x ∈ t) ↔ ∃ t, t ∈ B ∧ x ∈ t
    apply Iff.intro
    · intro ⟨t, ⟨ht, hx⟩⟩
      rw [hA] at ht
      refine ⟨{1, 2}, ⟨by rw [hB]; simp, ?_⟩⟩
      apply Or.elim ht <;>
      · intro ht'
        rw [ht'] at hx
        rw [hx]
        simp
    · intro ⟨t, ⟨ht, hx⟩⟩
      rw [hB] at ht
      rw [ht] at hx
      apply Or.elim hx
      · intro hx'
        exact ⟨{1}, ⟨by rw [hA]; simp, by rw [hx']; simp⟩⟩
      · intro hx'
        exact ⟨{2}, ⟨by rw [hA]; simp, by rw [hx']; simp⟩⟩
  · show A ≠ B
    -- Find an element that exists in `B` but not in `A`. Extensionality
    -- concludes the proof.
    intro h
    rw [hA, hB, Set.ext_iff] at h
    have h₁ := h {1, 2}
    simp at h₁
    rw [Set.ext_iff] at h₁
    have h₂ := h₁ 2
    simp at h₂

/-- ### Exercise 3.3

Show that every member of a set `A` is a subset of `U A`. (This was stated as an
example in this section.)
-/
theorem exercise_3_3 {A : Set (Set α)}
  : ∀ x ∈ A, x ⊆ Set.sUnion A := by
  intro x hx
  show ∀ y ∈ x, y ∈ { a | ∃ t, t ∈ A ∧ a ∈ t }
  intro y hy
  rw [Set.mem_setOf_eq]
  exact ⟨x, ⟨hx, hy⟩⟩

/-- ### Exercise 3.4

Show that if `A ⊆ B`, then `⋃ A ⊆ ⋃ B`.
-/
theorem exercise_3_4 (h : A ⊆ B) : ⋃₀ A ⊆ ⋃₀ B := by
  show ∀ x ∈ { a | ∃ t, t ∈ A ∧ a ∈ t }, x ∈ { a | ∃ t, t ∈ B ∧ a ∈ t }
  intro x hx
  rw [Set.mem_setOf_eq] at hx
  have ⟨t, ⟨ht, hxt⟩⟩ := hx
  rw [Set.mem_setOf_eq]
  exact ⟨t, ⟨h ht, hxt⟩⟩

/-- ### Exercise 3.5

Assume that every member of `𝓐` is a subset of `B`. Show that `⋃ 𝓐 ⊆ B`.
-/
theorem exercise_3_5 (h : ∀ x ∈ 𝓐, x ⊆ B) : ⋃₀ 𝓐 ⊆ B := by
  unfold Set.sUnion sSup Set.instSupSetSet
  simp only
  show ∀ y ∈ { a | ∃ t, t ∈ 𝓐 ∧ a ∈ t }, y ∈ B
  intro y hy
  rw [Set.mem_setOf_eq] at hy
  have ⟨t, ⟨ht𝓐, hyt⟩⟩ := hy
  exact (h t ht𝓐) hyt

/-- ### Exercise 3.6a

Show that for any set `A`, `⋃ 𝓟 A = A`.
-/
theorem exercise_3_6a : ⋃₀ (Set.powerset A) = A := by
  unfold Set.sUnion sSup Set.instSupSetSet Set.powerset
  simp only
  ext x
  apply Iff.intro
  · intro hx
    rw [Set.mem_setOf_eq] at hx
    have ⟨t, ⟨htl, htr⟩⟩ := hx
    rw [Set.mem_setOf_eq] at htl
    exact htl htr
  · intro hx
    rw [Set.mem_setOf_eq]
    exact ⟨A, ⟨by rw [Set.mem_setOf_eq], hx⟩⟩

/-- ### Exercise 3.6b

Show that `A ⊆ 𝓟 ⋃ A`. Under what conditions does equality hold?
-/
theorem exercise_3_6b
  : A ⊆ Set.powerset (⋃₀ A)
  ∧ (A = Set.powerset (⋃₀ A) ↔ ∃ B, A = Set.powerset B) := by
  apply And.intro
  · unfold Set.powerset
    show ∀ x ∈ A, x ∈ { t | t ⊆ ⋃₀ A }
    intro x hx
    rw [Set.mem_setOf]
    exact exercise_3_3 x hx
  · apply Iff.intro
    · intro hA
      exact ⟨⋃₀ A, hA⟩
    · intro ⟨B, hB⟩
      conv => rhs; rw [hB, exercise_3_6a]
      exact hB

/-- ### Exercise 3.7a

Show that for any sets `A` and `B`, `𝓟 A ∩ 𝓟 B = 𝓟 (A ∩ B)`.
-/
theorem exercise_3_7A
  : Set.powerset A ∩ Set.powerset B = Set.powerset (A ∩ B) := by
  suffices
    Set.powerset A ∩ Set.powerset B ⊆ Set.powerset (A ∩ B) ∧
    Set.powerset (A ∩ B) ⊆ Set.powerset A ∩ Set.powerset B from
    subset_antisymm this.left this.right
  apply And.intro
  · unfold Set.powerset
    intro x hx
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hx
    rwa [Set.mem_setOf, Set.subset_inter_iff]
  · unfold Set.powerset
    simp
    intro x hA _
    exact hA

-- theorem false_of_false_iff_true : (false ↔ true) → false := by simp

/-- ### Exercise 3.7b (i)

Show that `𝓟 A ∪ 𝓟 B ⊆ 𝓟 (A ∪ B)`.
-/
theorem exercise_3_7b_i
  : Set.powerset A ∪ Set.powerset B ⊆ Set.powerset (A ∪ B) := by
  unfold Set.powerset
  intro x hx
  simp at hx
  apply Or.elim hx
  · intro hA
    rw [Set.mem_setOf_eq]
    exact Set.subset_union_of_subset_left hA B
  · intro hB
    rw [Set.mem_setOf_eq]
    exact Set.subset_union_of_subset_right hB A

/-- ### Exercise 3.7b (ii)

Under what conditions does `𝓟 A ∪ 𝓟 B = 𝓟 (A ∪ B)`.?
-/
theorem exercise_3_7b_ii
  : Set.powerset A ∪ Set.powerset B = Set.powerset (A ∪ B) ↔ A ⊆ B ∨ B ⊆ A := by
  unfold Set.powerset
  apply Iff.intro
  · intro h
    by_contra nh
    rw [not_or] at nh
    have ⟨a, hA⟩ := Set.not_subset.mp nh.left
    have ⟨b, hB⟩ := Set.not_subset.mp nh.right
    rw [Set.ext_iff] at h
    have hz := h {a, b}
    -- `hz` states that `{a, b} ⊆ A ∨ {a, b} ⊆ B ↔ {a, b} ⊆ A ∪ B`. We show the
    -- left-hand side is false but the right-hand side is true, yielding our
    -- contradiction.
    suffices ¬({a, b} ⊆ A ∨ {a, b} ⊆ B) by
      have hz₁ : a ∈ A ∪ B := by
        rw [Set.mem_union]
        exact Or.inl hA.left
      have hz₂ : b ∈ A ∪ B := by
        rw [Set.mem_union]
        exact Or.inr hB.left
      exact absurd (hz.mpr $ Set.mem_mem_imp_pair_subset hz₁ hz₂) this
    intro hAB
    exact Or.elim hAB
      (fun y => absurd (y $ show b ∈ {a, b} by simp) hB.right)
      (fun y => absurd (y $ show a ∈ {a, b} by simp) hA.right)
  · intro h
    ext x
    apply Or.elim h
    · intro hA
      apply Iff.intro
      · intro hx
        exact Or.elim hx
          (Set.subset_union_of_subset_left · B)
          (Set.subset_union_of_subset_right · A)
      · intro hx
        refine Or.inr (Set.Subset.trans hx ?_)
        exact subset_of_eq (Set.left_subset_union_eq_self hA)
    · intro hB
      apply Iff.intro
      · intro hx
        exact Or.elim hx
          (Set.subset_union_of_subset_left · B)
          (Set.subset_union_of_subset_right · A)
      · intro hx
        refine Or.inl (Set.Subset.trans hx ?_)
        exact subset_of_eq (Set.right_subset_union_eq_self hB)

/-- ### Exercise 3.9

Give an example of sets `a` and `B` for which `a ∈ B` but `𝓟 a ∉ 𝓟 B`.
-/
theorem exercise_3_9 (ha : a = {1}) (hB : B = {{1}})
  : a ∈ B ∧ Set.powerset a ∉ Set.powerset B := by
  apply And.intro
  · rw [ha, hB]
    simp
  · intro h
    have h₁ : Set.powerset a = {∅, {1}} := by
      rw [ha]
      exact Set.powerset_singleton 1
    have h₂ : Set.powerset B = {∅, {{1}}} := by
      rw [hB]
      exact Set.powerset_singleton {1}
    rw [h₁, h₂] at h
    simp at h
    apply Or.elim h
    · intro h
      rw [Set.ext_iff] at h
      have := h ∅
      simp at this
    · intro h
      rw [Set.ext_iff] at h
      have := h 1
      simp at this

/-- ### Exercise 3.10

Show that if `a ∈ B`, then `𝓟 a ∈ 𝓟 𝓟 ⋃ B`.
-/
theorem exercise_3_10 (ha : a ∈ B)
  : Set.powerset a ∈ Set.powerset (Set.powerset (⋃₀ B)) := by
  have h₁ := exercise_3_3 a ha
  have h₂ := Chapter_1.exercise_1_3 h₁
  generalize hb : 𝒫 (⋃₀ B) = b
  conv => rhs; unfold Set.powerset
  rw [← hb, Set.mem_setOf_eq]
  exact h₂

end Enderton.Set.Chapter_2