import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice

import Bookshelf.Enderton.Set.Chapter_1
import Common.Logic.Basic
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
  : ∀ x ∈ A, x ⊆ ⋃₀ A := by
  intro x hx
  show ∀ y ∈ x, y ∈ { a | ∃ t, t ∈ A ∧ a ∈ t }
  intro y hy
  rw [Set.mem_setOf_eq]
  exact ⟨x, ⟨hx, hy⟩⟩

/-- ### Exercise 3.4

Show that if `A ⊆ B`, then `⋃ A ⊆ ⋃ B`.
-/
theorem exercise_3_4 {A B : Set (Set α)} (h : A ⊆ B) : ⋃₀ A ⊆ ⋃₀ B := by
  show ∀ x ∈ { a | ∃ t, t ∈ A ∧ a ∈ t }, x ∈ { a | ∃ t, t ∈ B ∧ a ∈ t }
  intro x hx
  rw [Set.mem_setOf_eq] at hx
  have ⟨t, ⟨ht, hxt⟩⟩ := hx
  rw [Set.mem_setOf_eq]
  exact ⟨t, ⟨h ht, hxt⟩⟩

/-- ### Exercise 3.5

Assume that every member of `𝓐` is a subset of `B`. Show that `⋃ 𝓐 ⊆ B`.
-/
theorem exercise_3_5 {𝓐 : Set (Set α)} (h : ∀ x ∈ 𝓐, x ⊆ B)
  : ⋃₀ 𝓐 ⊆ B := by
  show ∀ y ∈ { a | ∃ t, t ∈ 𝓐 ∧ a ∈ t }, y ∈ B
  intro y hy
  rw [Set.mem_setOf_eq] at hy
  have ⟨t, ⟨ht𝓐, hyt⟩⟩ := hy
  exact (h t ht𝓐) hyt

/-- ### Exercise 3.6a

Show that for any set `A`, `⋃ 𝓟 A = A`.
-/
theorem exercise_3_6a : ⋃₀ (𝒫 A) = A := by
  show { a | ∃ t, t ∈ { t | t ⊆ A } ∧ a ∈ t } = A
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
  : A ⊆ 𝒫 (⋃₀ A)
  ∧ (A = 𝒫 (⋃₀ A) ↔ ∃ B, A = 𝒫 B) := by
  apply And.intro
  · show ∀ x ∈ A, x ∈ { t | t ⊆ ⋃₀ A }
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
  : 𝒫 A ∩ 𝒫 B = 𝒫 (A ∩ B) := by
  suffices 𝒫 A ∩ 𝒫 B ⊆ 𝒫 (A ∩ B) ∧ 𝒫 (A ∩ B) ⊆ 𝒫 A ∩ 𝒫 B from
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
  : 𝒫 A ∪ 𝒫 B ⊆ 𝒫 (A ∪ B) := by
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
  : 𝒫 A ∪ 𝒫 B = 𝒫 (A ∪ B) ↔ A ⊆ B ∨ B ⊆ A := by
  unfold Set.powerset
  apply Iff.intro
  · intro h
    by_contra nh
    rw [not_or_de_morgan] at nh
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
  : a ∈ B ∧ 𝒫 a ∉ 𝒫 B := by
  apply And.intro
  · rw [ha, hB]
    simp
  · intro h
    have h₁ : 𝒫 a = {∅, {1}} := by
      rw [ha]
      exact Set.powerset_singleton 1
    have h₂ : 𝒫 B = {∅, {{1}}} := by
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
theorem exercise_3_10 {B : Set (Set α)} (ha : a ∈ B)
  : 𝒫 a ∈ 𝒫 (𝒫 (⋃₀ B)) := by
  have h₁ := exercise_3_3 a ha
  have h₂ := Chapter_1.exercise_1_3 h₁
  generalize hb : 𝒫 (⋃₀ B) = b
  conv => rhs; unfold Set.powerset
  rw [← hb, Set.mem_setOf_eq]
  exact h₂

/-- ### Exercise 4.11 (i)

Show that for any sets `A` and `B`, `A = (A ∩ B) ∪ (A - B)`.
-/
theorem exercise_4_11_i {A B : Set α}
  : A = (A ∩ B) ∪ (A \ B) := by
  show A = fun a => A a ∧ B a ∨ A a ∧ ¬B a
  suffices ∀ x, (A x ∧ (B x ∨ ¬B x)) = A x by
    conv => rhs; ext x; rw [← and_or_left, this]
  intro x
  refine propext ?_
  apply Iff.intro
  · intro hx
    exact hx.left
  · intro hx
    exact ⟨hx, em (B x)⟩

/-- ### Exercise 4.11 (ii)

Show that for any sets `A` and `B`, `A ∪ (B - A) = A ∪ B`.
-/
theorem exercise_4_11_ii {A B : Set α}
  : A ∪ (B \ A) = A ∪ B := by
  show (fun a => A a ∨ B a ∧ ¬A a) = fun a => A a ∨ B a
  suffices ∀ x, ((A x ∨ B x) ∧ (A x ∨ ¬A x)) = (A x ∨ B x) by
    conv => lhs; ext x; rw [or_and_left, this x]
  intro x
  refine propext ?_
  apply Iff.intro
  · intro hx
    exact hx.left
  · intro hx
    exact ⟨hx, em (A x)⟩

section

variable {A B C : Set ℕ}

variable {hA : A = {1, 2, 3}}
variable {hB : B = {2, 3, 4}}
variable {hC : C = {3, 4, 5}}

lemma right_diff_eq_insert_one_three : A \ (B \ C) = {1, 3} := by
  rw [hA, hB, hC]
  ext x
  apply Iff.intro
  · intro hx
    unfold SDiff.sdiff Set.instSDiffSet Set.diff at hx
    unfold Membership.mem Set.instMembershipSet Set.Mem setOf at hx
    unfold insert Set.instInsertSet Set.insert setOf at hx
    have ⟨ha, hb⟩ := hx
    rw [not_and_de_morgan, not_or_de_morgan] at hb
    simp only [Set.mem_singleton_iff, not_not] at hb
    refine Or.elim ha Or.inl ?_
    intro hy
    apply Or.elim hb
    · intro hz
      exact Or.elim hy (absurd · hz.left) Or.inr
    · intro hz
      refine Or.elim hz Or.inr ?_
      intro hz₁
      apply Or.elim hy <;> apply Or.elim hz₁ <;>
      · intro hz₂ hz₃
        rw [hz₂] at hz₃
        simp at hz₃
  · intro hx
    unfold SDiff.sdiff Set.instSDiffSet Set.diff
    unfold Membership.mem Set.instMembershipSet Set.Mem setOf
    unfold insert Set.instInsertSet Set.insert setOf
    apply Or.elim hx
    · intro hy
      refine ⟨Or.inl hy, ?_⟩
      intro hz
      rw [hy] at hz
      unfold Membership.mem Set.instMembershipSet Set.Mem at hz
      unfold singleton Set.instSingletonSet Set.singleton setOf at hz
      simp only at hz
    · intro hy
      refine ⟨Or.inr (Or.inr hy), ?_⟩
      intro hz
      have hzr := hz.right
      rw [not_or_de_morgan] at hzr
      exact absurd hy hzr.left

lemma left_diff_eq_singleton_one : (A \ B) \ C = {1} := by
  rw [hA, hB, hC]
  ext x
  apply Iff.intro
  · intro hx
    unfold SDiff.sdiff Set.instSDiffSet Set.diff at hx
    unfold Membership.mem Set.instMembershipSet Set.Mem setOf at hx
    unfold insert Set.instInsertSet Set.insert setOf at hx
    have ⟨⟨ha, hb⟩, hc⟩ := hx
    rw [not_or_de_morgan] at hb hc
    apply Or.elim ha
    · simp 
    · intro hy
      apply Or.elim hy
      · intro hz
        exact absurd hz hb.left
      · intro hz
        exact absurd hz hc.left
  · intro hx
    refine ⟨⟨Or.inl hx, ?_⟩, ?_⟩ <;>
    · intro hy
      cases hy with
      | inl y => rw [hx] at y; simp at y
      | inr hz => cases hz with
        | inl y => rw [hx] at y; simp at y
        | inr y => rw [hx] at y; simp at y

/-- ### Exercise 4.14

Show by example that for some sets `A`, `B`, and `C`, the set `A - (B - C)` is
different from `(A - B) - C`.
-/
theorem exercise_4_14 : A \ (B \ C) ≠ (A \ B) \ C := by
  rw [
    @right_diff_eq_insert_one_three A B C hA hB hC,
    @left_diff_eq_singleton_one A B C hA hB hC
  ]
  intro h
  rw [Set.ext_iff] at h
  have := h 3
  simp at this

end

/-- ### Exercise 4.16

Simplify:
`[(A ∪ B ∪ C) ∩ (A ∪ B)] - [(A ∪ (B - C)) ∩ A]`
-/
theorem exercise_4_16 {A B C : Set α}
  : ((A ∪ B ∪ C) ∩ (A ∪ B)) \ ((A ∪ (B \ C)) ∩ A) = B \ A := by
  calc ((A ∪ B ∪ C) ∩ (A ∪ B)) \ ((A ∪ (B \ C)) ∩ A)
    _ = (A ∪ B) \ ((A ∪ (B \ C)) ∩ A) := by rw [Set.union_inter_cancel_left]
    _ = (A ∪ B) \ A := by rw [Set.union_inter_cancel_left]
    _ = B \ A := by rw [Set.union_diff_left]

/-! ### Exercise 4.17

Show that the following four conditions are equivalent.

(a) `A ⊆ B`
(b) `A - B = ∅`
(c) `A ∪ B = B`
(d) `A ∩ B = A`
-/

theorem exercise_4_17_i {A B : Set α} (h : A ⊆ B)
  : A \ B = ∅ := by
  ext x
  apply Iff.intro
  · intro hx
    exact absurd (h hx.left) hx.right
  · intro hx
    exact False.elim hx

theorem exercise_4_17_ii {A B : Set α} (h : A \ B = ∅)
  : A ∪ B = B := by
  suffices A ⊆ B from Set.left_subset_union_eq_self this
  show ∀ t, t ∈ A → t ∈ B
  intro t ht
  rw [Set.ext_iff] at h
  by_contra nt
  exact (h t).mp ⟨ht, nt⟩

theorem exercise_4_17_iii {A B : Set α} (h : A ∪ B = B)
  : A ∩ B = A := by
  suffices A ⊆ B from Set.inter_eq_left_iff_subset.mpr this
  exact Set.union_eq_right_iff_subset.mp h

theorem exercise_4_17_iv {A B : Set α} (h : A ∩ B = A)
  : A ⊆ B := Set.inter_eq_left_iff_subset.mp h

/-- ### Exercise 4.19

Is `𝒫 (A - B)` always equal to `𝒫 A - 𝒫 B`? Is it ever equal to `𝒫 A - 𝒫 B`?
-/
theorem exercise_4_19 {A B : Set α}
  : 𝒫 (A \ B) ≠ (𝒫 A) \ (𝒫 B) := by
  intro h
  have he : ∅ ∈ 𝒫 (A \ B) := by simp
  have ne : ∅ ∉ (𝒫 A) \ (𝒫 B) := by simp
  rw [Set.ext_iff] at h
  have := h ∅
  exact absurd (this.mp he) ne

/-- ### Exercise 4.20

Let `A`, `B`, and `C` be sets such that `A ∪ B = A ∪ C` and `A ∩ B = A ∩ C`.
Show that `B = C`.
-/
theorem exercise_4_20 {A B C : Set α}
  (hu : A ∪ B = A ∪ C) (hi : A ∩ B = A ∩ C) : B = C := by
  ext x
  apply Iff.intro
  · intro hB
    by_cases hA : x ∈ A
    · have : x ∈ A ∩ B := Set.mem_inter hA hB
      rw [hi] at this
      exact this.right
    · have : x ∈ A ∪ B := Set.mem_union_right A hB
      rw [hu] at this
      exact Or.elim this (absurd · hA) (by simp)
  · intro hC
    by_cases hA : x ∈ A
    · have : x ∈ A ∩ C := Set.mem_inter hA hC
      rw [← hi] at this
      exact this.right
    · have : x ∈ A ∪ C := Set.mem_union_right A hC
      rw [← hu] at this
      exact Or.elim this (absurd · hA) (by simp)

/-- ### Exercise 4.21

Show that `⋃ (A ∪ B) = (⋃ A) ∪ (⋃ B)`.
-/
theorem exercise_4_21 {A B : Set (Set α)}
  : ⋃₀ (A ∪ B) = (⋃₀ A) ∪ (⋃₀ B) := by
  ext x
  apply Iff.intro
  · intro hx
    have ⟨t, ht⟩ : ∃ t, t ∈ A ∪ B ∧ x ∈ t := hx
    apply Or.elim ht.left
    · intro hA
      exact Or.inl ⟨t, ⟨hA, ht.right⟩⟩
    · intro hB
      exact Or.inr ⟨t, ⟨hB, ht.right⟩⟩
  · intro hx
    apply Or.elim hx
    · intro hA
      have ⟨t, ht⟩ : ∃ t, t ∈ A ∧ x ∈ t := hA
      exact ⟨t, ⟨Set.mem_union_left B ht.left, ht.right⟩⟩
    · intro hB
      have ⟨t, ht⟩ : ∃ t, t ∈ B ∧ x ∈ t := hB
      exact ⟨t, ⟨Set.mem_union_right A ht.left, ht.right⟩⟩

/-- ### Exercise 4.22

Show that if `A` and `B` are nonempty sets, then `⋂ (A ∪ B) = ⋂ A ∩ ⋂ B`.
-/
theorem exercise_4_22 {A B : Set (Set α)}
  : ⋂₀ (A ∪ B) = ⋂₀ A ∩ ⋂₀ B := by
  ext x
  apply Iff.intro
  · intro hx
    have : ∀ t : Set α, t ∈ A ∪ B → x ∈ t := hx
    show (∀ t : Set α, t ∈ A → x ∈ t) ∧ (∀ t : Set α, t ∈ B → x ∈ t)
    rw [← forall_and]
    intro t
    exact ⟨
      fun ht => this t (Set.mem_union_left B ht),
      fun ht => this t (Set.mem_union_right A ht)
    ⟩
  · intro hx
    have : ∀ t : Set α, (t ∈ A → x ∈ t) ∧ (t ∈ B → x ∈ t) := by
      have : (∀ t : Set α, t ∈ A → x ∈ t) ∧ (∀ t : Set α, t ∈ B → x ∈ t) := hx
      rwa [← forall_and] at this
    show ∀ (t : Set α), t ∈ A ∪ B → x ∈ t
    intro t ht
    apply Or.elim ht
    · intro hA
      exact (this t).left hA
    · intro hB
      exact (this t).right hB

/-- ### Exercise 4.24a

Show that is `𝓐` is nonempty, then `𝒫 (⋂ 𝓐) = ⋂ { 𝒫 X | X ∈ 𝓐 }`.
-/
theorem exercise_4_24a {𝓐 : Set (Set α)}
  : 𝒫 (⋂₀ 𝓐) = ⋂₀ { 𝒫 X | X ∈ 𝓐 } := by
  calc 𝒫 (⋂₀ 𝓐)
    _ = { x | x ⊆ ⋂₀ 𝓐 } := rfl
    _ = { x | x ⊆ { y | ∀ X, X ∈ 𝓐 → y ∈ X } } := rfl
    _ = { x | ∀ t ∈ x, t ∈ { y | ∀ X, X ∈ 𝓐 → y ∈ X } } := rfl
    _ = { x | ∀ t ∈ x, (∀ X, X ∈ 𝓐 → t ∈ X) } := rfl
    _ = { x | ∀ X ∈ 𝓐, (∀ t, t ∈ x → t ∈ X) } := by
      ext
      rw [Set.mem_setOf, Set.mem_setOf, forall_mem_comm (· ∈ ·)]
    _ = { x | ∀ X ∈ 𝓐, x ⊆ X} := rfl
    _ = { x | ∀ X ∈ 𝓐, x ∈ 𝒫 X } := rfl
    _ = { x | ∀ t ∈ { 𝒫 X | X ∈ 𝓐 }, x ∈ t} := by simp
    _ = ⋂₀ { 𝒫 X | X ∈ 𝓐 } := rfl

/-- ### Exercise 4.24b

Show that
```
⋃ {𝒫 X | X ∈ 𝓐} ⊆ 𝒫 ⋃ 𝓐.
```
Under what conditions does equality hold?
-/
theorem exercise_4_24b {𝓐 : Set (Set α)}
  : (⋃₀ { 𝒫 X | X ∈ 𝓐 } ⊆ 𝒫 ⋃₀ 𝓐)
  ∧ ((⋃₀ { 𝒫 X | X ∈ 𝓐 } = 𝒫 ⋃₀ 𝓐) ↔ (⋃₀ 𝓐 ∈ 𝓐)) := by
  have hS : (⋃₀ { 𝒫 X | X ∈ 𝓐 } ⊆ 𝒫 ⋃₀ 𝓐) := by
    simp
    exact exercise_3_3
  refine ⟨hS, ?_⟩
  apply Iff.intro
  · intro rS
    have rS : 𝒫 ⋃₀ 𝓐 ⊆ ⋃₀ { 𝒫 X | X ∈ 𝓐 } :=
      (Set.Subset.antisymm_iff.mp rS).right
    have hA : ⋃₀ 𝓐 ∈ ⋃₀ { 𝒫 X | X ∈ 𝓐 } :=
      rS Set.self_mem_powerset_self
    conv at hA =>
      rhs
      unfold Set.sUnion sSup Set.instSupSetSet
      simp only
    have ⟨X, ⟨⟨x, hx⟩, ht⟩⟩ := Set.mem_setOf.mp hA
    have : ⋃₀ 𝓐 = x := by
      rw [← hx.right] at ht
      have hl : ⋃₀ 𝓐 ⊆ x := ht
      have hr : x ⊆ ⋃₀ 𝓐 := exercise_3_3 x hx.left
      exact Set.Subset.antisymm hl hr
    rw [← this] at hx
    exact hx.left
  · intro hA
    suffices 𝒫 ⋃₀ 𝓐 ⊆ ⋃₀ { 𝒫 X | X ∈ 𝓐 } from
      subset_antisymm hS this
    show ∀ x, x ∈ 𝒫 ⋃₀ 𝓐 → x ∈ ⋃₀ { x | ∃ X, X ∈ 𝓐 ∧ 𝒫 X = x }
    intro x hx
    unfold Set.sUnion sSup Set.instSupSetSet
    simp only [Set.mem_setOf_eq, exists_exists_and_eq_and, Set.mem_powerset_iff]
    exact ⟨⋃₀ 𝓐, ⟨hA, hx⟩⟩

/-- ### Exercise 4.25

Is `A ∪ (⋃ 𝓑)` always the same as `⋃ { A ∪ X | X ∈ 𝓑 }`? If not, then under
what conditions does equality hold? 
-/
theorem exercise_4_25 {A : Set α} (𝓑 : Set (Set α))
  : (A ∪ (⋃₀ 𝓑) = ⋃₀ { A ∪ X | X ∈ 𝓑 }) ↔ (A = ∅ ∨ Set.Nonempty 𝓑) := by
  apply Iff.intro
  · intro h
    by_cases h𝓑 : Set.Nonempty 𝓑
    · exact Or.inr h𝓑
    · have : 𝓑 = ∅ := Set.not_nonempty_iff_eq_empty.mp h𝓑
      rw [this] at h
      simp at h
      exact Or.inl h
  · intro h
    apply Or.elim h
    · intro hA
      rw [hA]
      simp
    · intro h𝓑
      calc A ∪ (⋃₀ 𝓑)
        _ = { x | x ∈ A ∨ x ∈ ⋃₀ 𝓑} := rfl
        _ = { x | x ∈ A ∨ (∃ b ∈ 𝓑, x ∈ b) } := rfl
        _ = { x | ∃ b ∈ 𝓑, x ∈ A ∨ x ∈ b } := by
          ext x
          rw [Set.mem_setOf, Set.mem_setOf]
          apply Iff.intro
          · intro hx
            apply Or.elim hx
            · intro hA
              have ⟨b, hb⟩ := Set.nonempty_def.mp h𝓑
              exact ⟨b, ⟨hb, Or.inl hA⟩⟩
            · intro ⟨b, hb⟩
              exact ⟨b, ⟨hb.left, Or.inr hb.right⟩⟩
          · intro ⟨b, ⟨hb, hx⟩⟩
            apply Or.elim hx
            · exact (Or.inl ·)
            · intro h
              exact Or.inr ⟨b, ⟨hb, h⟩⟩
        _ = { x | ∃ b ∈ 𝓑, x ∈ A ∪ b } := rfl
        _ = { x | ∃ t, t ∈ { y | ∃ X, X ∈ 𝓑 ∧ A ∪ X = y } ∧ x ∈ t } := by simp
        _ = ⋃₀ { A ∪ X | X ∈ 𝓑 } := rfl

end Enderton.Set.Chapter_2