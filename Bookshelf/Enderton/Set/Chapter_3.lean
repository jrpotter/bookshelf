import Mathlib.Data.Set.Basic

import Bookshelf.Enderton.Set.Chapter_2
import Common.Logic.Basic
import Common.Set.Basic

/-! # Enderton.Chapter_3

Relations and Functions
-/

namespace Enderton.Set.Chapter_3

/-! ## Ordered Pairs -/

/--
Kazimierz Kuratowski's definition of an ordered pair.
-/
def OrderedPair (x : α) (y : β) : Set (Set (α ⊕ β)) :=
  {{Sum.inl x}, {Sum.inl x, Sum.inr y}}

namespace OrderedPair

/--
For any sets `x`, `y`, `u`, and `v`, `⟨u, v⟩ = ⟨x, y⟩` **iff** `u = x ∧ v = y`.
-/
theorem ext_iff {x u : α} {y v : β}
  : (OrderedPair x y = OrderedPair u v) ↔ (x = u ∧ y = v) := by
  unfold OrderedPair
  apply Iff.intro
  · intro h
    have hu := Set.ext_iff.mp h {Sum.inl u}
    have huv := Set.ext_iff.mp h {Sum.inl u, Sum.inr v}
    simp only [
      Set.mem_singleton_iff,
      Set.mem_insert_iff,
      true_or,
      iff_true
    ] at hu
    simp only [
      Set.mem_singleton_iff,
      Set.mem_insert_iff,
      or_true,
      iff_true
    ] at huv
    apply Or.elim hu
    · apply Or.elim huv
      · -- #### Case 1
        -- `{u} = {x}` and `{u, v} = {x}`.
        intro huv_x hu_x
        rw [Set.singleton_eq_singleton_iff] at hu_x
        rw [hu_x] at huv_x
        have hx_v := Set.pair_eq_singleton_mem_imp_eq_self huv_x
        rw [hu_x, hx_v] at h
        simp only [Set.mem_singleton_iff, Set.insert_eq_of_mem] at h
        have := Set.pair_eq_singleton_mem_imp_eq_self $
          Set.pair_eq_singleton_mem_imp_eq_self h
        rw [← hx_v] at this
        injection hu_x with p
        injection this with q
        exact ⟨p.symm, q⟩
      · -- #### Case 2
        -- `{u} = {x}` and `{u, v} = {x, y}`.
        intro huv_xy hu_x
        rw [Set.singleton_eq_singleton_iff] at hu_x
        rw [hu_x] at huv_xy
        by_cases hx_v : Sum.inl x = Sum.inr v
        · rw [hx_v] at huv_xy
          simp at huv_xy
          have := Set.pair_eq_singleton_mem_imp_eq_self huv_xy.symm
          injection hu_x with p
          injection this with q
          exact ⟨p.symm, q⟩
        · rw [Set.ext_iff] at huv_xy
          have := huv_xy (Sum.inr v)
          simp at this
          injection hu_x with p
          exact ⟨p.symm, this.symm⟩
    · apply Or.elim huv
      · -- #### Case 3
        -- `{u} = {x, y}` and `{u, v} = {x}`.
        intro huv_x _
        rw [Set.ext_iff] at huv_x
        have hv_x := huv_x (Sum.inr v)
        simp only [
          Set.mem_singleton_iff,
          Set.mem_insert_iff,
          or_true,
          true_iff
        ] at hv_x
      · -- #### Case 4
        -- `{u} = {x, y}` and `{u, v} = {x, y}`.
        intro _ hu_xy
        rw [Set.ext_iff] at hu_xy
        have hy_u := hu_xy (Sum.inr y)
        simp only [
          Set.mem_singleton_iff,
          Set.mem_insert_iff,
          or_true,
          iff_true
        ] at hy_u
  · intro h
    rw [h.left, h.right]

end OrderedPair

/-- ### Theorem 3B

If `x ∈ C` and `y ∈ C`, then `⟨x, y⟩ ∈ 𝒫 𝒫 C`.
-/
theorem theorem_3b {C : Set (α ⊕ α)} (hx : Sum.inl x ∈ C) (hy : Sum.inr y ∈ C)
  : OrderedPair x y ∈ 𝒫 𝒫 C := by
  have hxs : {Sum.inl x} ⊆ C := Set.singleton_subset_iff.mpr hx
  have hxys : {Sum.inl x, Sum.inr y} ⊆ C := Set.mem_mem_imp_pair_subset hx hy
  exact Set.mem_mem_imp_pair_subset hxs hxys

/-- ### Exercise 5.1

Suppose that we attempted to generalize the Kuratowski definitions of ordered
pairs to ordered triples by defining
```
⟨x, y, z⟩* = {{x}, {x, y}, {x, y, z}}.open Set

```
Show that this definition is unsuccessful by giving examples of objects `u`,
`v`, `w`, `x`, `y`, `z` with `⟨x, y, z⟩* = ⟨u, v, w⟩*` but with either `y ≠ v`
or `z ≠ w` (or both).
-/
theorem exercise_5_1 {x y z u v w : ℕ}
  (hx : x = 1) (hy : y = 1) (hz : z = 2)
  (hu : u = 1) (hv : v = 2) (hw : w = 2)
  : ({{x}, {x, y}, {x, y, z}} : Set (Set ℕ)) = {{u}, {u, v}, {u, v, w}}
  ∧ y ≠ v := by
  apply And.intro
  · rw [hx, hy, hz, hu, hv, hw]
    simp
  · rw [hy, hv]
    simp only

/-- ### Exercise 5.2a

Show that `A × (B ∪ C) = (A × B) ∪ (A × C)`.
-/
theorem exercise_5_2a {A : Set α} {B C : Set β}
  : Set.prod A (B ∪ C) = (Set.prod A B) ∪ (Set.prod A C) := by
  calc Set.prod A (B ∪ C)
    _ = { p | p.1 ∈ A ∧ p.2 ∈ B ∪ C } := rfl
    _ = { p | p.1 ∈ A ∧ (p.2 ∈ B ∨ p.2 ∈ C) } := rfl
    _ = { p | (p.1 ∈ A ∧ p.2 ∈ B) ∨ (p.1 ∈ A ∧ p.2 ∈ C) } := by
      ext x
      rw [Set.mem_setOf_eq]
      conv => lhs; rw [and_or_left]
    _ = { p | p ∈ Set.prod A B ∨ (p ∈ Set.prod A C) } := rfl
    _ = (Set.prod A B) ∪ (Set.prod A C) := rfl

/-- ### Exercise 5.2b

Show that if `A × B = A × C` and `A ≠ ∅`, then `B = C`.
-/
theorem exercise_5_2b {A : Set α} {B C : Set β}
  (h : Set.prod A B = Set.prod A C) (hA : Set.Nonempty A)
  : B = C := by
  by_cases hB : Set.Nonempty B
  · suffices B ⊆ C ∧ C ⊆ B from Set.Subset.antisymm_iff.mpr this
    have ⟨a, ha⟩ := hA
    apply And.intro
    · show ∀ t, t ∈ B → t ∈ C
      intro t ht
      have : (a, t) ∈ Set.prod A B := ⟨ha, ht⟩
      rw [h] at this
      exact this.right
    · show ∀ t, t ∈ C → t ∈ B
      intro t ht
      have : (a, t) ∈ Set.prod A C := ⟨ha, ht⟩
      rw [← h] at this
      exact this.right
  · have nB : B = ∅ := Set.not_nonempty_iff_eq_empty.mp hB
    rw [nB, Set.prod_right_emptyset_eq_emptyset, Set.ext_iff] at h
    rw [nB]
    by_contra nC
    have ⟨a, ha⟩ := hA
    have ⟨c, hc⟩ := Set.nonempty_iff_ne_empty.mpr (Ne.symm nC)
    exact (h (a, c)).mpr ⟨ha, hc⟩

/-- ### Exercise 5.3

Show that `A × ⋃ 𝓑 = ⋃ {A × X | X ∈ 𝓑}`.
-/
theorem exercise_5_3 {A : Set (Set α)} {𝓑 : Set (Set β)}
  : Set.prod A (⋃₀ 𝓑) = ⋃₀ {Set.prod A X | X ∈ 𝓑} := by
  calc Set.prod A (⋃₀ 𝓑)
    _ = { p | p.1 ∈ A ∧ p.2 ∈ ⋃₀ 𝓑} := rfl
    _ = { p | p.1 ∈ A ∧ ∃ b ∈ 𝓑, p.2 ∈ b } := rfl
    _ = { p | ∃ b ∈ 𝓑, p.1 ∈ A ∧ p.2 ∈ b } := by
      ext x
      rw [Set.mem_setOf_eq]
      apply Iff.intro
      · intro ⟨h₁, ⟨b, h₂⟩⟩
        exact ⟨b, ⟨h₂.left, ⟨h₁, h₂.right⟩⟩⟩
      · intro ⟨b, ⟨h₁, ⟨h₂, h₃⟩⟩⟩
        exact ⟨h₂, ⟨b, ⟨h₁, h₃⟩⟩⟩
    _ = ⋃₀ { Set.prod A p | p ∈ 𝓑 } := by
      ext x
      rw [Set.mem_setOf_eq]
      unfold Set.sUnion sSup Set.instSupSetSet
      simp only [Set.mem_setOf_eq, exists_exists_and_eq_and]
      apply Iff.intro
      · intro ⟨b, ⟨h₁, ⟨h₂, h₃⟩⟩⟩
        exact ⟨b, ⟨h₁, ⟨h₂, h₃⟩⟩⟩
      · intro ⟨b, ⟨h₁, ⟨h₂, h₃⟩⟩⟩
        exact ⟨b, ⟨h₁, ⟨h₂, h₃⟩⟩⟩

/-- ### Exercise 5.5a

Assume that `A` and `B` are given sets, and show that there exists a set `C`
such that for any `y`,
```
y ∈ C ↔ y = {x} × B for some x in A.
```
In other words, show that `{{x} × B | x ∈ A}` is a set.
-/
theorem exercise_5_5a {A : Set α} {B : Set β}
  : ∃ C : Set (Set (α × β)),
      y ∈ C ↔ ∃ x ∈ A, y = Set.prod {x} B := by
  let C := {y ∈ 𝒫 (Set.prod A B) | ∃ a ∈ A, ∀ x, (x ∈ y ↔ ∃ b ∈ B, x = (a, b))}
  refine ⟨C, ?_⟩
  apply Iff.intro
  · intro hC
    simp only [Set.mem_setOf_eq] at hC
    have ⟨_, ⟨a, ⟨ha, h⟩⟩⟩ := hC
    refine ⟨a, ⟨ha, ?_⟩⟩
    ext x
    apply Iff.intro
    · intro hxy
      unfold Set.prod
      simp only [Set.mem_singleton_iff, Set.mem_setOf_eq]
      have ⟨b, ⟨hb, hx⟩⟩ := (h x).mp hxy
      rw [Prod.ext_iff] at hx
      simp only at hx
      rw [← hx.right] at hb
      exact ⟨hx.left, hb⟩
    · intro hx
      simp only [Set.mem_singleton_iff, Set.mem_setOf_eq] at hx
      have := (h (a, x.snd)).mpr ⟨x.snd, ⟨hx.right, rfl⟩⟩
      have hxab : x = (a, x.snd) := by
        ext <;> simp
        exact hx.left
      rwa [← hxab] at this
  · intro ⟨x, ⟨hx, hy⟩⟩
    show y ∈ 𝒫 Set.prod A B ∧ ∃ a, a ∈ A ∧
           ∀ (x : α × β), x ∈ y ↔ ∃ b, b ∈ B ∧ x = (a, b)
    apply And.intro
    · simp only [Set.mem_powerset_iff]
      rw [hy]
      unfold Set.prod
      simp only [
        Set.mem_singleton_iff,
        Set.setOf_subset_setOf,
        and_imp,
        Prod.forall
      ]
      intro a b ha hb
      exact ⟨by rw [ha]; exact hx, hb⟩
    · refine ⟨x, ⟨hx, ?_⟩⟩
      intro p
      apply Iff.intro
      · intro hab
        rw [hy] at hab
        unfold Set.prod at hab
        simp only [Set.mem_singleton_iff, Set.mem_setOf_eq] at hab
        exact ⟨p.2, ⟨hab.right, by ext; exact hab.left; simp⟩⟩
      · intro ⟨b, ⟨hb, hab⟩⟩
        rw [hy]
        unfold Set.prod
        simp only [Set.mem_singleton_iff, Set.mem_setOf_eq]
        rw [Prod.ext_iff] at hab
        simp only at hab
        rw [hab.right]
        exact ⟨hab.left, hb⟩

/-- ### Exercise 5.5b

With `A`, `B`, and `C` as above, show that `A × B = ∪ C`.
-/
theorem exercise_5_5b {A : Set α} (B : Set β)
  : Set.prod A B = ⋃₀ {Set.prod ({x} : Set α) B | x ∈ A} := by
  suffices Set.prod A B ⊆ ⋃₀ {Set.prod {x} B | x ∈ A} ∧
           ⋃₀ {Set.prod {x} B | x ∈ A} ⊆ Set.prod A B from
    Set.Subset.antisymm_iff.mpr this
  apply And.intro
  · show ∀ t, t ∈ Set.prod A B → t ∈ ⋃₀ {Set.prod {x} B | x ∈ A}
    intro t h
    simp only [Set.mem_setOf_eq] at h
    unfold Set.sUnion sSup Set.instSupSetSet
    simp only [Set.mem_setOf_eq, exists_exists_and_eq_and]
    unfold Set.prod at h
    simp only [Set.mem_setOf_eq] at h
    refine ⟨t.fst, ⟨h.left, ?_⟩⟩
    unfold Set.prod
    simp only [Set.mem_singleton_iff, Set.mem_setOf_eq, true_and]
    exact h.right
  · show ∀ t, t ∈ ⋃₀ {Set.prod {x} B | x ∈ A} → t ∈ Set.prod A B
    unfold Set.prod
    intro t ht
    simp only [
      Set.mem_singleton_iff,
      Set.mem_sUnion,
      Set.mem_setOf_eq,
      exists_exists_and_eq_and
    ] at ht
    have ⟨a, ⟨h, ⟨ha, hb⟩⟩⟩ := ht
    simp only [Set.mem_setOf_eq]
    rw [← ha] at h
    exact ⟨h, hb⟩

/-- ### Theorem 3D

If `⟨x, y⟩ ∈ A`, then `x` and `y` belong to `⋃ ⋃ A`.
-/
theorem theorem_3d {A : Set (Set (Set (α ⊕ α)))} (h : OrderedPair x y ∈ A)
  : Sum.inl x ∈ ⋃₀ (⋃₀ A) ∧ Sum.inr y ∈ ⋃₀ (⋃₀ A) := by
  have hp : OrderedPair x y ⊆ ⋃₀ A := Chapter_2.exercise_3_3 (OrderedPair x y) h
  have hp' : ∀ t, t ∈ {{Sum.inl x}, {Sum.inl x, Sum.inr y}} → t ∈ ⋃₀ A := hp

  have hq := hp' {Sum.inl x, Sum.inr y} (by simp)
  have hq' := Chapter_2.exercise_3_3 {Sum.inl x, Sum.inr y} hq

  have : ∀ t, t ∈ {Sum.inl x, Sum.inr y} → t ∈ ⋃₀ (⋃₀ A) := hq'
  exact ⟨this (Sum.inl x) (by simp), this (Sum.inr y) (by simp)⟩

/-- ### Exercise 6.6

Show that a set `A` is a relation **iff** `A ⊆ dom A × ran A`.
-/
theorem exercise_6_6 {A : Set (α × β)}
  : A ⊆ Set.prod (Prod.fst '' A) (Prod.snd '' A) := by
  show ∀ t, t ∈ A → t ∈ Set.prod (Prod.fst '' A) (Prod.snd '' A)
  intro (a, b) ht
  unfold Set.prod
  simp only [
    Set.mem_image,
    Prod.exists,
    exists_and_right,
    exists_eq_right,
    Set.mem_setOf_eq
  ]
  exact ⟨⟨b, ht⟩, ⟨a, ht⟩⟩

end Enderton.Set.Chapter_3