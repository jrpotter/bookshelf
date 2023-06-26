import Bookshelf.Enderton.Set.Chapter_2
import Common.Set.OrderedPair
import Common.Set.Relation

/-! # Enderton.Chapter_3

Relations and Functions
-/

namespace Enderton.Set.Chapter_3

/-- ### Theorem 3B

If `x ∈ C` and `y ∈ C`, then `⟨x, y⟩ ∈ 𝒫 𝒫 C`.
-/
theorem theorem_3b {C : Set α} (hx : x ∈ C) (hy : y ∈ C)
  : OrderedPair x y ∈ 𝒫 𝒫 C := by
  have hxs : {x} ⊆ C := Set.singleton_subset_iff.mpr hx
  have hxys : {x, y} ⊆ C := Set.mem_mem_imp_pair_subset hx hy
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
      · intro ⟨h₁, b, h₂⟩
        exact ⟨b, h₂.left, h₁, h₂.right⟩
      · intro ⟨b, h₁, h₂, h₃⟩
        exact ⟨h₂, b, h₁, h₃⟩
    _ = ⋃₀ { Set.prod A p | p ∈ 𝓑 } := by
      ext x
      rw [Set.mem_setOf_eq]
      unfold Set.sUnion sSup Set.instSupSetSet
      simp only [Set.mem_setOf_eq, exists_exists_and_eq_and]
      apply Iff.intro
      · intro ⟨b, h₁, h₂, h₃⟩
        exact ⟨b, h₁, h₂, h₃⟩
      · intro ⟨b, h₁, h₂, h₃⟩
        exact ⟨b, h₁, h₂, h₃⟩

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
theorem theorem_3d {A : Set (Set (Set α))} (h : OrderedPair x y ∈ A)
  : x ∈ ⋃₀ (⋃₀ A) ∧ y ∈ ⋃₀ (⋃₀ A) := by
  have hp := Chapter_2.exercise_3_3 (OrderedPair x y) h
  unfold OrderedPair at hp  
  have hq : {x, y} ∈ ⋃₀ A := hp (by simp)
  have : {x, y} ⊆ ⋃₀ ⋃₀ A := Chapter_2.exercise_3_3 {x, y} hq
  exact ⟨this (by simp), this (by simp)⟩

/-- ### Exercise 6.6

Show that a set `A` is a relation **iff** `A ⊆ dom A × ran A`.
-/
theorem exercise_6_6 {A : Set.Relation α}
  : A ⊆ Set.prod (A.dom) (A.ran) := by
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

/-- ### Exercise 6.7

Show that if `R` is a relation, then `fld R = ⋃ ⋃ R`.
-/
theorem exercise_6_7 {R : Set.Relation α}
  : R.fld = ⋃₀ ⋃₀ R.toOrderedPairs := by
  let img := R.toOrderedPairs
  suffices R.fld ⊆ ⋃₀ ⋃₀ img ∧ ⋃₀ ⋃₀ img ⊆ R.fld from
    Set.Subset.antisymm_iff.mpr this

  apply And.intro
  · show ∀ x, x ∈ R.fld → x ∈ ⋃₀ ⋃₀ img
    intro x hx
    apply Or.elim hx
    · intro hd
      unfold Set.Relation.dom Prod.fst at hd
      simp only [
        Set.mem_image, Prod.exists, exists_and_right, exists_eq_right
      ] at hd
      have ⟨y, hp⟩ := hd
      have hm : OrderedPair x y ∈ Set.image (fun p => OrderedPair p.1 p.2) R := by
        unfold Set.image
        simp only [Prod.exists, Set.mem_setOf_eq]
        exact ⟨x, ⟨y, ⟨hp, rfl⟩⟩⟩
      unfold OrderedPair at hm
      have : {x} ∈ ⋃₀ img := Chapter_2.exercise_3_3 {{x}, {x, y}} hm (by simp)
      exact (Chapter_2.exercise_3_3 {x} this) (show x ∈ {x} by rfl)
    · intro hr
      unfold Set.Relation.ran Prod.snd at hr
      simp only [Set.mem_image, Prod.exists, exists_eq_right] at hr
      have ⟨t, ht⟩ := hr
      have hm : OrderedPair t x ∈ Set.image (fun p => OrderedPair p.1 p.2) R := by
        simp only [Set.mem_image, Prod.exists]
        exact ⟨t, ⟨x, ⟨ht, rfl⟩⟩⟩
      unfold OrderedPair at hm
      have : {t, x} ∈ ⋃₀ img := Chapter_2.exercise_3_3 {{t}, {t, x}} hm
        (show {t, x} ∈ {{t}, {t, x}} by simp)
      exact Chapter_2.exercise_3_3 {t, x} this (show x ∈ {t, x} by simp)

  · show ∀ t, t ∈ ⋃₀ ⋃₀ img → t ∈ Set.Relation.fld R
    intro t ht
    have ⟨T, hT⟩ : ∃ T ∈ ⋃₀ img, t ∈ T := ht
    have ⟨T', hT'⟩ : ∃ T' ∈ img, T ∈ T' := hT.left
    dsimp only at hT'
    unfold Set.Relation.toOrderedPairs at hT'
    simp only [Set.mem_image, Prod.exists] at hT'
    have ⟨x, ⟨y, ⟨p, hp⟩⟩⟩ := hT'.left
    have hr := hT'.right
    rw [← hp] at hr
    unfold OrderedPair at hr
    simp only [Set.mem_singleton_iff, Set.mem_insert_iff] at hr

    -- Use `exercise_6_6` to prove that if `t = x` then `t ∈ dom R` and if
    -- `t = y` then `t ∈ ran R`.
    have hxy_mem : t = x ∨ t = y → t ∈ Set.Relation.fld R := by
      intro ht
      have hz : R ⊆ Set.prod (R.dom) (R.ran) := exercise_6_6
      have : (x, y) ∈ Set.prod (R.dom) (R.ran) := hz p
      unfold Set.prod at this
      simp at this
      apply Or.elim ht
      · intro ht'
        rw [← ht'] at this
        exact Or.inl this.left
      · intro ht'
        rw [← ht'] at this
        exact Or.inr this.right

    -- Eliminate `T = {x} ∨ T = {x, y}`.
    apply Or.elim hr
    · intro hx
      have := hT.right
      rw [hx] at this
      simp only [Set.mem_singleton_iff] at this
      exact hxy_mem (Or.inl this)
    · intro hxy
      have := hT.right
      rw [hxy] at this
      simp only [Set.mem_singleton_iff, Set.mem_insert_iff] at this
      exact hxy_mem this

section

open Set.Relation

/-- ### Exercise 6.8 (i)

Show that for any set `𝓐`:
```
dom ⋃ A = ⋃ { dom R | R ∈ 𝓐 }
```
-/
theorem exercise_6_8_i {A : Set (Set.Relation α)}
  : dom (⋃₀ A) = ⋃₀ { dom R | R ∈ A } := by
  ext x
  unfold dom Prod.fst
  simp only [
    Set.mem_image,
    Set.mem_sUnion,
    Prod.exists,
    exists_and_right,
    exists_eq_right,
    Set.mem_setOf_eq,
    exists_exists_and_eq_and
  ]
  apply Iff.intro
  · intro ⟨y, t, ht, hx⟩
    exact ⟨t, ht, y, hx⟩
  · intro ⟨t, ht, y, hx⟩
    exact ⟨y, t, ht, hx⟩

/-- ### Exercise 6.8 (ii)

Show that for any set `𝓐`:
```
ran ⋃ A = ⋃ { ran R | R ∈ 𝓐 }
```
-/
theorem exercise_6_8_ii {A : Set (Set.Relation α)}
  : ran (⋃₀ A) = ⋃₀ { ran R | R ∈ A } := by
  ext x
  unfold ran Prod.snd
  simp only [
    Set.mem_image,
    Set.mem_sUnion,
    Prod.exists,
    exists_eq_right,
    Set.mem_setOf_eq,
    exists_exists_and_eq_and
  ]
  apply Iff.intro
  · intro ⟨t, ⟨y, ⟨hy, ht⟩⟩⟩
    exact ⟨y, ⟨hy, ⟨t, ht⟩⟩⟩
  · intro ⟨y, ⟨hy, ⟨t, ht⟩⟩⟩
    exact ⟨t, ⟨y, ⟨hy, ht⟩⟩⟩

/-- ### Exercise 6.9 (i)

Discuss the result of replacing the union operation by the intersection
operation in the preceding problem.
```
dom ⋃ A = ⋃ { dom R | R ∈ 𝓐 }
```
-/
theorem exercise_6_9_i {A : Set (Set.Relation α)}
  : dom (⋂₀ A) ⊆ ⋂₀ { dom R | R ∈ A } := by
  show ∀ x, x ∈ dom (⋂₀ A) → x ∈ ⋂₀ { dom R | R ∈ A }
  unfold dom Prod.fst
  simp only [
    Set.mem_image,
    Set.mem_sInter,
    Prod.exists,
    exists_and_right,
    exists_eq_right,
    Set.mem_setOf_eq,
    forall_exists_index,
    and_imp,
    forall_apply_eq_imp_iff₂
  ]
  intro _ y hy R hR
  exact ⟨y, hy R hR⟩

/-- ### Exercise 6.9 (ii)

Discuss the result of replacing the union operation by the intersection
operation in the preceding problem.
```
ran ⋃ A = ⋃ { ran R | R ∈ 𝓐 }
```
-/
theorem exercise_6_9_ii {A : Set (Set.Relation α)}
  : ran (⋂₀ A) ⊆ ⋂₀ { ran R | R ∈ A } := by
  show ∀ x, x ∈ ran (⋂₀ A) → x ∈ ⋂₀ { ran R | R ∈ A }
  unfold ran Prod.snd
  simp only [
    Set.mem_image,
    Set.mem_sInter,
    Prod.exists,
    exists_and_right,
    exists_eq_right,
    Set.mem_setOf_eq,
    forall_exists_index,
    and_imp,
    forall_apply_eq_imp_iff₂
  ]
  intro _ y hy R hR
  exact ⟨y, hy R hR⟩

/-- ### Theorem 3G (i)

Assume that `F` is a one-to-one function. If `x ∈ dom F`, then `F⁻¹(F(x)) = x`.
-/
theorem theorem_3g_i {α : Type _} {x y : α} {F : Set.Relation α}
  (hF : isOneToOne F) (hx : x ∈ dom F)
  : ∃! y, (x, y) ∈ F ∧ (y, x) ∈ F.inv := by
  simp only [mem_self_comm_mem_inv, and_self]
  have ⟨y, hy⟩ := dom_exists hx
  refine ⟨y, hy, ?_⟩
  intro y₁ hy₁
  unfold isOneToOne at hF
  exact (single_valued_eq_unique hF.left hy hy₁).symm

/-- ### Theorem 3G (ii)

Assume that `F` is a one-to-one function. If `y ∈ ran F`, then `F(F⁻¹(y)) = y`.
-/
theorem theorem_3g_ii {F : Set.Relation α}
  (hF : isOneToOne F) (hy : y ∈ F.ran)
  : ∃! x, (x, y) ∈ F ∧ (y, x) ∈ F.inv := by
  simp only [mem_self_comm_mem_inv, and_self]
  have ⟨x, hx⟩ := ran_exists hy
  refine ⟨x, hx, ?_⟩
  intro x₁ hx₁
  unfold isOneToOne at hF
  exact (single_rooted_eq_unique hF.right hx hx₁).symm

/-- ### Theorem 3H

Assume that `F` and `G` are functions. Then
```
dom (F ∘ G) = {x ∈ dom G | G(x) ∈ dom F}.
```
-/
theorem theorem_3h_dom {F G : Set.Relation α}
  (_ : isSingleValued F) (hG : isSingleValued G)
  : dom (comp F G) = {x ∈ dom G | ∃! y, (x, y) ∈ G ∧ y ∈ dom F } := by
  let rhs := {x ∈ dom G | ∃! y, (x, y) ∈ G ∧ y ∈ dom F }
  suffices dom (comp F G) ⊆ rhs ∧ rhs ⊆ dom (comp F G) from
    Set.Subset.antisymm_iff.mpr this
  apply And.intro
  · show ∀ t, t ∈ dom (comp F G) → t ∈ rhs
    intro t ht
    simp only [Set.mem_setOf_eq]
    have ⟨z, hz⟩ := dom_exists ht
    refine ⟨dom_comp_imp_dom_self ht, ?_⟩
    simp only [Set.mem_setOf_eq] at hz
    have ⟨a, ha⟩ := hz
    unfold dom
    simp only [Set.mem_image, Prod.exists, exists_and_right, exists_eq_right]
    unfold ExistsUnique
    simp only [and_imp, forall_exists_index]
    refine ⟨a, ⟨ha.left, z, ha.right⟩, ?_⟩
    intro y₁ hy₁
    exact fun _ _ => single_valued_eq_unique hG hy₁ ha.left
  · show ∀ t, t ∈ rhs → t ∈ dom (comp F G)
    intro t ht
    simp only [Set.mem_setOf_eq] at ht
    unfold dom
    simp only [Set.mem_image, Prod.exists, exists_and_right, exists_eq_right]
    have ⟨a, ha⟩ := ht.right
    simp at ha
    have ⟨b, hb⟩ := dom_exists ha.left.right
    refine ⟨b, ?_⟩
    unfold comp
    simp only [Set.mem_setOf_eq]
    exact ⟨a, ha.left.left, hb⟩

end

end Enderton.Set.Chapter_3