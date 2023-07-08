import Bookshelf.Enderton.Set.Chapter_2
import Bookshelf.Enderton.Set.OrderedPair
import Bookshelf.Enderton.Set.Relation
import Mathlib.Tactic.CasesM

/-! # Enderton.Set.Chapter_3

Relations and Functions
-/

namespace Enderton.Set.Chapter_3

/-- #### Theorem 3B

If `x ∈ C` and `y ∈ C`, then `⟨x, y⟩ ∈ 𝒫 𝒫 C`.
-/
theorem theorem_3b {C : Set α} (hx : x ∈ C) (hy : y ∈ C)
  : OrderedPair x y ∈ 𝒫 𝒫 C := by
  have hxs : {x} ⊆ C := Set.singleton_subset_iff.mpr hx
  have hxys : {x, y} ⊆ C := Set.mem_mem_imp_pair_subset hx hy
  exact Set.mem_mem_imp_pair_subset hxs hxys

/-- #### Exercise 3.1

Suppose that we attempted to generalize the Kuratowski definitions of ordered
pairs to ordered triples by defining
```
⟨x, y, z⟩* = {{x}, {x, y}, {x, y, z}}.open Set

```
Show that this definition is unsuccessful by giving examples of objects `u`,
`v`, `w`, `x`, `y`, `z` with `⟨x, y, z⟩* = ⟨u, v, w⟩*` but with either `y ≠ v`
or `z ≠ w` (or both).
-/
theorem exercise_3_1 {x y z u v w : ℕ}
  (hx : x = 1) (hy : y = 1) (hz : z = 2)
  (hu : u = 1) (hv : v = 2) (hw : w = 2)
  : ({{x}, {x, y}, {x, y, z}} : Set (Set ℕ)) = {{u}, {u, v}, {u, v, w}}
  ∧ y ≠ v := by
  apply And.intro
  · rw [hx, hy, hz, hu, hv, hw]
    simp
  · rw [hy, hv]
    simp only

/-- #### Exercise 3.2a

Show that `A × (B ∪ C) = (A × B) ∪ (A × C)`.
-/
theorem exercise_3_2a {A : Set α} {B C : Set β}
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

/-- #### Exercise 3.2b

Show that if `A × B = A × C` and `A ≠ ∅`, then `B = C`.
-/
theorem exercise_3_2b {A : Set α} {B C : Set β}
  (h : Set.prod A B = Set.prod A C) (hA : Set.Nonempty A)
  : B = C := by
  by_cases hB : Set.Nonempty B
  · rw [Set.Subset.antisymm_iff]
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

/-- #### Exercise 3.3

Show that `A × ⋃ 𝓑 = ⋃ {A × X | X ∈ 𝓑}`.
-/
theorem exercise_3_3 {A : Set (Set α)} {𝓑 : Set (Set β)}
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

/-- #### Exercise 3.5a

Assume that `A` and `B` are given sets, and show that there exists a set `C`
such that for any `y`,
```
y ∈ C ↔ y = {x} × B for some x in A.
```
In other words, show that `{{x} × B | x ∈ A}` is a set.
-/
theorem exercise_3_5a {A : Set α} {B : Set β}
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

/-- #### Exercise 3.5b

With `A`, `B`, and `C` as above, show that `A × B = ∪ C`.
-/
theorem exercise_3_5b {A : Set α} (B : Set β)
  : Set.prod A B = ⋃₀ {Set.prod ({x} : Set α) B | x ∈ A} := by
  rw [Set.Subset.antisymm_iff]
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

/-- #### Theorem 3D

If `⟨x, y⟩ ∈ A`, then `x` and `y` belong to `⋃ ⋃ A`.
-/
theorem theorem_3d {A : Set (Set (Set α))} (h : OrderedPair x y ∈ A)
  : x ∈ ⋃₀ (⋃₀ A) ∧ y ∈ ⋃₀ (⋃₀ A) := by
  have hp := Chapter_2.exercise_2_3 (OrderedPair x y) h
  unfold OrderedPair at hp  
  have hq : {x, y} ∈ ⋃₀ A := hp (by simp)
  have : {x, y} ⊆ ⋃₀ ⋃₀ A := Chapter_2.exercise_2_3 {x, y} hq
  exact ⟨this (by simp), this (by simp)⟩

section Relation

open Set.Relation

/-- #### Exercise 3.6

Show that a set `A` is a relation **iff** `A ⊆ dom A × ran A`.
-/
theorem exercise_3_6 {A : Set.HRelation α β}
  : A ⊆ Set.prod (dom A) (ran A) := by
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

/-- #### Exercise 3.7

Show that if `R` is a relation, then `fld R = ⋃ ⋃ R`.
-/
theorem exercise_3_7 {R : Set.Relation α}
  : R.fld = ⋃₀ ⋃₀ R.toOrderedPairs := by
  let img := R.toOrderedPairs
  rw [Set.Subset.antisymm_iff]
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
      have : {x} ∈ ⋃₀ img := Chapter_2.exercise_2_3 {{x}, {x, y}} hm (by simp)
      exact (Chapter_2.exercise_2_3 {x} this) (show x ∈ {x} by rfl)
    · intro hr
      unfold Set.Relation.ran Prod.snd at hr
      simp only [Set.mem_image, Prod.exists, exists_eq_right] at hr
      have ⟨t, ht⟩ := hr
      have hm : OrderedPair t x ∈ Set.image (fun p => OrderedPair p.1 p.2) R := by
        simp only [Set.mem_image, Prod.exists]
        exact ⟨t, ⟨x, ⟨ht, rfl⟩⟩⟩
      unfold OrderedPair at hm
      have : {t, x} ∈ ⋃₀ img := Chapter_2.exercise_2_3 {{t}, {t, x}} hm
        (show {t, x} ∈ {{t}, {t, x}} by simp)
      exact Chapter_2.exercise_2_3 {t, x} this (show x ∈ {t, x} by simp)

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
      have hz : R ⊆ Set.prod (dom R) (ran R) := exercise_3_6
      have : (x, y) ∈ Set.prod (dom R) (ran R) := hz p
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

/-- #### Exercise 3.8 (i)

Show that for any set `𝓐`:
```
dom ⋃ A = ⋃ { dom R | R ∈ 𝓐 }
```
-/
theorem exercise_3_8_i {A : Set (Set.HRelation α β)}
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

/-- #### Exercise 3.8 (ii)

Show that for any set `𝓐`:
```
ran ⋃ A = ⋃ { ran R | R ∈ 𝓐 }
```
-/
theorem exercise_3_8_ii {A : Set (Set.HRelation α β)}
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

/-- #### Exercise 3.9 (i)

Discuss the result of replacing the union operation by the intersection
operation in the preceding problem.
```
dom ⋃ A = ⋃ { dom R | R ∈ 𝓐 }
```
-/
theorem exercise_3_9_i {A : Set (Set.HRelation α β)}
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

/-- #### Exercise 3.9 (ii)

Discuss the result of replacing the union operation by the intersection
operation in the preceding problem.
```
ran ⋃ A = ⋃ { ran R | R ∈ 𝓐 }
```
-/
theorem exercise_3_9_ii {A : Set (Set.HRelation α β)}
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

/-- #### Theorem 3G (i)

Assume that `F` is a one-to-one function. If `x ∈ dom F`, then `F⁻¹(F(x)) = x`.
-/
theorem theorem_3g_i {F : Set.HRelation α β}
  (hF : isOneToOne F) (hx : x ∈ dom F)
  : ∃! y, (x, y) ∈ F ∧ (y, x) ∈ inv F := by
  simp only [mem_self_comm_mem_inv, and_self]
  have ⟨y, hy⟩ := dom_exists hx
  refine ⟨y, hy, ?_⟩
  intro y₁ hy₁
  unfold isOneToOne at hF
  exact (single_valued_eq_unique hF.left hy hy₁).symm

/-- #### Theorem 3G (ii)

Assume that `F` is a one-to-one function. If `y ∈ ran F`, then `F(F⁻¹(y)) = y`.
-/
theorem theorem_3g_ii {F : Set.HRelation α β}
  (hF : isOneToOne F) (hy : y ∈ ran F)
  : ∃! x, (x, y) ∈ F ∧ (y, x) ∈ inv F := by
  simp only [mem_self_comm_mem_inv, and_self]
  have ⟨x, hx⟩ := ran_exists hy
  refine ⟨x, hx, ?_⟩
  intro x₁ hx₁
  unfold isOneToOne at hF
  exact (single_rooted_eq_unique hF.right hx hx₁).symm

/-- #### Theorem 3H

Assume that `F` and `G` are functions. Then
```
dom (F ∘ G) = {x ∈ dom G | G(x) ∈ dom F}.
```
-/
theorem theorem_3h_dom {F : Set.HRelation β γ} {G : Set.HRelation α β}
  (_ : isSingleValued F) (hG : isSingleValued G)
  : dom (comp F G) = {x ∈ dom G | ∃! y, (x, y) ∈ G ∧ y ∈ dom F} := by
  let rhs := {x ∈ dom G | ∃! y, (x, y) ∈ G ∧ y ∈ dom F }
  rw [Set.Subset.antisymm_iff]
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

/-- #### Theorem 3J (a)

Assume that `F : A → B`, and that `A` is nonempty. There exists a function
`G : B → A` (a "left inverse") such that `G ∘ F` is the identity function on `A`
**iff** `F` is one-to-one.
-/
theorem theorem_3j_a {F : Set.HRelation α β} {A : Set α} {B : Set β}
  (hF : mapsInto F A B) (hA : Set.Nonempty A)
  : (∃ G : Set.HRelation β α,
      isSingleValued G ∧ mapsInto G B A ∧
        (comp G F = { p | p.1 ∈ A ∧ p.1 = p.2 })) ↔ isOneToOne F := by
  apply Iff.intro
  · intro ⟨G, hG⟩
    refine ⟨hF.left, ?_⟩
    intro y hy
    have ⟨x₁, hx₁⟩ := ran_exists hy
    refine ⟨x₁, ⟨mem_pair_imp_fst_mem_dom hx₁, hx₁⟩, ?_⟩
    intro x₂ hx₂
    sorry
  · sorry

/-- #### Theorem 3J (b)

Assume that `F : A → B`, and that `A` is nonempty. There exists a function
`H : B → A` (a "right inverse") such that `F ∘ H` is the identity function on
`B` **iff** `F` maps `A` onto `B`.
-/
theorem theorem_3j_b {F : Set.HRelation α β} {A : Set α} {B : Set β}
  (hF : mapsInto F A B) (hA : Set.Nonempty A)
  : (∃ H : Set.HRelation β α,
      isSingleValued H ∧ mapsInto H B A ∧
        (comp F H = { p | p.1 ∈ B ∧ p.1 = p.2 })) ↔ mapsOnto F A B := by
  sorry

/-- #### Theorem 3K (a)

The following hold for any sets. (`F` need not be a function.)
The image of a union is the union of the images:
```
F⟦⋃ 𝓐⟧ = ⋃ {F⟦A⟧ | A ∈ 𝓐}
```
-/
theorem theorem_3k_a {F : Set.HRelation α β} {𝓐 : Set (Set α)}
  : image F (⋃₀ 𝓐) = ⋃₀ { image F A | A ∈ 𝓐 } := by
  rw [Set.Subset.antisymm_iff]
  apply And.intro
  · show ∀ v, v ∈ image F (⋃₀ 𝓐) → v ∈ ⋃₀ { image F A | A ∈ 𝓐 }
    intro v hv
    unfold image at hv
    simp only [Set.mem_sUnion, Set.mem_setOf_eq] at hv
    have ⟨u, hu⟩ := hv
    have ⟨A, hA⟩ := hu.left
    simp only [Set.mem_sUnion, Set.mem_setOf_eq, exists_exists_and_eq_and]
    refine ⟨A, hA.left, ?_⟩
    show v ∈ image F A
    unfold image
    simp only [Set.mem_setOf_eq]
    exact ⟨u, hA.right, hu.right⟩
  · show ∀ v, v ∈ ⋃₀ {x | ∃ A, A ∈ 𝓐 ∧ image F A = x} → v ∈ image F (⋃₀ 𝓐)
    intro v hv
    simp only [Set.mem_sUnion, Set.mem_setOf_eq, exists_exists_and_eq_and] at hv
    have ⟨A, hA⟩ := hv
    unfold image at hA
    simp only [Set.mem_setOf_eq] at hA
    have ⟨u, hu⟩ := hA.right
    unfold image
    simp only [Set.mem_sUnion, Set.mem_setOf_eq]
    exact ⟨u, ⟨A, hA.left, hu.left⟩, hu.right⟩

/-! #### Theorem 3K (b)

The following hold for any sets. (`F` need not be a function.)
The image of an intersection is included in the intersection of the images:
```
F⟦⋂ 𝓐⟧ ⊆ ⋂ {F⟦A⟧ | A ∈ 𝓐}
```
Equality holds if `F` is single-rooted.
-/

theorem theorem_3k_b_i {F : Set.HRelation α β} {𝓐 : Set (Set α)}
  : image F (⋂₀ 𝓐) ⊆ ⋂₀ { image F A | A ∈ 𝓐} := by
  show ∀ v, v ∈ image F (⋂₀ 𝓐) → v ∈ ⋂₀ { image F A | A ∈ 𝓐}
  intro v hv
  unfold image at hv
  simp only [Set.mem_sInter, Set.mem_setOf_eq] at hv
  have ⟨u, hu⟩ := hv
  simp only [
    Set.mem_sInter,
    Set.mem_setOf_eq,
    forall_exists_index,
    and_imp,
    forall_apply_eq_imp_iff₂
  ]
  intro A hA
  unfold image
  simp only [Set.mem_setOf_eq]
  exact ⟨u, hu.left A hA, hu.right⟩

theorem theorem_3k_b_ii {F : Set.HRelation α β} {𝓐 : Set (Set α)}
  (hF : isSingleRooted F) (h𝓐 : Set.Nonempty 𝓐)
  : image F (⋂₀ 𝓐) = ⋂₀ { image F A | A ∈ 𝓐} := by
  rw [Set.Subset.antisymm_iff]
  refine ⟨theorem_3k_b_i, ?_⟩
  show ∀ v, v ∈ ⋂₀ {x | ∃ A, A ∈ 𝓐 ∧ image F A = x} → v ∈ image F (⋂₀ 𝓐)
  intro v hv
  simp only [
    Set.mem_sInter,
    Set.mem_setOf_eq,
    forall_exists_index,
    and_imp,
    forall_apply_eq_imp_iff₂
  ] at hv
  unfold image at hv
  simp only [Set.mem_setOf_eq] at hv
  have ⟨u, hu⟩ : ∃ u, (∀ (a : Set α), a ∈ 𝓐 → u ∈ a) ∧ (u, v) ∈ F := by
    have ⟨A, hA⟩ := h𝓐
    have ⟨_, ⟨_, hv'⟩⟩ := hv A hA
    have ⟨u, hu⟩ := hF v (mem_pair_imp_snd_mem_ran hv')
    simp only [and_imp] at hu
    refine ⟨u, ?_, hu.left.right⟩
    intro a ha
    have ⟨u₁, hu₁⟩ := hv a ha
    have := hu.right u₁ (mem_pair_imp_fst_mem_dom hu₁.right) hu₁.right
    rw [← this]
    exact hu₁.left
  unfold image
  simp only [Set.mem_sInter, Set.mem_setOf_eq]
  exact ⟨u, hu⟩

/-! #### Theorem 3K (c)

The following hold for any sets. (`F` need not be a function.)
The image of a difference includes the difference of the images:
```
F⟦A⟧ - F⟦B⟧ ⊆ F⟦A - B⟧.
```
Equality holds if `F` is single-rooted.
-/

theorem theorem_3k_c_i {F : Set.HRelation α β} {A B : Set α}
  : image F A \ image F B ⊆ image F (A \ B) := by
  show ∀ v, v ∈ image F A \ image F B → v ∈ image F (A \ B)
  intro v hv
  have hv' : v ∈ image F A ∧ v ∉ image F B := hv
  conv at hv' => arg 1; unfold image; simp only [Set.mem_setOf_eq, eq_iff_iff]
  have ⟨u, hu⟩ := hv'.left
  have hw : ∀ w ∈ B, (w, v) ∉ F := by
    intro w hw nw
    have nv := hv'.right
    unfold image at nv
    simp only [Set.mem_setOf_eq, not_exists, not_and] at nv
    exact absurd nw (nv w hw)
  have hu' : u ∉ B := by
    by_contra nu
    exact absurd hu.right (hw u nu)
  unfold image
  simp only [Set.mem_diff, Set.mem_setOf_eq]
  exact ⟨u, ⟨hu.left, hu'⟩, hu.right⟩

theorem theorem_3k_c_ii {F : Set.HRelation α β} {A B : Set α}
  (hF : isSingleRooted F)
  : image F A \ image F B = image F (A \ B) := by
  rw [Set.Subset.antisymm_iff]
  refine ⟨theorem_3k_c_i, ?_⟩
  show ∀ v, v ∈ image F (A \ B) → v ∈ image F A \ image F B
  intro v hv
  unfold image at hv
  simp only [Set.mem_diff, Set.mem_setOf_eq] at hv
  have ⟨u, hu⟩ := hv
  have hv₁ : v ∈ image F A := by
    unfold image
    simp only [Set.mem_setOf_eq]
    exact ⟨u, hu.left.left, hu.right⟩
  have hv₂ : v ∉ image F B := by
    intro nv
    unfold image at nv
    simp only [Set.mem_setOf_eq] at nv
    have ⟨u₁, hu₁⟩ := nv
    have := single_rooted_eq_unique hF hu.right hu₁.right
    rw [← this] at hu₁
    exact absurd hu₁.left hu.left.right
  exact ⟨hv₁, hv₂⟩

/-! #### Corollary 3L

For any function `G` and sets `A`, `B`, and `𝓐`:

```
G⁻¹⟦⋃ 𝓐⟧ = ⋃ {G⁻¹⟦A⟧ | A ∈ 𝓐},
G⁻¹⟦𝓐⟧ = ⋂ {G⁻¹⟦A⟧ | A ∈ 𝓐} for 𝓐 ≠ ∅,
G⁻¹⟦A - B⟧ = G⁻¹⟦A⟧ - G⁻¹⟦B⟧.
```
-/

theorem corollary_3l_i {G : Set.HRelation β α} {𝓐 : Set (Set α)}
  : image (inv G) (⋃₀ 𝓐) = ⋃₀ {image (inv G) A | A ∈ 𝓐} := theorem_3k_a

theorem corollary_3l_ii {G : Set.HRelation β α} {𝓐 : Set (Set α)}
  (hG : isSingleValued G) (h𝓐 : Set.Nonempty 𝓐)
  : image (inv G) (⋂₀ 𝓐) = ⋂₀ {image (inv G) A | A ∈ 𝓐} := by
  have hG' : isSingleRooted (inv G) :=
    single_valued_self_iff_single_rooted_inv.mp hG
  exact theorem_3k_b_ii hG' h𝓐

theorem corollary_3l_iii {G : Set.HRelation β α} {A B : Set α}
  (hG : isSingleValued G)
  : image (inv G) (A \ B) = image (inv G) A \ image (inv G) B := by
  have hG' : isSingleRooted (inv G) :=
    single_valued_self_iff_single_rooted_inv.mp hG
  exact (theorem_3k_c_ii hG').symm

/-- #### Exercise 3.12

Assume that `f` and `g` are functions and show that
```
f ⊆ g ↔ dom f ⊆ dom g ∧ (∀ x ∈ dom f) f(x) = g(x).
```
-/
theorem exercise_3_12 {f g : Set.HRelation α β}
  (hf : isSingleValued f) (_ : isSingleValued g)
  : f ⊆ g ↔ dom f ⊆ dom g ∧
      (∀ x ∈ dom f, ∃! y : β, (x, y) ∈ f ∧ (x, y) ∈ g) := by
  apply Iff.intro
  · intro h
    apply And.intro
    · show ∀ x, x ∈ dom f → x ∈ dom g
      intro x hx
      have ⟨y, hy⟩ := dom_exists hx
      exact mem_pair_imp_fst_mem_dom (h hy)
    · intro x hx
      have ⟨y, hy⟩ := dom_exists hx
      refine ⟨y, ⟨hy, h hy⟩, ?_⟩
      intro y₁ hy₁
      exact single_valued_eq_unique hf hy₁.left hy
  · intro ⟨_, hx⟩
    show ∀ p, p ∈ f → p ∈ g
    intro (x, y) hp
    have ⟨y₁, hy₁⟩ := hx x (mem_pair_imp_fst_mem_dom hp)
    rw [single_valued_eq_unique hf hp hy₁.left.left]
    exact hy₁.left.right

/-- #### Exercise 3.13

Assume that `f` and `g` are functions with `f ⊆ g` and `dom g ⊆ dom f`. Show
that `f = g`.
-/
theorem exercise_3_13 {f g : Set.HRelation α β}
  (hf : isSingleValued f) (hg : isSingleValued g)
  (h : f ⊆ g) (h₁ : dom g ⊆ dom f)
  : f = g := by
  have h₂ := (exercise_3_12 hf hg).mp h
  have hfg := Set.Subset.antisymm_iff.mpr ⟨h₁, h₂.left⟩
  ext p
  have (a, b) := p
  apply Iff.intro
  · intro hp
    have ⟨x, hx⟩ := h₂.right a (mem_pair_imp_fst_mem_dom hp)
    rw [single_valued_eq_unique hf hp hx.left.left]
    exact hx.left.right
  · intro hp
    rw [← hfg] at h₂
    have ⟨x, hx⟩ := h₂.right a (mem_pair_imp_fst_mem_dom hp)
    rw [single_valued_eq_unique hg hp hx.left.right]
    exact hx.left.left

/-- #### Exercise 3.14 (a)

Assume that `f` and `g` are functions. Show that `f ∩ g` is a function.
-/
theorem exercise_3_14_a {f g : Set.HRelation α β}
  (hf : isSingleValued f) (_ : isSingleValued g)
  : isSingleValued (f ∩ g) :=
  single_valued_subset hf (Set.inter_subset_left f g)

/-- #### Exercise 3.14 (b)

Assume that `f` and `g` are functions. Show that `f ∪ g` is a function **iff**
`f(x) = g(x)` for every `x` in `(dom f) ∩ (dom g)`.
-/
theorem exercise_3_14_b {f g : Set.HRelation α β}
  (hf : isSingleValued f) (hg : isSingleValued g)
  : isSingleValued (f ∪ g) ↔
      (∀ x ∈ dom f ∩ dom g, ∃! y, (x, y) ∈ f ∧ (x, y) ∈ g) := by
  apply Iff.intro
  · intro h x hx
    have ⟨y₁, hy₁⟩ := hf x hx.left
    have ⟨y₂, hy₂⟩ := hg x hx.right
    have : y₁ = y₂ := single_valued_eq_unique h
      (Or.inl hy₁.left.right)
      (Or.inr hy₂.left.right)
    rw [← this] at hy₂
    refine ⟨y₁, ⟨hy₁.left.right, hy₂.left.right⟩, ?_⟩
    intro y₃ hfy₃
    exact single_valued_eq_unique hf hfy₃.left hy₁.left.right
  · intro h x hx
    by_cases hfx : x ∈ dom f <;>
    by_cases hgx : x ∈ dom g
    · -- `x ∈ dom f ∧ x ∈ dom g`
      have ⟨y₁, hy₁⟩ := hf x hfx
      have ⟨y₂, hy₂⟩ := hg x hgx
      refine ⟨y₁, ⟨?_, Or.inl hy₁.left.right⟩, ?_⟩
      · unfold ran
        simp only [Set.mem_image, Set.mem_union, Prod.exists, exists_eq_right]
        exact ⟨x, Or.inl hy₁.left.right⟩
      · intro y₃ hy₃
        apply Or.elim hy₃.right
        · intro hxy
          exact single_valued_eq_unique hf hxy hy₁.left.right
        · refine fun hxy => single_valued_eq_unique hg hxy ?_
          have : y₁ = y₂ := by
            have ⟨z, ⟨hz, _⟩⟩ := h x ⟨hfx, hgx⟩
            rw [
              single_valued_eq_unique hf hy₁.left.right hz.left,
              single_valued_eq_unique hg hy₂.left.right hz.right
            ]
          rw [this]
          exact hy₂.left.right
    · -- `x ∈ dom f ∧ x ∉ dom g`
      have ⟨y, hy⟩ := dom_exists hfx
      have hxy : (x, y) ∈ f ∪ g := (Set.subset_union_left f g) hy
      refine ⟨y, ⟨mem_pair_imp_snd_mem_ran hxy, hxy⟩, ?_⟩
      intro y₁ hy₁
      apply Or.elim hy₁.right
      · intro hx'
        exact single_valued_eq_unique hf hx' hy
      · intro hx'
        exact absurd (mem_pair_imp_fst_mem_dom hx') hgx
    · -- `x ∉ dom f ∧ x ∈ dom g`
      have ⟨y, hy⟩ := dom_exists hgx
      have hxy : (x, y) ∈ f ∪ g := (Set.subset_union_right f g) hy
      refine ⟨y, ⟨mem_pair_imp_snd_mem_ran hxy, hxy⟩, ?_⟩
      intro y₁ hy₁
      apply Or.elim hy₁.right
      · intro hx'
        exact absurd (mem_pair_imp_fst_mem_dom hx') hfx
      · intro hx'
        exact single_valued_eq_unique hg hx' hy
    · -- `x ∉ dom f ∧ x ∉ dom g`
      exfalso
      unfold dom at hx
      simp only [
        Set.mem_image,
        Set.mem_union,
        Prod.exists,
        exists_and_right,
        exists_eq_right
      ] at hx
      have ⟨_, hy⟩ := hx
      apply Or.elim hy
      · intro hz
        exact absurd (mem_pair_imp_fst_mem_dom hz) hfx
      · intro hz
        exact absurd (mem_pair_imp_fst_mem_dom hz) hgx

/-- #### Exercise 3.15

Let `𝓐` be a set of functions such that for any `f` and `g` in `𝓐`, either
`f ⊆ g` or `g ⊆ f`. Show that `⋃ 𝓐` is a function.
-/
theorem exercise_3_15 {𝓐 : Set (Set.HRelation α β)}
  (h𝓐 : ∀ F ∈ 𝓐, isSingleValued F)
  (h : ∀ F, ∀ G, F ∈ 𝓐 → G ∈ 𝓐 → F ⊆ G ∨ G ⊆ F)
  : isSingleValued (⋃₀ 𝓐) := by
  intro x hx
  have ⟨y₁, hy₁⟩ := dom_exists hx
  refine ⟨y₁, ⟨mem_pair_imp_snd_mem_ran hy₁, hy₁⟩, ?_⟩
  intro y₂ hy₂
  have ⟨f, hf⟩ : ∃ f : Set.HRelation α β, f ∈ 𝓐 ∧ (x, y₁) ∈ f := hy₁
  have ⟨g, hg⟩ : ∃ g : Set.HRelation α β, g ∈ 𝓐 ∧ (x, y₂) ∈ g := hy₂.right
  apply Or.elim (h f g hf.left hg.left)
  · intro hf'
    have := hf' hf.right
    exact single_valued_eq_unique (h𝓐 g hg.left) hg.right this
  · intro hg'
    have := hg' hg.right
    exact single_valued_eq_unique (h𝓐 f hf.left) this hf.right

/-! #### Exercise 3.17

Show that the composition of two single-rooted sets is again single-rooted.
Conclude that the composition of two one-to-one functions is again one-to-one.
-/

theorem exercise_3_17_i {F : Set.HRelation β γ} {G : Set.HRelation α β}
  (hF : isSingleRooted F) (hG : isSingleRooted G)
  : isSingleRooted (comp F G):= by
  intro v hv
  
  have ⟨u₁, hu₁⟩ := ran_exists hv
  have hu₁' := hu₁
  unfold comp at hu₁'
  simp only [Set.mem_setOf_eq] at hu₁'
  have ⟨t₁, ht₁⟩ := hu₁'
  unfold ExistsUnique
  refine ⟨u₁, ⟨mem_pair_imp_fst_mem_dom hu₁, hu₁⟩, ?_⟩
  
  intro u₂ hu₂
  have hu₂' := hu₂
  unfold comp at hu₂'
  simp only [Set.mem_setOf_eq] at hu₂'
  have ⟨_, ⟨t₂, ht₂⟩⟩ := hu₂'
  
  have ht : t₁ = t₂ := single_rooted_eq_unique hF ht₁.right ht₂.right
  rw [ht] at ht₁
  exact single_rooted_eq_unique hG ht₂.left ht₁.left

theorem exercise_3_17_ii {F : Set.HRelation β γ} {G : Set.HRelation α β}
  (hF : isOneToOne F) (hG : isOneToOne G)
  : isOneToOne (comp F G) := And.intro
      (single_valued_comp_is_single_valued hF.left hG.left)
      (exercise_3_17_i hF.right hG.right)

/-! #### Exercise 3.18

Let `R` be the set
```
{⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 3⟩, ⟨1, 2⟩, ⟨1, 3⟩, ⟨2, 3⟩}
```
Evaluate the following: `R ∘ R`, `R ↾ {1}`, `R⁻¹ ↾ {1}`, `R⟦{1}⟧`, and
`R⁻¹⟦{1}⟧`.
-/

section Exercise_3_18

variable {R : Set.Relation ℕ}
variable (hR : R = {(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)})

theorem exercise_3_18_i
  : comp R R = {(0, 2), (0, 3), (1, 3)} := by
  rw [hR]
  unfold comp
  simp only [Set.mem_singleton_iff, Set.mem_insert_iff, or_self, Prod.mk.injEq]
  ext x
  have (a, b) := x
  apply Iff.intro
  · simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Set.mem_insert_iff]
    intro ⟨t, ht₁, ht₂⟩
    casesm* _ ∨ _
    all_goals case _ hl hr => first
      | {rw [hl.right] at hr; simp at hr}
      | {rw [hl.left] at hr; simp at hr}
      | {rw [hl.left, hr.right]; simp}
  · simp only [
      Set.mem_singleton_iff,
      Set.mem_insert_iff,
      Prod.mk.injEq,
      Set.mem_setOf_eq
    ]
    intro h
    casesm* _ ∨ _
    · case _ h =>
        refine ⟨1, Or.inl ⟨h.left, rfl⟩, ?_⟩
        iterate 3 right
        left
        exact ⟨rfl, h.right⟩
    · case _ h =>
        refine ⟨1, Or.inl ⟨h.left, rfl⟩, ?_⟩
        iterate 4 right
        left
        exact ⟨rfl, h.right⟩
    · case _ h =>
        refine ⟨2, ?_, ?_⟩
        · iterate 3 right
          left
          exact ⟨h.left, rfl⟩
        · iterate 5 right
          exact ⟨rfl, h.right⟩

theorem exercise_3_18_ii
  : restriction R {1} = {(1, 2), (1, 3)} := by
  rw [hR]
  unfold restriction
  ext p
  have (a, b) := p
  simp only [
    Set.mem_singleton_iff,
    Set.mem_insert_iff,
    Set.mem_setOf_eq,
    or_self
  ]
  apply Iff.intro
  · intro ⟨hp, ha⟩
    rw [ha]
    simp only [Prod.mk.injEq, true_and]
    casesm* _ ∨ _
    all_goals case _ h => first
      | {rw [ha] at h; simp at h}
      | {simp only [Prod.mk.injEq] at h; left; exact h.right}
      | {simp only [Prod.mk.injEq] at h; right; exact h.right}
  · intro h
    apply Or.elim h
    · intro hab
      simp only [Prod.mk.injEq] at hab
      refine ⟨?_, hab.left⟩
      iterate 3 right
      left
      rw [hab.left, hab.right]
    · intro hab
      simp only [Prod.mk.injEq] at hab
      refine ⟨?_, hab.left⟩
      iterate 4 right
      left
      rw [hab.left, hab.right]

theorem exercise_3_18_iii
  : restriction (inv R) {1} = {(1, 0)} := by
  rw [hR]
  unfold inv restriction
  ext p
  have (a, b) := p
  simp only [
    Set.mem_singleton_iff,
    Set.mem_insert_iff,
    or_self,
    exists_eq_or_imp,
    exists_eq_left,
    Set.mem_setOf_eq,
    Prod.mk.injEq
  ]
  apply Iff.intro
  · intro ⟨hb, ha⟩
    casesm* _ ∨ _
    all_goals case _ hr => first
      | exact ⟨ha, hr.right.symm⟩
      | rw [ha] at hr; simp at hr
  · intro ⟨ha, hb⟩
    rw [ha, hb]
    simp

theorem exercise_3_18_iv
  : image R {1} = {2, 3} := by
  rw [hR]
  unfold image
  ext y
  simp

theorem exercise_3_18_v
  : image (inv R) {1} = {0} := by
  rw [hR]
  unfold inv image
  ext y
  simp

end Exercise_3_18

/-! #### Exercise 3.19

Let
```
A = {⟨∅, {∅, {∅}}⟩, ⟨{∅}, ∅⟩}.
```
Evaluate each of the following: `A(∅)`, `A⟦∅⟧`, `A⟦{∅}⟧`, `A⟦{∅, {∅}}⟧`,
`A⁻¹`, `A ∘ A`, `A ↾ ∅`, `A ↾ {∅, {∅}}`, `⋃ ⋃ A`.
-/

section Exercise_3_19

variable {A : Set.Relation (Set (Set (Set α)))}
variable (hA : A = {(∅, {∅, {∅}}), ({∅}, ∅)})

theorem exercise_3_19_i
  : (∅, {∅, {∅}}) ∈ A := by
  rw [hA]
  simp

theorem exercise_3_19_ii
  : image A ∅ = ∅ := by
  unfold image
  simp

theorem exercise_3_19_iii
  : image A {∅} = {{∅, {∅}}} := by
  unfold image
  rw [hA]
  ext x
  simp only [
    Set.mem_singleton_iff,
    Prod.mk.injEq,
    Set.mem_insert_iff,
    exists_eq_left,
    true_and
  ]
  apply Iff.intro
  · intro hx
    simp at hx
    apply Or.elim hx
    · simp
    · intro ⟨h, _⟩
      exfalso
      rw [Set.ext_iff] at h
      have := h ∅
      simp at this
  · intro hx
    rw [hx]
    simp

theorem exercise_3_19_iv
  : image A {∅, {∅}} = {{∅, {∅}}, ∅} := by
  unfold image
  rw [hA]
  ext x
  simp only [
    Set.mem_singleton_iff,
    Set.mem_insert_iff,
    Prod.mk.injEq,
    exists_eq_or_imp,
    true_and,
    exists_eq_left,
    Set.singleton_ne_empty,
    false_and,
    false_or,
    Set.mem_setOf_eq
  ]
  apply Iff.intro
  · intro h
    apply Or.elim h
    · intro hx₁
      apply Or.elim hx₁
      · intro hx₂; left ; exact hx₂
      · intro hx₂; right; exact hx₂.right
    · intro hx₂
      right
      exact hx₂
  · intro h
    apply Or.elim h
    · intro hx₁; iterate 2 left
      exact hx₁
    · intro hx₁; right; exact hx₁

theorem exercise_3_19_v
  : inv A = {({∅, {∅}}, ∅), (∅, {∅})} := by
  unfold inv
  rw [hA]
  ext x
  simp only [
    Set.mem_singleton_iff,
    Prod.mk.injEq,
    Set.mem_insert_iff,
    exists_eq_or_imp,
    exists_eq_left,
    Set.mem_setOf_eq
  ]
  apply Iff.intro
  · intro hx
    apply Or.elim hx
    · intro hx₁; left ; rw [← hx₁]
    · intro hx₁; right; rw [← hx₁]
  · intro hx
    apply Or.elim hx
    · intro hx₁; left ; rw [← hx₁]
    · intro hx₁; right; rw [← hx₁]

theorem exercise_3_19_vi
  : comp A A = {({∅}, {∅, {∅}})} := by
  unfold comp
  rw [hA]
  ext x
  have (a, b) := x
  simp only [
    Set.mem_singleton_iff, Prod.mk.injEq, Set.mem_insert_iff, Set.mem_setOf_eq
  ]
  apply Iff.intro
  · intro ⟨t, ht₁, ht₂⟩
    casesm* _ ∨ _
    all_goals case _ hl hr => first
      | {
          rw [hl.right] at hr
          have := hr.left
          rw [Set.ext_iff] at this
          simp at this
        }
      | exact ⟨hl.left, hr.right⟩
  · intro ⟨ha, hb⟩
    refine ⟨∅, ?_, ?_⟩
    · right; rw [ha]; simp
    · left ; rw [hb]; simp

theorem exercise_3_19_vii
  : restriction A ∅ = ∅ := by
  unfold restriction
  rw [hA]
  simp

theorem exercise_3_19_viii
  : restriction A {∅} = {(∅, {∅, {∅}})} := by
  unfold restriction
  rw [hA]
  ext x
  have (a, b) := x
  simp only [
    Set.mem_singleton_iff, Prod.mk.injEq, Set.mem_insert_iff, Set.mem_setOf_eq
  ]
  apply Iff.intro
  · intro ⟨h, ha⟩
    apply Or.elim h
    · simp
    · intro ⟨ha', _⟩
      exfalso
      rw [ha', Set.ext_iff] at ha
      simp at ha
  · intro ⟨ha, hb⟩
    rw [ha, hb]
    simp

theorem exercise_3_19_ix
  : restriction A {∅, {∅}} = A := by
  unfold restriction
  rw [hA]
  ext x
  have (a, b) := x
  simp only [
    Set.mem_singleton_iff,
    Prod.mk.injEq,
    Set.mem_insert_iff,
    Set.mem_setOf_eq
  ]
  apply Iff.intro
  · intro ⟨h₁, h₂⟩
    casesm* _ ∨ _
    · case _ hl _ => left ; exact hl
    · case _ hl _ => left ; exact hl
    · case _ hl _ => right; exact hl
    · case _ hl _ => right; exact hl
  · intro h₁
    apply Or.elim h₁ <;>
    · intro ⟨ha, hb⟩
      rw [ha, hb]
      simp

theorem exercise_3_19_x
  : ⋃₀ ⋃₀ A.toOrderedPairs = {∅, {∅}, {∅, {∅}}} := by
  unfold toOrderedPairs OrderedPair Set.sUnion sSup Set.instSupSetSet
  rw [hA]
  ext x
  simp only [
    Set.mem_singleton_iff,
    Prod.mk.injEq,
    Set.mem_image,
    Set.mem_insert_iff,
    exists_eq_or_imp,
    exists_eq_left,
    Set.singleton_ne_empty,
    Set.mem_setOf_eq
  ]
  apply Iff.intro
  · intro ⟨a, ⟨t, ht₁, ht₂⟩, hx⟩
    apply Or.elim ht₁
    · intro ht
      rw [← ht] at ht₂
      simp only [Set.mem_singleton_iff, Set.mem_insert_iff] at ht₂ 
      apply Or.elim ht₂
      · intro ha
        rw [ha] at hx
        simp only [Set.mem_singleton_iff] at hx
        left
        exact hx
      · intro ha
        rw [ha] at hx
        simp at hx
        apply Or.elim hx <;>
        · intro hx'; rw [hx']; simp
    · intro ht
      rw [← ht] at ht₂
      simp only [
        Set.mem_singleton_iff, Set.singleton_ne_empty, Set.mem_insert_iff
      ] at ht₂
      apply Or.elim ht₂
      · intro ha
        rw [ha] at hx
        simp only [Set.mem_singleton_iff] at hx
        rw [hx]
        simp
      · intro ha
        rw [ha] at hx
        simp only [
          Set.mem_singleton_iff, Set.singleton_ne_empty, Set.mem_insert_iff
        ] at hx
        apply Or.elim hx <;>
        · intro hx'; rw [hx']; simp
  · intro hx
    apply Or.elim hx
    · intro hx₁
      rw [hx₁]
      refine ⟨{{∅}, ∅}, ⟨{{{∅}}, {{∅}, ∅}}, ?_⟩, ?_⟩ <;> simp
    · intro hx₁
      apply Or.elim hx₁
      · intro hx₂
        rw [hx₂]
        refine ⟨{{∅}, ∅}, ⟨{{{∅}}, {{∅}, ∅}}, ?_⟩, ?_⟩ <;> simp
      · intro hx₂
        rw [hx₂]
        refine ⟨{∅, {∅, {∅}}}, ⟨{{∅}, {∅, {∅, {∅}}}}, ?_⟩, ?_⟩ <;> simp

end Exercise_3_19

/-- #### Exercise 3.20

Show that `F ↾ A = F ∩ (A × ran F)`.
-/
theorem exercise_3_20 {F : Set.HRelation α β} {A : Set α}
  : restriction F A = F ∩ (Set.prod A (ran F)) := by
  calc restriction F A
    _ = {p | p ∈ F ∧ p.fst ∈ A} := rfl
    _ = {p | p ∈ F ∧ p.fst ∈ A ∧ p.snd ∈ ran F} := by
      ext x
      have (a, b) := x
      simp only [
        Set.mem_setOf_eq, Set.sep_and, Set.mem_inter_iff, iff_self_and, and_imp
      ]
      intro hF _
      exact ⟨hF, mem_pair_imp_snd_mem_ran hF⟩
    _ = {p | p ∈ F} ∩ {p | p.fst ∈ A ∧ p.snd ∈ ran F} := rfl
    _ = F ∩ {p | p.fst ∈ A ∧ p.snd ∈ ran F} := rfl
    _ = F ∩ (Set.prod A (ran F)) := rfl

/-- #### Exercise 3.22 (a)

Show that the following is correct for any sets.
```
A ⊆ B → F⟦A⟧ ⊆ F⟦B⟧
```
-/
theorem exercise_3_22_a {A B : Set α} {F : Set.HRelation α β} (h : A ⊆ B)
  : image F A ⊆ image F B := by
  show ∀ x, x ∈ image F A → x ∈ image F B
  unfold image
  simp only [Set.mem_setOf_eq]
  intro x hx
  have ⟨u, hu⟩ := hx
  have := h hu.left
  exact ⟨u, this, hu.right⟩

/-- #### Exercise 3.22 (b)

Show that the following is correct for any sets.
```
(F ∘ G)⟦A⟧ = F⟦G⟦A⟧⟧
```
-/
theorem exercise_3_22_b {A B : Set α} {F : Set.HRelation α β}
  : image (comp F G) A = image F (image G A) := by
  calc image (comp F G) A
    _ = { v | ∃ u ∈ A, (u, v) ∈ comp F G } := rfl
    _ = { v | ∃ u ∈ A, ∃ a, (u, a) ∈ G ∧ (a, v) ∈ F } := rfl
    _ = { v | ∃ a, ∃ u ∈ A, (u, a) ∈ G ∧ (a, v) ∈ F } := by
      ext p
      simp only [Set.mem_setOf_eq]
      apply Iff.intro
      · intro ⟨u, hu, a, ha⟩
        exact ⟨a, u, hu, ha⟩
      · intro ⟨a, u, hu, ha⟩
        exact ⟨u, hu, a, ha⟩
    _ = { v | ∃ a, (∃ u ∈ A, (u, a) ∈ G) ∧ (a, v) ∈ F } := by
      ext p
      simp only [Set.mem_setOf_eq]
      apply Iff.intro
      · intro ⟨a, u, h⟩
        exact ⟨a, ⟨u, h.left, h.right.left⟩, h.right.right⟩
      · intro ⟨a, ⟨u, hu⟩, ha⟩
        exact ⟨a, u, hu.left, hu.right, ha⟩
    _ = { v | ∃ a ∈ { w | ∃ u ∈ A, (u, w) ∈ G }, (a, v) ∈ F } := rfl
    _ = { v | ∃ a ∈ image G A, (a, v) ∈ F } := rfl
    _ = image F (image G A) := rfl

/-- #### Exercise 3.22 (c)

Show that the following is correct for any sets.
```
Q ↾ (A ∪ B) = (Q ↾ A) ∪ (Q ↾ B)
```
-/
theorem exercise_3_22_c {A B : Set α} {Q : Set.Relation α}
  : restriction Q (A ∪ B) = (restriction Q A) ∪ (restriction Q B) := by
  calc restriction Q (A ∪ B)
    _ = { p | p ∈ Q ∧ p.1 ∈ A ∪ B } := rfl
    _ = { p | p ∈ Q ∧ (p.1 ∈ A ∨ p.1 ∈ B) } := rfl
    _ = { p | (p ∈ Q ∧ p.1 ∈ A) ∨ (p ∈ Q ∧ p.1 ∈ B) } := by
      ext p
      simp only [Set.sep_or, Set.mem_union, Set.mem_setOf_eq]
    _ = { p | p ∈ Q ∧ p.1 ∈ A} ∪ { p | p ∈ Q ∧ p.1 ∈ B } := rfl
    _ = (restriction Q A) ∪ (restriction Q B) := rfl

/-- #### Exercise 3.23 (i)

Let `I` be the identity function on the set `A`. Show that for any sets `B` and
`C`, `B ∘ I = B ↾ A`.
-/
theorem exercise_3_23_i {A : Set α} {B : Set.HRelation α β} {I : Set.Relation α}
  (hI : I = { p | p.1 ∈ A ∧ p.1 = p.2 })
  : comp B I = restriction B A := by
  rw [Set.Subset.antisymm_iff]
  apply And.intro
  · show ∀ p, p ∈ comp B I → p ∈ restriction B A
    intro (x, y) hp
    have ⟨t, ht⟩ := hp
    rw [hI] at ht
    simp only [Set.mem_setOf_eq] at ht
    show (x, y) ∈ B ∧ x ∈ A
    rw [← ht.left.right] at ht
    exact ⟨ht.right, ht.left.left⟩
  · show ∀ p, p ∈ restriction B A → p ∈ comp B I
    unfold restriction comp
    rw [hI]
    simp only [Set.mem_setOf_eq, and_true]
    intro (x, y) hp
    refine ⟨x, ⟨hp.right, rfl⟩, hp.left⟩

/-- #### Exercise 3.23 (ii)

Let `I` be the identity function on the set `A`. Show that for any sets `B` and
`C`, `I⟦C⟧ = A ∩ C`.
-/
theorem exercise_3_23_ii {A C : Set α} {I : Set.Relation α}
  (hI : I = { p | p.1 ∈ A ∧ p.1 = p.2 })
  : image I C = A ∩ C := by
  calc image I C
    _ = { v | ∃ u ∈ C, (u, v) ∈ I } := rfl
    _ = { v | ∃ u ∈ C, u ∈ A ∧ u = v } := by
      ext v
      simp only [Set.mem_setOf_eq]
      apply Iff.intro
      · intro ⟨u, h₁, h₂⟩
        rw [hI] at h₂
        simp only [Set.mem_setOf_eq] at h₂
        exact ⟨u, h₁, h₂⟩
      · intro ⟨u, h₁, h₂⟩
        refine ⟨u, h₁, ?_⟩
        · rw [hI]
          simp only [Set.mem_setOf_eq]
          exact h₂
    _ = { v | v ∈ C ∧ v ∈ A } := by
      ext v
      simp only [Set.mem_setOf_eq, Set.sep_mem_eq, Set.mem_inter_iff]
      apply Iff.intro
      · intro ⟨u, hC, hA, hv⟩
        rw [← hv]
        exact ⟨hC, hA⟩
      · intro ⟨hC, hA⟩
        exact ⟨v, hC, hA, rfl⟩
    _ = C ∩ A := rfl
    _ = A ∩ C := Set.inter_comm C A

/-- #### Exercise 3.24

Show that for a function `F`, `F⁻¹⟦A⟧ = { x ∈ dom F | F(x) ∈ A }`.
-/
theorem exercise_3_24 {F : Set.HRelation α β} {A : Set β}
  (hF : isSingleValued F)
  : image (inv F) A = { x ∈ dom F | ∃! y : β, (x, y) ∈ F ∧ y ∈ A } := by
  calc image (inv F) A
    _ = { x | ∃ y ∈ A, (y, x) ∈ inv F } := rfl
    _ = { x | ∃ y ∈ A, (x, y) ∈ F } := by simp only [mem_self_comm_mem_inv]
    _ = { x | x ∈ dom F ∧ (∃ y : β, (x, y) ∈ F ∧ y ∈ A) } := by
      ext x
      simp only [Set.mem_setOf_eq]
      apply Iff.intro
      · intro ⟨y, hy, hyx⟩
        exact ⟨mem_pair_imp_fst_mem_dom hyx, y, hyx, hy⟩
      · intro ⟨_, y, hxy, hy⟩
        exact ⟨y, hy, hxy⟩
    _ = { x ∈ dom F | ∃ y : β, (x, y) ∈ F ∧ y ∈ A } := rfl
    _ = { x ∈ dom F | ∃! y : β, (x, y) ∈ F ∧ y ∈ A } := by
      ext x
      simp only [Set.mem_setOf_eq, and_congr_right_iff]
      intro _
      apply Iff.intro
      · intro ⟨y, hy⟩
        refine ⟨y, hy, ?_⟩
        intro y₁ hy₁
        exact single_valued_eq_unique hF hy₁.left hy.left
      · intro ⟨y, hy⟩
        exact ⟨y, hy.left⟩

/-- #### Exercise 3.25 (b)

Show that the result of part (a) holds for any function `G`, not necessarily
one-to-one.
-/
theorem exercise_3_25_b {G : Set.HRelation α β} (hG : isSingleValued G)
  : comp G (inv G) = { p | p.1 ∈ ran G ∧ p.1 = p.2 } := by
  ext p
  have (x, y) := p
  apply Iff.intro
  · unfold comp inv
    intro h
    simp only [Prod.exists, Set.mem_setOf_eq, Prod.mk.injEq] at h
    have ⟨t, ⟨a, b, ⟨hab, hb, ha⟩⟩, ht⟩ := h
    simp only [Set.mem_setOf_eq]
    rw [hb, ha] at hab
    exact ⟨mem_pair_imp_snd_mem_ran hab, single_valued_eq_unique hG hab ht⟩
  · intro h
    simp only [Set.mem_setOf_eq] at h
    unfold comp inv
    simp only [Prod.exists, Set.mem_setOf_eq, Prod.mk.injEq]
    have ⟨t, ht⟩ := ran_exists h.left
    exact ⟨t, ⟨t, x, ht, rfl, rfl⟩, by rwa [← h.right]⟩

/-- #### Exercise 3.25 (a)

Assume that `G` is a one-to-one function. Show that `G ∘ G⁻¹` is the identity
function on `ran G`.
-/
theorem exercise_3_25_a {G : Set.HRelation α β} (hG : isOneToOne G)
  : comp G (inv G) = { p | p.1 ∈ ran G ∧ p.1 = p.2 } :=
  exercise_3_25_b hG.left

/-- #### Exercise 3.27

Show that `dom (F ∘ G) = G⁻¹⟦dom F⟧` for any sets `F` and `G`. (`F` and `G` need
not be functions.)
-/
theorem exercise_3_27 {F : Set.HRelation β γ} {G : Set.HRelation α β}
  : dom (comp F G) = image (inv G) (dom F) := by
  rw [Set.Subset.antisymm_iff]
  apply And.intro
  · show ∀ x, x ∈ dom (comp F G) → x ∈ image (inv G) (dom F)
    intro x hx
    have ⟨y, hy⟩ := dom_exists hx
    unfold comp at hy
    simp only [Set.mem_setOf_eq] at hy
    have ⟨t, ht⟩ := hy
    have htF : t ∈ dom F := mem_pair_imp_fst_mem_dom ht.right
    
    unfold image inv
    simp only [Prod.exists, Set.mem_setOf_eq, Prod.mk.injEq]
    exact ⟨t, htF, x, t, ht.left, rfl, rfl⟩

  · show ∀ x, x ∈ image (inv G) (dom F) → x ∈ dom (comp F G)
    intro x hx
    unfold image at hx
    simp only [mem_self_comm_mem_inv, Set.mem_setOf_eq] at hx
    have ⟨u, hu⟩ := hx
    have ⟨t, ht⟩ := dom_exists hu.left

    unfold dom comp
    simp only [
      Set.mem_image,
      Set.mem_setOf_eq,
      Prod.exists,
      exists_and_right,
      exists_eq_right
    ]
    exact ⟨t, u, hu.right, ht⟩

/-- #### Exercise 3.28

Assume that `f` is a one-to-one function from `A` into `B`, and that `G` is the
function with `dom G = 𝒫 A` defined by the equation `G(X) = f⟦X⟧`. Show that `G`
maps `𝒫 A` one-to-one into `𝒫 B`.
-/
theorem exercise_3_28 {A : Set α} {B : Set β}
  {f : Set.HRelation α β} {G : Set.HRelation (Set α) (Set β)}
  (hf : isOneToOne f ∧ mapsInto f A B)
  (hG : G = { p | p.1 ∈ 𝒫 A ∧ p.2 = image f p.1 })
  : isOneToOne G ∧ mapsInto G (𝒫 A) (𝒫 B) := by
  have dG : dom G = 𝒫 A := by
    rw [hG]
    ext p
    unfold dom Prod.fst
    simp

  have hG₁ : isSingleValued G := by
    intro x hx
    have ⟨y, hy⟩ := dom_exists hx
    refine ⟨y, ⟨mem_pair_imp_snd_mem_ran hy, hy⟩, ?_⟩
    intro y₁ hy₁
    rw [hG, Set.mem_setOf_eq] at hy
    conv at hy₁ => rhs; rw [hG, Set.mem_setOf_eq]
    simp only at *
    rw [hy.right, hy₁.right.right]

  apply And.intro
  · show isOneToOne G
    refine ⟨hG₁, ?_⟩
    intro y hy
    have ⟨X₁, hX₁⟩ := ran_exists hy
    refine ⟨X₁, ⟨mem_pair_imp_fst_mem_dom hX₁, hX₁⟩, ?_⟩
    intro X₂ hX₂
    have hX₁' : y = image f X₁ := by
      rw [hG] at hX₁
      simp only [Set.mem_powerset_iff, Set.mem_setOf_eq] at hX₁
      exact hX₁.right
    have hX₂' : y = image f X₂ := by
      have := hX₂.right
      rw [hG] at this
      simp only [Set.mem_powerset_iff, Set.mem_setOf_eq] at this
      exact this.right

    ext t
    apply Iff.intro
    · intro ht
      rw [dG] at hX₂
      simp only [Set.mem_powerset_iff] at hX₂

      have ht' := hX₂.left ht
      rw [← hf.right.right.left] at ht'
      have ⟨ft, hft⟩ := dom_exists ht'
      have hft' : ft ∈ image f X₂ := ⟨t, ht, hft⟩

      rw [← hX₂', hX₁'] at hft'
      have ⟨t₁, ht₁⟩ := hft'
      rw [single_rooted_eq_unique hf.left.right hft ht₁.right]
      exact ht₁.left

    · intro ht
      have hX₁sub := mem_pair_imp_fst_mem_dom hX₁
      rw [dG] at hX₁sub
      simp only [Set.mem_powerset_iff] at hX₁sub
      
      have ht' := hX₁sub ht
      rw [← hf.right.right.left] at ht'
      have ⟨ft, hft⟩ := dom_exists ht'
      have hft' : ft ∈ image f X₁ := ⟨t, ht, hft⟩

      rw [← hX₁', hX₂'] at hft'
      have ⟨t₁, ht₁⟩ := hft'
      rw [single_rooted_eq_unique hf.left.right hft ht₁.right]
      exact ht₁.left

  · show mapsInto G (𝒫 A) (𝒫 B)
    refine ⟨hG₁, dG, ?_⟩
    show ∀ x, x ∈ ran G → x ∈ 𝒫 B
    intro x hx
    rw [hG] at hx
    unfold ran Prod.snd at hx
    simp only [
      Set.mem_powerset_iff,
      Set.mem_image,
      Set.mem_setOf_eq,
      Prod.exists,
      exists_eq_right
    ] at hx
    have ⟨a, ha⟩ := hx
    rw [ha.right]
    show ∀ y, y ∈ image f a → y ∈ B
    intro y hy
    simp only [Set.mem_setOf_eq] at hy
    have ⟨b, hb⟩ := hy
    have hz := mem_pair_imp_snd_mem_ran hb.right
    exact hf.right.right.right hz

/-- #### Exercise 3.29

Assume that `f : A → B` and define a function `G : B → 𝒫 A` by
```
G(b) = {x ∈ A | f(x) = b}
```
Show that if `f` maps `A` *onto* `B`, then `G` is one-to-one. Does the converse
hold?
-/
theorem exercise_3_29 {f : Set.HRelation α β} {G : Set.HRelation β (Set α)}
  {A : Set α} {B : Set β} (hf : mapsOnto f A B)
  (hG : mapsInto G B (𝒫 A) ∧ G = { p | p.1 ∈ B ∧ p.2 = {x ∈ A | (x, p.1) ∈ f} })
  : isOneToOne G := by
  unfold isOneToOne
  refine ⟨hG.left.left, ?_⟩
  intro y hy
  have ⟨x₁, hx₁⟩ := ran_exists hy
  refine ⟨x₁, ⟨mem_pair_imp_fst_mem_dom hx₁, hx₁⟩, ?_⟩
  intro x₂ hx₂

  have hG₁ : (x₁, {x ∈ A | (x, x₁) ∈ f}) ∈ G := by
    rw [hG.right, ← hG.left.right.left]
    simp only [Set.mem_setOf_eq, and_true]
    exact mem_pair_imp_fst_mem_dom hx₁
  have hG₂ : (x₂, {x ∈ A | (x, x₂) ∈ f}) ∈ G := by
    rw [hG.right, ← hG.left.right.left]
    simp only [Set.mem_setOf_eq, and_true]
    exact hx₂.left
  have heq : {x ∈ A | (x, x₁) ∈ f} = {x ∈ A | (x, x₂) ∈ f} := by
    have h₁ := single_valued_eq_unique hG.left.left hx₁ hG₁
    have h₂ := single_valued_eq_unique hG.left.left hx₂.right hG₂
    rw [← h₁, ← h₂]

  rw [hG.right, ← hf.right.right] at hG₁ hG₂
  simp only [Set.mem_setOf_eq, and_true] at hG₁ hG₂
  have ⟨t, ht⟩ := ran_exists hG₁
  have : t ∈ {x ∈ A | (x, x₁) ∈ f} := by
    simp only [Set.mem_setOf_eq]
    refine ⟨?_, ht⟩
    rw [← hf.right.left]
    exact mem_pair_imp_fst_mem_dom ht
  rw [heq] at this
  simp only [Set.mem_setOf_eq] at this
  exact single_valued_eq_unique hf.left this.right ht

end Relation

end Enderton.Set.Chapter_3