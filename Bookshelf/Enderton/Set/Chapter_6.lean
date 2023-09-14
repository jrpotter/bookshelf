import Common.Logic.Basic
import Common.Nat.Basic
import Common.Set.Basic
import Common.Set.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Finite
import Mathlib.Tactic.LibrarySearch

/-! # Enderton.Set.Chapter_6

Cardinal Numbers and the Axiom of Choice

NOTE: We choose to use injectivity/surjectivity concepts found in
`Mathlib.Data.Set.Function` over those in `Mathlib.Init.Function` since the
former provides noncomputable utilities around obtaining inverse functions
(namely `Function.invFunOn`).
-/

namespace Enderton.Set.Chapter_6

/-- #### Theorem 6B

No set is equinumerous to its powerset.
-/
theorem theorem_6b (A : Set α)
  : ∀ f, ¬ Set.BijOn f A (𝒫 A) := by
  intro f hf
  unfold Set.BijOn at hf
  let φ := { a ∈ A | a ∉ f a }
  suffices ∀ a ∈ A, f a ≠ φ by
    have hφ := hf.right.right (show φ ∈ 𝒫 A by simp)
    have ⟨a, ha⟩ := hφ
    exact absurd ha.right (this a ha.left)
  intro a ha hfa
  by_cases h : a ∈ f a
  · have h' := h
    rw [hfa] at h
    simp only [Set.mem_setOf_eq] at h
    exact absurd h' h.right
  · rw [Set.Subset.antisymm_iff] at hfa
    have := hfa.right ⟨ha, h⟩
    exact absurd this h

/-! ### Pigeonhole Principle -/

/--
A subset of a finite set of natural numbers has a max member.
-/
lemma subset_finite_max_nat {S' S : Set ℕ}
  (hS : Set.Finite S) (hS' : Set.Nonempty S') (h : S' ⊆ S)
  : ∃ m, m ∈ S' ∧ ∀ n, n ∈ S' → n ≤ m := by
  have ⟨m, hm₁, hm₂⟩ :=
    Set.Finite.exists_maximal_wrt id S' (Set.Finite.subset hS h) hS'
  simp only [id_eq] at hm₂
  refine ⟨m, hm₁, ?_⟩
  intro n hn
  match @trichotomous ℕ LT.lt _ m n with
  | Or.inr (Or.inl r) => exact Nat.le_of_eq r.symm
  | Or.inl r =>
    have := hm₂ n hn (Nat.le_of_lt r)
    exact Nat.le_of_eq this.symm
  | Or.inr (Or.inr r) => exact Nat.le_of_lt r

/--
Auxiliary function to be proven by induction.
-/
lemma pigeonhole_principle_aux (n : ℕ)
  : ∀ M, M ⊂ Set.Iio n →
      ∀ f : ℕ → ℕ,
        Set.MapsTo f M (Set.Iio n) ∧ Set.InjOn f M →
        ¬ Set.SurjOn f M (Set.Iio n) := by
  induction n with
  | zero =>
    intro _ hM
    unfold Set.Iio at hM
    simp only [Nat.zero_eq, not_lt_zero', Set.setOf_false] at hM
    rw [Set.ssubset_empty_iff_false] at hM
    exact False.elim hM
  | succ n ih =>
    intro M hM f ⟨hf_maps, hf_inj⟩ hf_surj

    by_cases hM' : M = ∅
    · unfold Set.SurjOn at hf_surj
      rw [hM'] at hf_surj
      simp only [Set.image_empty] at hf_surj
      rw [Set.subset_def] at hf_surj
      exact hf_surj n (show n < n + 1 by simp)

    by_cases h : ¬ ∃ t, t ∈ M ∧ f t = n
    -- Trivial case. `f` must not be onto if this is the case.
    · have ⟨t, ht⟩ := hf_surj (show n ∈ _ by simp)
      exact absurd ⟨t, ht⟩ h

    -- Continue under the assumption `n ∈ ran f`.
    simp only [not_not] at h
    have ⟨t, ht₁, ht₂⟩ := h

    -- `M ≠ ∅` so `∃ p, ∀ x ∈ M, p ≥ x`.
    have ⟨p, hp₁, hp₂⟩ : ∃ p ∈ M, ∀ x, x ∈ M → p ≥ x := by
      refine subset_finite_max_nat (show Set.Finite M from ?_) ?_ ?_
      · have := Set.finite_lt_nat (n + 1)
        exact Set.Finite.subset this (subset_of_ssubset hM)
      · exact Set.nmem_singleton_empty.mp hM'
      · show ∀ t, t ∈ M → t ∈ M
        simp only [imp_self, forall_const]

    -- `g` is a variant of `f` in which the largest element of its domain
    -- (i.e. `p`) corresponds to value `n`.
    let g x := if x = p then n else if x = t then f p else f x

    have hg_maps : Set.MapsTo g M (Set.Iio (n + 1)) := by
      intro x hx
      dsimp only
      by_cases hx₁ : x = p
      · rw [hx₁]
        simp
      · rw [if_neg hx₁]
        by_cases hx₂ : x = t
        · rw [hx₂]
          simp only [ite_true, Set.mem_Iio]
          exact hf_maps hp₁
        · rw [if_neg hx₂]
          simp only [Set.mem_Iio]
          exact hf_maps hx

    have hg_inj : Set.InjOn g M := by
      intro x₁ hx₁ x₂ hx₂ hf'
      by_cases hc₁ : x₁ = p
      · by_cases hc₂ : x₂ = p
        · rw [hc₁, hc₂]
        · dsimp at hf'
          rw [hc₁] at hf'
          simp only [ite_self, ite_true] at hf'
          by_cases hc₃ : x₂ = t
          · rw [if_neg hc₂, if_pos hc₃, ← ht₂] at hf'
            rw [hc₁] at hx₁ ⊢
            rw [hc₃] at hx₂ ⊢
            exact hf_inj hx₁ hx₂ hf'.symm
          · rw [if_neg hc₂, if_neg hc₃, ← ht₂] at hf'
            have := hf_inj ht₁ hx₂ hf'
            exact absurd this.symm hc₃
      · by_cases hc₂ : x₂ = p
        · rw [hc₂] at hf'
          simp only [ite_self, ite_true] at hf'
          by_cases hc₃ : x₁ = t
          · rw [if_neg hc₁, if_pos hc₃, ← ht₂] at hf'
            rw [hc₃] at hx₁ ⊢
            rw [hc₂] at hx₂ ⊢
            have := hf_inj hx₂ hx₁ hf'
            exact this.symm
          · rw [if_neg hc₁, if_neg hc₃, ← ht₂] at hf'
            have := hf_inj hx₁ ht₁ hf'
            exact absurd this hc₃
        · dsimp only at hf'
          rw [if_neg hc₁, if_neg hc₂] at hf'
          by_cases hc₃ : x₁ = t
          · by_cases hc₄ : x₂ = t
            · rw [hc₃, hc₄]
            · rw [if_pos hc₃, if_neg hc₄] at hf'
              have := hf_inj hp₁ hx₂ hf'
              exact absurd this.symm hc₂
          · by_cases hc₄ : x₂ = t
            · rw [if_neg hc₃, if_pos hc₄] at hf'
              have := hf_inj hx₁ hp₁ hf'
              exact absurd this hc₁
            · rw [if_neg hc₃, if_neg hc₄] at hf'
              exact hf_inj hx₁ hx₂ hf'

    let M' := M \ {p}
    have hM' : M' ⊂ Set.Iio n := by
      by_cases hc : p = n
      · suffices Set.Iio (n + 1) \ {n} = Set.Iio n by
          have h₁ := Set.diff_ssubset_diff_left hM hp₁
          conv at h₁ => right; rw [hc]
          rwa [← this]
        ext x
        apply Iff.intro
        · intro hx₁
          refine Or.elim (Nat.lt_or_eq_of_lt hx₁.left) (by simp) ?_
          intro hx₂
          rw [hx₂] at hx₁
          simp at hx₁
        · intro hx₁
          exact ⟨Nat.lt_trans hx₁ (by simp), Nat.ne_of_lt hx₁⟩

      have hp_lt_n : p < n := by
        have := subset_of_ssubset hM
        have hp' : p < n + 1 := this hp₁
        exact Or.elim (Nat.lt_or_eq_of_lt hp') id (absurd · hc)

      rw [Set.ssubset_def]
      apply And.intro
      · show ∀ x, x ∈ M' → x < n
        intro x hx
        simp only [Set.mem_diff, Set.mem_singleton_iff] at hx
        calc x
          _ ≤ p := hp₂ x hx.left
          _ < n := hp_lt_n
      · show ¬ ∀ x, x < n → x ∈ M'
        by_contra np
        have := np p hp_lt_n
        simp at this

    -- Consider `g = f' - {⟨p, n⟩}`. This restriction will allow us to use
    -- the induction hypothesis to prove `g` isn't surjective.
    have ng_surj : ¬ Set.SurjOn g M' (Set.Iio n) := by
      refine ih _ hM' g ⟨?_, ?_⟩
      · -- `Set.MapsTo g M' (Set.Iio n)`
        intro x hx
        have hx₁ : x ∈ M := Set.mem_of_mem_diff hx
        apply Or.elim (Nat.lt_or_eq_of_lt $ hg_maps hx₁)
        · exact id
        · intro hx₂
          rw [← show g p = n by simp] at hx₂
          exact absurd (hg_inj hx₁ hp₁ hx₂) hx.right
      · -- `Set.InjOn g M'`
        intro x₁ hx₁ x₂ hx₂ hg
        have hx₁' : x₁ ∈ M := (Set.diff_subset M {p}) hx₁
        have hx₂' : x₂ ∈ M := (Set.diff_subset M {p}) hx₂
        exact hg_inj hx₁' hx₂' hg

    -- We have shown `g` isn't surjective. This is another way of saying that.
    have ⟨a, ha₁, ha₂⟩ : ∃ a, a < n ∧ a ∉ g '' M' := by
      unfold Set.SurjOn at ng_surj
      rw [Set.subset_def] at ng_surj
      simp only [
        Set.mem_Iio,
        Set.mem_image,
        not_forall,
        not_exists,
        not_and,
        exists_prop
      ] at ng_surj 
      unfold Set.image
      simp only [Set.mem_Iio, Set.mem_setOf_eq, not_exists, not_and]
      exact ng_surj

    -- If `g` isn't surjective then neither is `f`.
    refine absurd (hf_surj $ calc a
      _ < n := ha₁
      _ < n + 1 := by simp) (show ↑a ∉ f '' M from ?_)

    suffices g '' M = f '' M by
      rw [← this]
      show a ∉ g '' M
      unfold Set.image at ha₂ ⊢
      simp only [Set.mem_Iio, Set.mem_setOf_eq, not_exists, not_and] at ha₂ ⊢
      intro x hx
      by_cases hxp : x = p
      · rw [if_pos hxp]
        exact (Nat.ne_of_lt ha₁).symm
      · refine ha₂ x ?_
        exact Set.mem_diff_of_mem hx hxp

    ext x
    simp only [Set.mem_image, Set.mem_Iio]
    apply Iff.intro
    · intro ⟨y, hy₁, hy₂⟩
      by_cases hc₁ : y = p
      · rw [if_pos hc₁] at hy₂
        rw [hy₂] at ht₂
        exact ⟨t, ht₁, ht₂⟩
      · rw [if_neg hc₁] at hy₂
        by_cases hc₂ : y = t
        · rw [if_pos hc₂] at hy₂
          exact ⟨p, hp₁, hy₂⟩
        · rw [if_neg hc₂] at hy₂
          exact ⟨y, hy₁, hy₂⟩
    · intro ⟨y, hy₁, hy₂⟩
      by_cases hc₁ : y = p
      · refine ⟨t, ht₁, ?_⟩
        by_cases hc₂ : y = t
        · rw [hc₂, ht₂] at hy₂
          rw [← hc₁, ← hc₂]
          simp only [ite_self, ite_true]
          exact hy₂
        · rw [hc₁, ← Ne.def] at hc₂
          rwa [if_neg hc₂.symm, if_pos rfl, ← hc₁]
      · by_cases hc₂ : y = t
        · refine ⟨p, hp₁, ?_⟩
          simp only [ite_self, ite_true]
          rwa [hc₂, ht₂] at hy₂
        · refine ⟨y, hy₁, ?_⟩
          rwa [if_neg hc₁, if_neg hc₂]

/--
No natural number is equinumerous to a proper subset of itself.
-/
theorem pigeonhole_principle {n : ℕ}
  : ∀ M, M ⊂ Set.Iio n → ∀ f, ¬ Set.BijOn f M (Set.Iio n) := by
  intro M hM f nf
  have := pigeonhole_principle_aux n M hM f ⟨nf.left, nf.right.left⟩
  exact absurd nf.right.right this

/-- #### Corollary 6C

No finite set is equinumerous to a proper subset of itself.
-/
theorem corollary_6c [DecidableEq α] [Nonempty α] {S S' : Finset α} (h : S' ⊂ S)
  : ∀ f, ¬ Set.BijOn f S.toSet S'.toSet := by
  have ⟨T, hT₁, hT₂⟩ : ∃ T, Disjoint S' T ∧ S = S' ∪ T := by
    refine ⟨S \ S', ?_, ?_⟩
    · intro X hX₁ hX₂
      show ∀ t, t ∈ X → t ∈ ⊥
      intro t ht
      have ht₂ := hX₂ ht
      simp only [Finset.mem_sdiff] at ht₂
      exact absurd (hX₁ ht) ht₂.right
    · simp only [
        Finset.union_sdiff_self_eq_union,
        Finset.right_eq_union_iff_subset
      ]
      exact subset_of_ssubset h

  -- `hF : S' ∪ T ≈ S`.
  -- `hG :      S ≈ n`.
  -- `hH : S' ∪ T ≈ n`.
  have ⟨F, hF⟩ := Set.equinumerous_refl S.toSet
  conv at hF => arg 2; rw [hT₂]
  have ⟨n, G, hG⟩ := Set.finite_iff_equinumerous_nat.mp (Finset.finite_toSet S)
  have ⟨H, hH⟩ := Set.equinumerous_trans hF hG

  -- Restrict `H` to `S'` to yield a bijection between `S'` and `m < n`.
  let R := (Set.Iio n) \ (H '' T)
  have hR : Set.BijOn H S' R := by
    refine ⟨?_, ?_, ?_⟩
    · -- `Set.MapsTo H S' R`
      intro x hx
      refine ⟨hH.left $ Finset.mem_union_left T hx, ?_⟩
      unfold Set.image
      by_contra nx
      simp only [Finset.mem_coe, Set.mem_setOf_eq] at nx

      have ⟨a, ha₁, ha₂⟩ := nx
      have hc₁ : a ∈ S' ∪ T := Finset.mem_union_right S' ha₁
      have hc₂ : x ∈ S' ∪ T := Finset.mem_union_left T hx
      rw [hH.right.left hc₁ hc₂ ha₂] at ha₁

      have hx₁ : {x} ⊆ S' := Finset.singleton_subset_iff.mpr hx
      have hx₂ : {x} ⊆ T := Finset.singleton_subset_iff.mpr ha₁
      have hx₃ := hT₁ hx₁ hx₂
      simp only [
        Finset.bot_eq_empty,
        Finset.le_eq_subset,
        Finset.singleton_subset_iff,
        Finset.not_mem_empty
      ] at hx₃
    · -- `Set.InjOn H S'`
      intro x₁ hx₁ x₂ hx₂ h
      have hc₁ : x₁ ∈ S' ∪ T := Finset.mem_union_left T hx₁
      have hc₂ : x₂ ∈ S' ∪ T := Finset.mem_union_left T hx₂
      exact hH.right.left hc₁ hc₂ h
    · -- `Set.SurjOn H S' R`
      show ∀ r, r ∈ R → r ∈ H '' S'
      intro r hr
      unfold Set.image
      simp only [Finset.mem_coe, Set.mem_setOf_eq]
      dsimp only at hr
      have := hH.right.right hr.left
      simp only [
        Finset.coe_union,
        Set.mem_image,
        Set.mem_union,
        Finset.mem_coe
      ] at this
      have ⟨x, hx⟩ := this
      apply Or.elim hx.left
      · intro hx'
        exact ⟨x, hx', hx.right⟩
      · intro hx'
        refine absurd ?_ hr.right
        rw [← hx.right]
        simp only [Set.mem_image, Finset.mem_coe]
        exact ⟨x, hx', rfl⟩
  
  intro f nf
  have ⟨f₁, hf₁⟩ : ∃ f₁ : α → ℕ, Set.BijOn f₁ S R :=
    Set.equinumerous_trans nf hR
  have ⟨f₂, hf₂⟩ : ∃ f₃ : ℕ → ℕ, Set.BijOn f₃ R (Set.Iio n) := by
    have ⟨k, hk₁⟩ := Set.equinumerous_symm hf₁
    exact Set.equinumerous_trans hk₁ hG
    
  refine absurd hf₂ (pigeonhole_principle R ?_ f₂)
  show R ⊂ Set.Iio n
  apply And.intro
  · show ∀ r, r ∈ R → r ∈ Set.Iio n
    intro _ hr
    exact hr.left
  · show ¬ ∀ r, r ∈ Set.Iio n → r ∈ R
    intro nr
    have ⟨t, ht₁⟩ : Finset.Nonempty T := by
      rw [hT₂, Finset.ssubset_def] at h
      have : ¬ ∀ x, x ∈ S' ∪ T → x ∈ S' := h.right
      simp only [Finset.mem_union, not_forall, exists_prop] at this
      have ⟨x, hx⟩ := this
      apply Or.elim hx.left
      · intro nx
        exact absurd nx hx.right
      · intro hx
        exact ⟨x, hx⟩
    have ht₂ : H t ∈ Set.Iio n := hH.left (Finset.mem_union_right S' ht₁)
    have ht₃ : H t ∈ R := nr (H t) ht₂
    exact absurd ⟨t, ht₁, rfl⟩ ht₃.right

/-- #### Corollary 6D (a)

Any set equinumerous to a proper subset of itself is infinite.
-/
theorem corollary_6d_a (S S' : Set α) (hS : S' ⊂ S) (hf : S' ≃ S)
  : Set.Infinite S := by
  sorry

/-- #### Corollary 6D (b)

The set `ω` is infinite.
-/
theorem corollary_6d_b
  : Set.Infinite (@Set.univ ℕ) := by
  sorry

/-- #### Corollary 6E

Any finite set is equinumerous to a unique natural number.
-/
theorem corollary_6e (S : Set α) (hn : S ≃ Fin n) (hm : S ≃ Fin m)
  : m = n := by
  sorry

/-- #### Lemma 6F

If `C` is a proper subset of a natural number `n`, then `C ≈ m` for some `m`
less than `n`.
-/
lemma lemma_6f {n : ℕ} (hC : C ⊂ Finset.range n)
  : ∃ m : ℕ, m < n ∧ ∃ f : C → Fin m, Function.Bijective f := by
  sorry

theorem corollary_6g (S S' : Set α) (hS : Finite S) (hS' : S' ⊆ S)
  : Finite S' := by
  sorry

/-- #### Exercise 6.1

Show that the equation
```
f(m, n) = 2ᵐ(2n + 1) - 1
```
defines a one-to-one correspondence between `ω × ω` and `ω`.
-/
theorem exercise_6_1
  : Function.Bijective (fun p : ℕ × ℕ => 2 ^ p.1 * (2 * p.2 + 1) - 1) := by
  sorry

/-- #### Exercise 6.2

Show that in Fig. 32 we have:
```
J(m, n) = [1 + 2 + ⋯ + (m + n)] + m
        = (1 / 2)[(m + n)² + 3m + n].
```
-/
theorem exercise_6_2
  : Function.Bijective
      (fun p : ℕ × ℕ => (1 / 2) * ((p.1 + p.2) ^ 2 + 3 * p.1 + p.2)) := by
  sorry

/-- #### Exercise 6.3

Find a one-to-one correspondence between the open unit interval `(0, 1)` and `ℝ`
that takes rationals to rationals and irrationals to irrationals.
-/
theorem exercise_6_3
  : True := by
  sorry

/-- #### Exercise 6.4

Construct a one-to-one correspondence between the closed unit interval
```
[0, 1] = {x ∈ ℝ | 0 ≤ x ≤ 1}
```
and the open unit interval `(0, 1)`.
-/
theorem exercise_6_4
  : ∃ F, Set.BijOn F (Set.Ioo 0 1) (@Set.univ ℝ) := by
  sorry

end Enderton.Set.Chapter_6
