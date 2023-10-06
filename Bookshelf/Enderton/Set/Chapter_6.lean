import Bookshelf.Enderton.Set.Chapter_4
import Common.Logic.Basic
import Common.Nat.Basic
import Common.Set.Basic
import Common.Set.Equinumerous
import Common.Set.Intervals
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
  : A ≉ 𝒫 A := by
  rw [Set.not_equinumerous_def]
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
  : ∀ {M}, M ⊂ Set.Iio n → M ≉ Set.Iio n := by
  intro M hM nM
  have ⟨f, hf⟩ := nM
  have := pigeonhole_principle_aux n M hM f ⟨hf.left, hf.right.left⟩
  exact absurd hf.right.right this

/-- #### Corollary 6C

No finite set is equinumerous to a proper subset of itself.
-/
theorem corollary_6c [DecidableEq α] [Nonempty α]
  {S S' : Set α} (hS : Set.Finite S) (h : S' ⊂ S)
  : S ≉ S' := by
  let T := S \ S'
  have hT : S = S' ∪ (S \ S') := by
    simp only [Set.union_diff_self]
    exact (Set.left_subset_union_eq_self (subset_of_ssubset h)).symm

  -- `hF : S' ∪ T ≈ S`.
  -- `hG :      S ≈ n`.
  -- `hH : S' ∪ T ≈ n`.
  have hF := Set.equinumerous_refl S
  conv at hF => arg 1; rw [hT]
  have ⟨n, hG⟩ := Set.finite_iff_equinumerous_nat.mp hS
  have ⟨H, hH⟩ := Set.equinumerous_trans hF hG

  -- Restrict `H` to `S'` to yield a bijection between `S'` and a proper subset
  -- of `n`.
  let R := (Set.Iio n) \ (H '' T)
  have hR : Set.BijOn H S' R := by
    refine ⟨?_, ?_, ?_⟩
    · -- `Set.MapsTo H S' R`
      intro x hx
      refine ⟨hH.left $ Set.mem_union_left T hx, ?_⟩
      unfold Set.image
      by_contra nx
      simp only [Finset.mem_coe, Set.mem_setOf_eq] at nx

      have ⟨a, ha₁, ha₂⟩ := nx
      have hc₁ : a ∈ S' ∪ T := Set.mem_union_right S' ha₁
      have hc₂ : x ∈ S' ∪ T := Set.mem_union_left T hx
      rw [hH.right.left hc₁ hc₂ ha₂] at ha₁

      have hx₁ : {x} ⊆ S' := Set.singleton_subset_iff.mpr hx
      have hx₂ : {x} ⊆ T := Set.singleton_subset_iff.mpr ha₁
      have hx₃ := Set.disjoint_sdiff_right hx₁ hx₂
      simp only [
        Set.bot_eq_empty,
        Set.le_eq_subset,
        Set.singleton_subset_iff,
        Set.mem_empty_iff_false
      ] at hx₃ 
    · -- `Set.InjOn H S'`
      intro x₁ hx₁ x₂ hx₂ h
      have hc₁ : x₁ ∈ S' ∪ T := Set.mem_union_left T hx₁
      have hc₂ : x₂ ∈ S' ∪ T := Set.mem_union_left T hx₂
      exact hH.right.left hc₁ hc₂ h
    · -- `Set.SurjOn H S' R`
      show ∀ r, r ∈ R → r ∈ H '' S'
      intro r hr
      unfold Set.image
      simp only [Set.mem_setOf_eq]
      dsimp only at hr
      have := hH.right.right hr.left
      simp only [Set.mem_image, Set.mem_union] at this
      have ⟨x, hx⟩ := this
      apply Or.elim hx.left
      · intro hx'
        exact ⟨x, hx', hx.right⟩
      · intro hx'
        refine absurd ?_ hr.right
        rw [← hx.right]
        simp only [Set.mem_image, Finset.mem_coe]
        exact ⟨x, hx', rfl⟩

  intro hf
  have hf₁ : S ≈ R := Set.equinumerous_trans hf ⟨H, hR⟩
  have hf₂ : R ≈ Set.Iio n := by
    have ⟨k, hk⟩ := Set.equinumerous_symm hf₁
    exact Set.equinumerous_trans ⟨k, hk⟩ hG
    
  refine absurd hf₂ (pigeonhole_principle ?_)
  show R ⊂ Set.Iio n
  apply And.intro
  · show ∀ r, r ∈ R → r ∈ Set.Iio n
    intro _ hr
    exact hr.left
  · show ¬ ∀ r, r ∈ Set.Iio n → r ∈ R
    intro nr
    have ⟨t, ht₁⟩ : Set.Nonempty T := Set.diff_ssubset_nonempty h
    have ht₂ : H t ∈ Set.Iio n := hH.left (Set.mem_union_right S' ht₁)
    have ht₃ : H t ∈ R := nr (H t) ht₂
    exact absurd ⟨t, ht₁, rfl⟩ ht₃.right

/-- #### Corollary 6D (a)

Any set equinumerous to a proper subset of itself is infinite.
-/
theorem corollary_6d_a [DecidableEq α] [Nonempty α]
  {S S' : Set α} (hS : S' ⊂ S) (hf : S ≈ S')
  : Set.Infinite S := by
  by_contra nS
  simp only [Set.not_infinite] at nS
  exact absurd hf (corollary_6c nS hS)

/-- #### Corollary 6D (b)

The set `ω` is infinite.
-/
theorem corollary_6d_b
  : Set.Infinite (@Set.univ ℕ) := by
  let S : Set ℕ := { 2 * n | n ∈ @Set.univ ℕ }
  let f x := 2 * x
  suffices Set.BijOn f (@Set.univ ℕ) S by
    refine corollary_6d_a ?_ ⟨f, this⟩
    rw [Set.ssubset_def]
    apply And.intro
    · simp
    · show ¬ ∀ x, x ∈ Set.univ → x ∈ S
      simp only [
        Set.mem_univ,
        true_and,
        Set.mem_setOf_eq,
        forall_true_left,
        not_forall,
        not_exists
      ]
      refine ⟨1, ?_⟩
      intro x nx
      simp only [mul_eq_one, false_and] at nx

  refine ⟨by simp, ?_, ?_⟩
  · -- `Set.InjOn f Set.univ`
    intro n₁ _ n₂ _ hf
    match @trichotomous ℕ LT.lt _ n₁ n₂ with
    | Or.inr (Or.inl r) => exact r
    | Or.inl r =>
      have := (Chapter_4.theorem_4n_ii n₁ n₂ 1).mp r
      conv at this => left; rw [mul_comm]
      conv at this => right; rw [mul_comm]
      exact absurd hf (Nat.ne_of_lt this)
    | Or.inr (Or.inr r) =>
      have := (Chapter_4.theorem_4n_ii n₂ n₁ 1).mp r
      conv at this => left; rw [mul_comm]
      conv at this => right; rw [mul_comm]
      exact absurd hf.symm (Nat.ne_of_lt this)
  · -- `Set.SurjOn f Set.univ S`
    show ∀ x, x ∈ S → x ∈ f '' Set.univ
    intro x hx
    unfold Set.image
    simp only [Set.mem_univ, true_and, Set.mem_setOf_eq] at hx ⊢
    exact hx

/-- #### Corollary 6E

Any finite set is equinumerous to a unique natural number.
-/
theorem corollary_6e [Nonempty α] (S : Set α) (hS : Set.Finite S)
  : ∃! n : ℕ, S ≈ Set.Iio n  := by
  have ⟨n, hf⟩ := Set.finite_iff_equinumerous_nat.mp hS
  refine ⟨n, hf, ?_⟩
  intro m hg
  match @trichotomous ℕ LT.lt _ m n with
  | Or.inr (Or.inl r) => exact r
  | Or.inl r =>
    have hh := Set.equinumerous_symm hg
    have hk := Set.equinumerous_trans hh hf
    have hmn : Set.Iio m ⊂ Set.Iio n := Set.Iio_nat_lt_ssubset r
    exact absurd hk (pigeonhole_principle hmn)
  | Or.inr (Or.inr r) =>
    have hh := Set.equinumerous_symm hf
    have hk := Set.equinumerous_trans hh hg
    have hnm : Set.Iio n ⊂ Set.Iio m := Set.Iio_nat_lt_ssubset r
    exact absurd hk (pigeonhole_principle hnm)

/-- #### Lemma 6F

If `C` is a proper subset of a natural number `n`, then `C ≈ m` for some `m`
less than `n`.
-/
lemma lemma_6f {n : ℕ}
  : ∀ {C}, C ⊂ Set.Iio n → ∃ m, m < n ∧ C ≈ Set.Iio m := by
  induction n with
  | zero =>
    intro C hC
    unfold Set.Iio at hC
    simp only [Nat.zero_eq, not_lt_zero', Set.setOf_false] at hC
    rw [Set.ssubset_empty_iff_false] at hC
    exact False.elim hC
  | succ n ih =>
    have h_subset_equinumerous
      : ∀ S, S ⊆ Set.Iio n →
          ∃ m, m < n + 1 ∧ S ≈ Set.Iio m := by
      intro S hS
      rw [subset_iff_ssubset_or_eq] at hS
      apply Or.elim hS
      · -- `S ⊂ Set.Iio n`
        intro h
        have ⟨m, hm⟩ := ih h
        exact ⟨m, calc m
          _ < n := hm.left
          _ < n + 1 := by simp, hm.right⟩
      · -- `S = Set.Iio n`
        intro h
        exact ⟨n, by simp, Set.eq_imp_equinumerous h⟩

    intro C hC
    by_cases hn : n ∈ C
    · -- Since `C` is a proper subset of `n⁺`, the set `n⁺ - C` is nonempty.
      have hC₁ : Set.Nonempty (Set.Iio (n + 1) \ C) := by
        rw [Set.ssubset_def] at hC
        have : ¬ ∀ x, x ∈ Set.Iio (n + 1) → x ∈ C := hC.right
        simp only [Set.mem_Iio, not_forall, exists_prop] at this
        exact this
      -- `p` is the least element of `n⁺ - C`.
      have ⟨p, hp⟩ := Chapter_4.well_ordering_nat hC₁

      let C' := (C \ {n}) ∪ {p}
      have hC'₁ : C' ⊆ Set.Iio n := by
        show ∀ x, x ∈ C' → x ∈ Set.Iio n
        intro x hx
        match @trichotomous ℕ LT.lt _ x n with
        | Or.inl r => exact r
        | Or.inr (Or.inl r) =>
          rw [r] at hx
          apply Or.elim hx
          · intro nx
            simp at nx
          · intro nx
            simp only [Set.mem_singleton_iff] at nx
            rw [nx] at hn
            exact absurd hn hp.left.right
        | Or.inr (Or.inr r) =>
          apply Or.elim hx
          · intro ⟨h₁, h₂⟩
            have h₃ := subset_of_ssubset hC h₁
            simp only [Set.mem_singleton_iff, Set.mem_Iio] at h₂ h₃
            exact Or.elim (Nat.lt_or_eq_of_lt h₃) id (absurd · h₂)
          · intro h
            simp only [Set.mem_singleton_iff] at h
            have := hp.left.left
            rw [← h] at this
            exact Or.elim (Nat.lt_or_eq_of_lt this)
              id (absurd · (Nat.ne_of_lt r).symm)
      have ⟨m, hm₁, hm₂⟩ := h_subset_equinumerous C' hC'₁

      suffices C' ≈ C from
        ⟨m, hm₁, Set.equinumerous_trans (Set.equinumerous_symm this) hm₂⟩
      
      -- Proves `f` is a one-to-one correspondence between `C'` and `C`.
      let f x := if x = p then n else x
      refine ⟨f, ?_, ?_, ?_⟩
      · -- `Set.MapsTo f C' C`
        intro x hx
        dsimp only
        by_cases hxp : x = p
        · rw [if_pos hxp]
          exact hn
        · rw [if_neg hxp]
          apply Or.elim hx
          · exact fun x => x.left
          · intro hx₁
            simp only [Set.mem_singleton_iff] at hx₁
            exact absurd hx₁ hxp
      · -- `Set.InjOn f C'`
        intro x₁ hx₁ x₂ hx₂ hf
        dsimp only at hf
        by_cases hx₁p : x₁ = p
        · by_cases hx₂p : x₂ = p
          · rw [hx₁p, hx₂p]
          · rw [if_pos hx₁p, if_neg hx₂p] at hf
            apply Or.elim hx₂
            · intro nx
              exact absurd hf.symm nx.right
            · intro nx
              simp only [Set.mem_singleton_iff] at nx
              exact absurd nx hx₂p
        · by_cases hx₂p : x₂ = p
          · rw [if_neg hx₁p, if_pos hx₂p] at hf
            apply Or.elim hx₁
            · intro nx
              exact absurd hf nx.right
            · intro nx
              simp only [Set.mem_singleton_iff] at nx
              exact absurd nx hx₁p
          · rwa [if_neg hx₁p, if_neg hx₂p] at hf
      · -- `Set.SurjOn f C' C`
        show ∀ x, x ∈ C → x ∈ f '' C'
        intro x hx
        simp only [
          Set.union_singleton,
          Set.mem_diff,
          Set.mem_singleton_iff,
          Set.mem_image,
          Set.mem_insert_iff,
          exists_eq_or_imp,
          ite_true
        ]
        by_cases nx₁ : x = n
        · left
          exact nx₁.symm
        · right
          by_cases nx₂ : x = p
          · have := hp.left.right
            rw [← nx₂] at this
            exact absurd hx this
          · exact ⟨x, ⟨hx, nx₁⟩, by rwa [if_neg]⟩

    · refine h_subset_equinumerous C ?_
      show ∀ x, x ∈ C → x ∈ Set.Iio n
      intro x hx
      unfold Set.Iio
      apply Or.elim (Nat.lt_or_eq_of_lt (subset_of_ssubset hC hx))
      · exact id
      · intro hx₁
        rw [hx₁] at hx
        exact absurd hx hn

/-- #### Corollary 6G

Any subset of a finite set is finite.
-/
theorem corollary_6g {S S' : Set α} (hS : Set.Finite S) (hS' : S' ⊆ S)
  : Set.Finite S' := by
  rw [subset_iff_ssubset_or_eq] at hS'
  apply Or.elim hS'
  · intro h
    rw [Set.finite_iff_equinumerous_nat] at hS
    have ⟨n, F, hF⟩ := hS

    -- Mirrors logic found in `corollary_6c`.
    let T := S \ S'
    let R := (Set.Iio n) \ (F '' T)
    have hR : R ⊂ Set.Iio n := by
      rw [Set.ssubset_def]
      apply And.intro
      · show ∀ x, x ∈ R → x ∈ Set.Iio n
        intro _ hx
        exact hx.left
      · show ¬ ∀ x, x ∈ Set.Iio n → x ∈ R
        intro nr
        have ⟨t, ht₁⟩ : Set.Nonempty T := Set.diff_ssubset_nonempty h
        have ht₂ : F t ∈ Set.Iio n := hF.left ht₁.left
        have ht₃ : F t ∈ R := nr (F t) ht₂
        exact absurd ⟨t, ht₁, rfl⟩ ht₃.right

    suffices Set.BijOn F S' R by
      have ⟨m, hm⟩ := lemma_6f hR
      have := Set.equinumerous_trans ⟨F, this⟩ hm.right
      exact Set.finite_iff_equinumerous_nat.mpr ⟨m, this⟩
    refine ⟨?_, ?_, ?_⟩
    · -- `Set.MapsTo f S' R`
      intro x hx
      dsimp only
      simp only [Set.mem_diff, Set.mem_Iio, Set.mem_image, not_exists, not_and]
      apply And.intro
      · exact hF.left (subset_of_ssubset h hx)
      · intro y hy
        by_contra nf
        have := hF.right.left (subset_of_ssubset h hx) hy.left nf.symm
        rw [this] at hx
        exact absurd hx hy.right
    · -- `Set.InjOn f S'`
      intro x₁ hx₁ x₂ hx₂ hf
      have h₁ : x₁ ∈ S := subset_of_ssubset h hx₁
      have h₂ : x₂ ∈ S := subset_of_ssubset h hx₂
      exact hF.right.left h₁ h₂ hf
    · -- `Set.SurjOn f S' R`
      show ∀ x, x ∈ R → x ∈ F '' S'
      intro x hx

      have h₁ := hF.right.right
      unfold Set.SurjOn at h₁
      rw [Set.subset_def] at h₁
      have ⟨y, hy⟩ := h₁ x hx.left

      refine ⟨y, ?_, hy.right⟩
      rw [← hy.right] at hx
      simp only [Set.mem_image, Set.mem_diff, not_exists, not_and] at hx
      by_contra ny
      exact (hx.right y ⟨hy.left, ny⟩) rfl

  · intro h
    rwa [h]

/-- #### Subset Size

Let `A` be a finite set and `B ⊂ A`. Then there exist natural numbers `m, n ∈ ω`
such that `B ≈ m`, `A ≈ n`, and `m ≤ n`.
-/
lemma subset_size [DecidableEq α] [Nonempty α] {A B : Set α}
  (hBA : B ⊆ A) (hA : Set.Finite A)
  : ∃ m n : ℕ, B ≈ Set.Iio m ∧ A ≈ Set.Iio n ∧ m ≤ n := by
  have ⟨n, hn⟩ := Set.finite_iff_equinumerous_nat.mp hA
  have ⟨m, hm⟩ := Set.finite_iff_equinumerous_nat.mp (corollary_6g hA hBA)
  refine ⟨m, n, hm, hn, ?_⟩

  suffices ¬ m > n by
    match @trichotomous ℕ LT.lt _ m n with
    | Or.inr (Or.inl hr) =>  -- m = n
      rw [hr]
    | Or.inr (Or.inr hr) =>  -- m > n
      exact absurd hr this
    | Or.inl hr          =>  -- m < n
      exact Nat.le_of_lt hr

  by_contra nr
  have ⟨f, hf⟩ := Set.equinumerous_symm hm
  have ⟨g, hg⟩ := hn

  let h x := f (g x)
  have hh : Set.BijOn h A (h '' A) := by
    refine ⟨?_, ?_, Eq.subset rfl⟩
    · -- `Set.MapsTo h A (ran h)`
      intro x hx
      simp only [Set.mem_image]
      exact ⟨x, hx, rfl⟩
    · -- `Set.InjOn h A`
      refine Set.InjOn.comp hf.right.left hg.right.left ?_
      intro x hx
      exact Nat.lt_trans (hg.left hx) nr

  have : h '' A ⊂ A := by
    rw [Set.ssubset_def]
    apply And.intro
    · show ∀ x, x ∈ h '' A → x ∈ A
      intro x hx
      have ⟨y, hy₁, hy₂⟩ := hx
      have h₁ : g y ∈ Set.Iio n := hg.left hy₁
      have h₂ : f (g y) ∈ B := hf.left (Nat.lt_trans h₁ nr)
      have h₃ : x ∈ B := by rwa [← hy₂]
      exact hBA h₃
    · rw [Set.subset_def]
      simp only [Set.mem_image, not_forall, not_exists, not_and, exists_prop]
      refine ⟨f n, hBA (hf.left nr), ?_⟩
      intro x hx
      by_contra nh
      have h₁ : g x < n := hg.left hx
      have h₂ : g x ∈ Set.Iio m := Nat.lt_trans h₁ nr
      rw [hf.right.left h₂ nr nh] at h₁
      simp at h₁
  exact absurd ⟨h, hh⟩ (corollary_6c hA this)

/-- #### Finite Domain and Range Size

Let `A` and `B` be finite sets and `f : A → B` be a function. Then there exist
natural numbers `m, n ∈ ω` such that `dom f ≈ m`, `ran f ≈ n`, and `m ≥ n`.
-/
theorem finite_dom_ran_size [Nonempty α] {A B : Set α}
  (hA : Set.Finite A) (hB : Set.Finite B) (hf : Set.MapsTo f A B)
  : ∃ m n : ℕ, A ≈ Set.Iio m ∧ f '' A ≈ Set.Iio n ∧ m ≥ n := by
  have ⟨m, hm⟩ := Set.finite_iff_equinumerous_nat.mp hA
  have ⟨p, hp⟩ := Set.finite_iff_equinumerous_nat.mp hB
  have ⟨g, hg⟩ := Set.equinumerous_symm hm

  let A_y y := { x ∈ Set.Iio m | f (g x) = y }
  have hA₁ : ∀ y ∈ B, A_y y ≈ f ⁻¹' {y} := by
    sorry
  have hA₂ : ∀ y ∈ B, Set.Nonempty (A_y y) := by
    sorry
  have hA₃ : ∀ y ∈ B, ∃ q : ℕ, ∀ p ∈ A_y y, q ≤ p := by
    sorry

  let C := { q | ∃ y ∈ B, ∀ p ∈ A_y y, q ≤ p }
  let h x := f (g x)
  have hh : C ≈ f '' A := by
    sorry

  sorry

/-- #### Set Difference Size

Let `A ≈ m` for some natural number `m` and `B ⊆ A`. Then there exists some
`n ∈ ω` such that `B ≈ n` and `A - B ≈ m - n`.
-/
lemma sdiff_size_aux [DecidableEq α] [Nonempty α]
  : ∀ A : Set α, A ≈ Set.Iio m →
      ∀ B, B ⊆ A →
        ∃ n : ℕ, B ≈ Set.Iio n ∧ A \ B ≈ (Set.Iio m) \ (Set.Iio n) := by
  induction m with
  | zero =>
    intro A hA B hB
    refine ⟨0, ?_⟩
    simp only [
      Nat.zero_eq,
      sdiff_self,
      Set.bot_eq_empty,
      Set.equinumerous_zero_iff_emptyset
    ] at hA ⊢
    have hB' : B = ∅ := Set.subset_eq_empty hB hA
    have : A \ B = ∅ := by
      rw [hB']
      simp only [Set.diff_empty]
      exact hA
    rw [this]
    refine ⟨hB', Set.equinumerous_emptyset_emptyset⟩
  | succ m ih =>
    sorry

lemma sdiff_size [DecidableEq α] [Nonempty α] {A B : Set α}
  (hB : B ⊆ A) (hA : A ≈ Set.Iio m)
  : ∃ n : ℕ, B ≈ Set.Iio n ∧ A \ B ≈ (Set.Iio m) \ (Set.Iio n) :=
  sdiff_size_aux A hA B hB

/-- #### Exercise 6.7

Assume that `A` is finite and `f : A → A`. Show that `f` is one-to-one **iff**
`ran f = A`.
-/
theorem exercise_6_7 [DecidableEq α] [Nonempty α] {A : Set α} {f : α → α}
  (hA₁ : Set.Finite A) (hA₂ : Set.MapsTo f A A)
  : Set.InjOn f A ↔ f '' A = A := by
  apply Iff.intro
  · intro hf
    have hf₂ : A ≈ f '' A := by
      refine ⟨f, ?_, hf, ?_⟩
      · -- `Set.MapsTo f A (f '' A)`
        intro x hx
        simp only [Set.mem_image]
        exact ⟨x, hx, rfl⟩
      · -- `Set.SurjOn f A (f '' A)`
        intro _ hx
        exact hx
    have hf₃ : f '' A  ⊆ A := by
      show ∀ x, x ∈ f '' A → x ∈ A
      intro x ⟨a, ha₁, ha₂⟩
      rw [← ha₂]
      exact hA₂ ha₁
    rw [subset_iff_ssubset_or_eq] at hf₃
    exact Or.elim hf₃ (fun h => absurd hf₂ (corollary_6c hA₁ h)) id
  · intro hf₁
    by_cases hA₃ : A = ∅
    · rw [hA₃]
      simp
    · intro x₁ hx₁ x₂ hx₂ hf₂
      let y := f x₁
      let B := f ⁻¹' {y}
      have hB₁ : x₁ ∈ B := sorry
      have hB₂ : x₂ ∈ B := sorry
      have hB₃ : B ⊆ A := sorry
      have ⟨m₁, n₁, hm₁, hn₁, hmn₁⟩ := subset_size hB₃ hA₁
      
      have hf'₁ : Set.MapsTo f (A \ B) (A \ {y}) := sorry
      have hf'₂ : f '' (A \ B) = A \ {y} := sorry
      have hf'₃ : Set.Finite (A \ B) := sorry
      have hf'₄ : Set.Finite (A \ {y}) := sorry

      have ⟨m₂, n₂, hm₂, hn₂, hmn₂⟩ := finite_dom_ran_size hf'₃ hf'₄ hf'₁
      
      have h₁ : A \ B ≈ Set.Iio (n₁ - m₁) := sorry
      have h₂ : A \ {y} ≈ Set.Iio (n₁ - 1) := sorry
      sorry

/-- #### Exercise 6.8

Prove that the union of two finites sets is finite, without any use of
arithmetic.
-/
theorem exercise_6_8 {A B : Set α} (hA : Set.Finite A) (hB : Set.Finite B)
  : Set.Finite (A ∪ B) := by
  sorry

/-- #### Exercise 6.9

Prove that the Cartesian product of two finites sets is finite, without any use
of arithmetic.
-/
theorem exercise_6_9 {A : Set α} {B : Set β}
  (hA : Set.Finite A) (hB : Set.Finite B)
  : Set.Finite (Set.prod A B) := by
  sorry

end Enderton.Set.Chapter_6
