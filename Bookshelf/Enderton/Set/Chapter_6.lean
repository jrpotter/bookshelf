import Bookshelf.Enderton.Set.Chapter_4
import Common.Logic.Basic
import Common.Nat.Basic
import Common.Set.Basic
import Common.Set.Equinumerous
import Common.Set.Function
import Common.Set.Intervals
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Finite

/-! # Enderton.Set.Chapter_6

Cardinal Numbers and the Axiom of Choice

NOTE: We choose to use injectivity/surjectivity concepts found in
`Mathlib.Data.Set.Function` over those in `Mathlib.Init.Function` since the
former provides noncomputable utilities around obtaining inverse functions
(namely `Function.invFunOn`).
-/

namespace Enderton.Set.Chapter_6

/-- ### Theorem 6B

No set is equinumerous to its powerset.
-/
theorem theorem_6b (A : Set α)
  : A ≉ 𝒫 A := by
/-
> Let `A` be an arbitrary set and `f: A → 𝒫 A`.
-/
  rw [Set.not_equinumerous_def]
  intro f hf
  unfold Set.BijOn at hf
/-
> Define `φ = {a ∈ A | a ∉ f(a)}`.
-/
  let φ := { a ∈ A | a ∉ f a }
/-
> Clearly `φ ∈ 𝒫 A`. Furthermore, for all `a ∈ A`, `φ ≠ f(a)` since `a ∈ φ` if
> and only if `a ∉ f(a)`. Thus `f` cannot be onto `𝒫 A`. Since `f` was
> arbitrarily chosen, there exists no one-to-one correspondence between `A` and
> `𝒫 A`. Since `A` was arbitrarily chosen, there is no set equinumerous to its
> powerset.
-/
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
/-
> Let
>
> `S = {n ∈ ω | ∀ M ⊂ n, every one-to-one function f: M → n is not onto}`. (1)
>
> We show that (i) `0 ∈ S` and (ii) if `n ∈ S`, then so is `n⁺`. Afterward we
> prove (iii) the theorem statement.
-/
  induction n with
/-
> #### (i)
> By definition, `0 = ∅`. Then `0` has no proper subsets. Hence `0 ∈ S`
> vacuously.
-/
  | zero =>
    intro _ hM
    unfold Set.Iio at hM
    simp only [Nat.zero_eq, not_lt_zero', Set.setOf_false] at hM
    rw [Set.ssubset_empty_iff_false] at hM
    exact False.elim hM
/-
> #### (ii)
> Suppose `n ∈ S` and `M ⊂ n⁺`. Furthermore, let `f: M → n⁺` be a one-to-one
> function.
-/
  | succ n ih =>
    intro M hM f ⟨hf_maps, hf_inj⟩ hf_surj
/-
> If `M = ∅`, it vacuously holds that `f` is not onto `n⁺`.
-/
    by_cases hM' : M = ∅
    · rw [hM', Set.SurjOn_emptyset_Iio_iff_eq_zero] at hf_surj
      simp at hf_surj
/-
> Otherwise `M ≠ 0`. Because `M` is finite, the *Trichotomy Law for `ω`* implies
> the existence of a largest member `p ∈ M`. There are two cases to consider:
-/
    by_cases h : ¬ ∃ t, t ∈ M ∧ f t = n
/-
> ##### Case 1
> `n ∉ ran f`.
> Then `f` is not onto `n⁺`.
-/
    · have ⟨t, ht⟩ := hf_surj (show n ∈ _ by simp)
      exact absurd ⟨t, ht⟩ h
/-
> ##### Case 2
> `n ∈ ran f`.
> Then there exists some `t ∈ M` such that `⟨t, n⟩ ∈ f`.
-/
    have ⟨t, ht₁, ht₂⟩ := not_not.mp h
/-
> Define `f': M → n⁺` given by
>
> `f'(p) = f(t) = n`
> `f'(t) = f(p)`
> `f'(x) = f(x)` for all other `x`.
>
> That is, `f'` is a variant of `f` in which the largest element of its domain
> (i.e. `p`) corresponds to value `n`.
-/
    -- `M ≠ ∅` so `∃ p, ∀ x ∈ M, p ≥ x`, i.e. a maximum member.
    have ⟨p, hp₁, hp₂⟩ : ∃ p ∈ M, ∀ x, x ∈ M → p ≥ x := by
      refine subset_finite_max_nat (show Set.Finite M from ?_) ?_ ?_
      · show Set.Finite M
        have := Set.finite_lt_nat (n + 1)
        exact Set.Finite.subset this (subset_of_ssubset hM)
      · show Set.Nonempty M
        exact Set.nmem_singleton_empty.mp hM'
      · show M ⊆ M
        exact Eq.subset rfl
/-
> Next define `g = f' - {⟨p, n⟩}`. Then `g` is a function mapping `M - {p}` to
> `n`.
-/
    let g := Set.Function.swap f p t
/-
> Since `f` is one-to-one, `f'` and `g` are also one-to-one.
-/
    have hg_maps := Set.Function.swap_MapsTo_self hp₁ ht₁ hf_maps
    have hg_inj := Set.Function.swap_InjOn_self hp₁ ht₁ hf_inj
/-
> Then *(1)* indicates `g` must not be onto `n`.
-/
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
        apply Or.elim (Nat.lt_or_eq_of_lt $ hg_maps hx₁) id
        intro hx₂
        unfold Set.Function.swap at hx₂
        by_cases hc₁ : x = p
        · exact absurd hc₁ hx.right
        · rw [if_neg hc₁] at hx₂
          by_cases hc₂ : x = t
          · rw [if_pos hc₂, ← ht₂] at hx₂
            have := hf_inj hp₁ ht₁ hx₂
            rw [← hc₂] at this
            exact absurd this.symm hc₁
          · rw [if_neg hc₂, ← ht₂] at hx₂
            have := hf_inj hx₁ ht₁ hx₂
            exact absurd this hc₂
      · -- `Set.InjOn g M'`
        intro x₁ hx₁ x₂ hx₂ hg
        have hx₁' : x₁ ∈ M := (Set.diff_subset M {p}) hx₁
        have hx₂' : x₂ ∈ M := (Set.diff_subset M {p}) hx₂
        exact hg_inj hx₁' hx₂' hg
/-
> That is, there exists some `a ∈ n` such that `a ∉ ran g`.
-/
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
/-
> By the *Trichotomy Law for `ω`*, `a ≠ n`. Therefore `a ∉ ran f'`.
> `ran f' = ran f` meaning `a ∉ ran f`. Because `a ∈ n ∈ n⁺`, *Theorem 4F*
> implies `a ∈ n⁺`. Hence `f` is not onto `n⁺`.
-/
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
      · unfold Set.Function.swap
        rw [if_pos hxp, ht₂]
        exact (Nat.ne_of_lt ha₁).symm
      · refine ha₂ x ?_
        exact Set.mem_diff_of_mem hx hxp

    ext x
    dsimp only
    unfold Set.Function.swap
    simp only [Set.mem_image, Set.mem_Iio]
    apply Iff.intro
    · intro ⟨y, hy₁, hy₂⟩
      by_cases hc₁ : y = p
      · rw [if_pos hc₁, ht₂] at hy₂
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
          rwa [hc₂, ht₂]
        · rw [hc₁, ← Ne.def] at hc₂
          rwa [if_neg hc₂.symm, if_pos rfl, ← hc₁]
      · by_cases hc₂ : y = t
        · refine ⟨p, hp₁, ?_⟩
          simp only [ite_self, ite_true]
          rwa [hc₂] at hy₂
        · refine ⟨y, hy₁, ?_⟩
          rwa [if_neg hc₁, if_neg hc₂]
/-
> ##### Subconclusion
> The foregoing cases are exhaustive. Hence `n⁺ ∈ S`.
>
> #### (iii)
> By *(i)* and *(ii)*, `S` is an inductive set. By *Theorem 4B*, `S = ω`. Thus
> for all natural numbers `n`, there is no one-to-one correspondence between `n`
> and a proper subset of `n`. In other words, no natural number is equinumerous
> to a proper subset of itself.
-/

/--
No natural number is equinumerous to a proper subset of itself.
-/
theorem pigeonhole_principle {n : ℕ}
  : ∀ {M}, M ⊂ Set.Iio n → M ≉ Set.Iio n := by
  intro M hM nM
  have ⟨f, hf⟩ := nM
  have := pigeonhole_principle_aux n M hM f ⟨hf.left, hf.right.left⟩
  exact absurd hf.right.right this

/-- ### Corollary 6C

No finite set is equinumerous to a proper subset of itself.
-/
theorem corollary_6c [DecidableEq α] [Nonempty α]
  {S S' : Set α} (hS : Set.Finite S) (h : S' ⊂ S)
  : S ≉ S' := by
/-
> Let `S` be a finite set and `S'` be a proper subset of `S`. Then there exists
> some set `T`, disjoint from `S'`, such that `S' ∪ T = S`. By definition of a
> finite set, `S` is equinumerous to a natural number `n`.
-/
  let T := S \ S'
  have hT : S = S' ∪ (S \ S') := by
    simp only [Set.union_diff_self]
    exact (Set.left_subset_union_eq_self (subset_of_ssubset h)).symm
/-
> By *Theorem 6A*, `S' ∪ T ≈ S` which, by the same theorem, implies
> `S' ∪ T ≈ n`.
-/
  have hF := Set.equinumerous_refl S
  conv at hF => arg 1; rw [hT]
  have ⟨n, hG⟩ := Set.finite_iff_equinumerous_nat.mp hS
/-
> Let `f` be a one-to-one correspondence between `S' ∪ T` and `n`.
-/
  have ⟨f, hf⟩ := Set.equinumerous_trans hF hG
/-
> Then `f ↾ S'` is a one-to-one correspondence between `S'` and a proper subset
> of `n`.
-/
  let R := (Set.Iio n) \ (f '' T)
  have hR : Set.BijOn f S' R := by
    refine ⟨?_, ?_, ?_⟩
    · -- `Set.MapsTo H S' R`
      intro x hx
      refine ⟨hf.left $ Set.mem_union_left T hx, ?_⟩
      unfold Set.image
      by_contra nx
      simp only [Finset.mem_coe, Set.mem_setOf_eq] at nx

      have ⟨a, ha₁, ha₂⟩ := nx
      have hc₁ : a ∈ S' ∪ T := Set.mem_union_right S' ha₁
      have hc₂ : x ∈ S' ∪ T := Set.mem_union_left T hx
      rw [hf.right.left hc₁ hc₂ ha₂] at ha₁

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
      exact hf.right.left hc₁ hc₂ h
    · -- `Set.SurjOn H S' R`
      show ∀ r, r ∈ R → r ∈ f '' S'
      intro r hr
      unfold Set.image
      simp only [Set.mem_setOf_eq]
      dsimp only at hr
      have := hf.right.right hr.left
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
/-
> By the *Pigeonhole Principle*, `n` is not equinumerous to any proper subset of
> `n`. Therefore *Theorem 6A* implies `S'` cannot be equinumerous to `n`, which,
> by the same theorem, implies `S'` cannot be equinumerous to `S`. Hence no
> finite set is equinumerous to a proper subset of itself.
-/
  intro hf'
  have hf₁ : S ≈ R := Set.equinumerous_trans hf' ⟨f, hR⟩
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
    have ht₂ : f t ∈ Set.Iio n := hf.left (Set.mem_union_right S' ht₁)
    have ht₃ : f t ∈ R := nr (f t) ht₂
    exact absurd ⟨t, ht₁, rfl⟩ ht₃.right

/-- ### Corollary 6D (a)

Any set equinumerous to a proper subset of itself is infinite.
-/
theorem corollary_6d_a [DecidableEq α] [Nonempty α]
  {S S' : Set α} (hS : S' ⊂ S) (hf : S ≈ S')
  : Set.Infinite S := by
/-
> Let `S` be a set equinumerous to proper subset `S'` of itself. Then `S` cannot
> be a finite set by *Corollary 6C*. By definition, `S` is an infinite set.
-/
  by_contra nS
  simp only [Set.not_infinite] at nS
  exact absurd hf (corollary_6c nS hS)

/-- ### Corollary 6D (b)

The set `ω` is infinite.
-/
theorem corollary_6d_b
  : Set.Infinite (@Set.univ ℕ) := by
/-
> Consider set `S = {n ∈ ω | n is even}`. We prove that (i) `S` is equinumerous
> to `ω` and (ii) that `ω` is infinite.
-/
  let S : Set ℕ := { 2 * n | n ∈ @Set.univ ℕ }
  let f x := 2 * x
/-
> #### (i)
> Define `f : ω → S` given by `f(n) = 2 ⬝ n`. Notice `f` is well-defined by the
> definition of an even natural number, introduced in *Exercise 4.14*. We first
> show `f` is one-to-one and then that `f` is onto.
-/
  have : Set.BijOn f (@Set.univ ℕ) S := by
    refine ⟨by simp, ?_, ?_⟩
/-
> Suppose `f(n₁) = f(n₁) = 2 ⬝ n₁`. We must prove that `n₁ = n₂`.
-/
    · -- `Set.InjOn f Set.univ`
      intro n₁ _ n₂ _ hf
/-
> By the *Trichotomy Law for `ω`*, exactly one of the following may occur:
> `n₁ = n₂`, `n₁ < n₂`, or `n₂ < n₁`. If `n₁ < n₂`, then *Theorem 4N* implies
> `n₁ ⬝ 2 < n₂ ⬝ 2`. *Theorem 4K-5* then indicates `2 ⬝ n₁ < 2 ⬝ n₂`, a
> contradiction to `2 ⬝ n₁ = 2 ⬝ n₂`. A parallel argument holds for when
> `n₂ < n₁`. Thus `n₁ = n₂`.
-/
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
/-
> Next, let `m ∈ S`. That is, `m` is an even number. By definition, there exists
> some `n ∈ ω` such that `m = 2 ⬝ n`. Thus `f(n) = m`.
-/
    · -- `Set.SurjOn f Set.univ S`
      show ∀ x, x ∈ S → x ∈ f '' Set.univ
      intro x hx
      unfold Set.image
      simp only [Set.mem_univ, true_and, Set.mem_setOf_eq] at hx ⊢
      exact hx
/-
> By *(i)*, `ω` is equinumerous to a subset of itself. By *Corollary 6D (a)*,
> `ω` is infinite.
-/
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
    simp only [mul_eq_one, OfNat.ofNat_ne_one, false_and] at nx

/-- ### Corollary 6E

Any finite set is equinumerous to a unique natural number.
-/
theorem corollary_6e [Nonempty α] (S : Set α) (hS : Set.Finite S)
  : ∃! n : ℕ, S ≈ Set.Iio n  := by
/-
> Let `S` be a finite set. By definition `S` is equinumerous to a natural number
> `n`.
-/
  have ⟨n, hf⟩ := Set.finite_iff_equinumerous_nat.mp hS
  refine ⟨n, hf, ?_⟩
/-
> Suppose `S` is equinumerous to another natural number `m`.
-/
  intro m hg
/-
> By the *Trichotomy Law for `ω`*, exactly one of three situations is possible:
> `n = m`, `n < m`, or `m < n`.
-/
  match @trichotomous ℕ LT.lt _ m n with
/-
> If `n < m`, then `m ≈ S` and `S ≈ n`. By *Theorem 6A*, it follows `m ≈ n`. But
> the *Pigeonhole Principle* indicates no natural number is equinumerous to a
> proper subset of itself, a contradiction.
-/
  | Or.inr (Or.inr r) =>
    have hh := Set.equinumerous_symm hf
    have hk := Set.equinumerous_trans hh hg
    have hnm : Set.Iio n ⊂ Set.Iio m := Set.Iio_nat_lt_ssubset r
    exact absurd hk (pigeonhole_principle hnm)
/-
> If `m < n`, a parallel argument applies.
-/
  | Or.inl r =>
    have hh := Set.equinumerous_symm hg
    have hk := Set.equinumerous_trans hh hf
    have hmn : Set.Iio m ⊂ Set.Iio n := Set.Iio_nat_lt_ssubset r
    exact absurd hk (pigeonhole_principle hmn)
/-
> Hence `n = m`, proving every finite set is equinumerous to a unique natural
> number.
-/
  | Or.inr (Or.inl r) => exact r


/-- ### Lemma 6F

If `C` is a proper subset of a natural number `n`, then `C ≈ m` for some `m`
less than `n`.
-/
lemma lemma_6f {n : ℕ}
  : ∀ {C}, C ⊂ Set.Iio n → ∃ m, m < n ∧ C ≈ Set.Iio m := by
/-
> Let
>
> `S = {n ∈ ω | ∀C ⊂ n, ∃m < n such that C ≈ m}`. (2)
>
> We prove that (i) `0 ∈ S` and (ii) if `n ∈ S` then `n⁺ ∈ S`. Afterward we
> prove (iii) the lemma statement.
-/
  induction n with
/-
> #### (i)
> By definition, `0 = ∅`. Thus `0` has no proper subsets. Hence `0 ∈ S`
> vacuously.
-/
  | zero =>
    intro C hC
    unfold Set.Iio at hC
    simp only [Nat.zero_eq, not_lt_zero', Set.setOf_false] at hC
    rw [Set.ssubset_empty_iff_false] at hC
    exact False.elim hC
/-
> #### (ii)
> Suppose `n ∈ S` and consider `n⁺`. By definition of the successor,
> `n⁺ = n ∪ {n}`. There are two cases to consider:
-/
  | succ n ih =>
/-
> Let `C` be an arbitrary, proper subset of `n⁺`.
-/
    intro C hC

    -- A useful theorem we use in a couple of places.
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
/-
> There are two cases to consider:
-/
    by_cases hn : n ∉ C
/-
> ##### Case 1
> Suppose `n ∉ C`. Then `C ⊆ n`. If `C` is a proper subset of `n`, *(2)* implies
> `C` is equinumerous to some `m < n < n⁺`. If `C = n`, then *Theorem 6A*
> implies `C` is equinumerous to `n < n⁺`.
-/
    · refine h_subset_equinumerous C ?_
      show ∀ x, x ∈ C → x ∈ Set.Iio n
      intro x hx
      apply Or.elim (Nat.lt_or_eq_of_lt (subset_of_ssubset hC hx))
      · exact id
      · intro hx₁
        rw [hx₁] at hx
        exact absurd hx hn
/-
> ##### Case 2
> Suppose `n ∈ C`. Since `C` is a proper subset of `n⁺`, the set `n⁺ - C` is
> nonempty. By the *Well Ordering of `ω`*, `n⁺ - C` has a least element, say
> `p` (which does not equal `n`).
-/
    simp only [not_not] at hn
    have hC₁ : Set.Nonempty (Set.Iio (n + 1) \ C) := by
      rw [Set.ssubset_def] at hC
      have : ¬ ∀ x, x ∈ Set.Iio (n + 1) → x ∈ C := hC.right
      simp only [Set.mem_Iio, not_forall, exists_prop] at this
      exact this
    -- `p` is the least element of `n⁺ - C`.
    have ⟨p, hp⟩ := Chapter_4.well_ordering_nat hC₁
/-
> Consider now set `C' = (C - {n}) ∪ {p}`. By construction, `C' ⊆ n`.
-/
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
/-
> As seen in *Case 1*, `C'` is equinumerous to some `m < n⁺`.
-/
    have ⟨m, hm₁, hm₂⟩ := h_subset_equinumerous C' hC'₁
/-
> It suffices to show there exists a one-to-one correspondence between `C'` and
> `C`, since then *Theorem 6A* implies `C` is equinumerous to `m` as well.
-/
    suffices C' ≈ C from
      ⟨m, hm₁, Set.equinumerous_trans (Set.equinumerous_symm this) hm₂⟩
/-
> Function `f : C' → C` given by
>
> `f(x) = if x = p then n else x`
>
> is trivially one-to-one and onto as expected.
-/
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
/-
> #### (iii)
> By *(i)* and *(ii)*, `S` is an inductive set. By *Theorem 4B*, `S = ω`.
> Therefore, for every proper subset `C` of a natural number `n`, there exists
> some `m < n` such that `C ≈ n`.
-/

/-- ### Corollary 6G

Any subset of a finite set is finite.
-/
theorem corollary_6g {S S' : Set α} (hS : Set.Finite S) (hS' : S' ⊆ S)
  : Set.Finite S' := by
/-
> Let `S` be a finite set and `S' ⊆ S`.
-/
  rw [subset_iff_ssubset_or_eq, or_comm] at hS'
  apply Or.elim hS'
/-
> Clearly, if `S' = S`, then `S'` is finite.
-/
  · intro h
    rwa [h]
/-
> Therefore suppose `S'` is a proper subset of `S`.
-/
  intro h
/-
> By definition of a finite set, `S` is equinumerous to some natural number `n`.
> Let `f` be a one-to-one correspondence between `S` and `n`.
-/
  rw [Set.finite_iff_equinumerous_nat] at hS
  have ⟨n, f, hf⟩ := hS
/-
> Then `f ↾ S'` is a one-to-one correspondence between `S'` and some proper
> subset of `n`.
-/
  -- Mirrors logic found in `corollary_6c`.
  let T := S \ S'
  let R := (Set.Iio n) \ (f '' T)
  have hR : R ⊂ Set.Iio n := by
    rw [Set.ssubset_def]
    apply And.intro
    · show ∀ x, x ∈ R → x ∈ Set.Iio n
      intro _ hx
      exact hx.left
    · show ¬ ∀ x, x ∈ Set.Iio n → x ∈ R
      intro nr
      have ⟨t, ht₁⟩ : Set.Nonempty T := Set.diff_ssubset_nonempty h
      have ht₂ : f t ∈ Set.Iio n := hf.left ht₁.left
      have ht₃ : f t ∈ R := nr (f t) ht₂
      exact absurd ⟨t, ht₁, rfl⟩ ht₃.right

  have : Set.BijOn f S' R := by
    refine ⟨?_, ?_, ?_⟩
    · -- `Set.MapsTo f S' R`
      intro x hx
      dsimp only
      simp only [Set.mem_diff, Set.mem_Iio, Set.mem_image, not_exists, not_and]
      apply And.intro
      · exact hf.left (subset_of_ssubset h hx)
      · intro y hy
        by_contra nf
        have := hf.right.left (subset_of_ssubset h hx) hy.left nf.symm
        rw [this] at hx
        exact absurd hx hy.right
    · -- `Set.InjOn f S'`
      intro x₁ hx₁ x₂ hx₂ hf'
      have h₁ : x₁ ∈ S := subset_of_ssubset h hx₁
      have h₂ : x₂ ∈ S := subset_of_ssubset h hx₂
      exact hf.right.left h₁ h₂ hf'
    · -- `Set.SurjOn f S' R`
      show ∀ x, x ∈ R → x ∈ f '' S'
      intro x hx

      have h₁ := hf.right.right
      unfold Set.SurjOn at h₁
      rw [Set.subset_def] at h₁
      have ⟨y, hy⟩ := h₁ x hx.left

      refine ⟨y, ?_, hy.right⟩
      rw [← hy.right] at hx
      simp only [Set.mem_image, Set.mem_diff, not_exists, not_and] at hx
      by_contra ny
      exact (hx.right y ⟨hy.left, ny⟩) rfl
/-
> By *Lemma 6f*, `ran (f ↾ S')` is equinumerous to some `m < n`.
-/
  have ⟨m, hm⟩ := lemma_6f hR
/-
> Then *Theorem 6A* indicates `S' ≈ m`. Hence `S'` is a finite set.
-/
  have := Set.equinumerous_trans ⟨f, this⟩ hm.right
  exact Set.finite_iff_equinumerous_nat.mpr ⟨m, this⟩


/-- ### Subset Size

Let `A` be a finite set and `B ⊂ A`. Then there exist natural numbers `m, n ∈ ω`
such that `B ≈ m`, `A ≈ n`, and `m ≤ n`.
-/
lemma subset_size [DecidableEq α] [Nonempty α] {A B : Set α}
  (hBA : B ⊆ A) (hA : Set.Finite A)
  : ∃ m n : ℕ, B ≈ Set.Iio m ∧ A ≈ Set.Iio n ∧ m ≤ n := by
/-
> Let `A` be a finite set and `B` be a subset of `A`. By *Corollary 6G*, `B`
> must be finite. By definition of a finite set, there exists natural numbers
> `m, n ∈ ω` such that `B ≈ m` and `A ≈ n`.
-/
  have ⟨n, hn⟩ := Set.finite_iff_equinumerous_nat.mp hA
  have ⟨m, hm⟩ := Set.finite_iff_equinumerous_nat.mp (corollary_6g hA hBA)
  refine ⟨m, n, hm, hn, ?_⟩
/-
> By the *Trichotomy Law for `ω`*, it suffices to prove that `m > n` is not
> possible for then either `m < n` or `m = n`.
-/
  suffices ¬ m > n by
    match @trichotomous ℕ LT.lt _ m n with
    | Or.inr (Or.inl hr) =>  -- m = n
      rw [hr]
    | Or.inr (Or.inr hr) =>  -- m > n
      exact absurd hr this
    | Or.inl hr          =>  -- m < n
      exact Nat.le_of_lt hr
/-
> For the sake of contradiction, assume `m > n`. By definition of equinumerous,
> there exists a one-to-one correspondence between `B` and `m`. *Theorem 6A*
> indicates there then exists a one-to-one correspondence `f` between `m` and
> `B`. Likewise, there exists a one-to-one correspondence `g` between `A` and
> `n`.
-/
  by_contra nr
  have ⟨f, hf⟩ := Set.equinumerous_symm hm
  have ⟨g, hg⟩ := hn
/-
> Define `h : A → B` as `h(x) = f(g(x))` for all `x ∈ A`. Since `n ⊂ m` by
> *Corollary 4M*, `h` is well-defined. By *One-to-One Composition*, `h` must be
> one-to-one. thus `h` is a one-to-one correspondence between `A` and `ran h`,
> i.e. `A ≈ ran h`.
-/
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
/-
> But `n < m` meaning `ran h ⊂ B` which in turn is a proper subset of `A` by
> hypothesis. *Corollary 6C* states no finite set is equinumerous to a proper
> subset of itself, a contradiction.
-/
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

/-- ### Finite Domain and Range Size

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

/-- ### Set Difference Size

Let `A ≈ m` for some natural number `m` and `B ⊆ A`. Then there exists some
`n ∈ ω` such that `B ≈ n` and `A - B ≈ m - n`.
-/
lemma sdiff_size_aux [DecidableEq α] [Nonempty α]
  : ∀ A : Set α, A ≈ Set.Iio m →
      ∀ B, B ⊆ A →
        ∃ n : ℕ, n ≤ m ∧ B ≈ Set.Iio n ∧ A \ B ≈ (Set.Iio m) \ (Set.Iio n) := by
/-
> `Let
>
> `S = {m ∈ ω | ∀ A ≈ m, ∀ B ⊆ A, ∃ n ∈ ω(n ≤ m ∧ B ≈ n ∧ A - B ≈ m - n) }`.
>
> We prove that (i) `0 ∈ S` and (ii) if `n ∈ S` then `n⁺ ∈ S`. Afterward we
> prove (iii) the lemma statement.
-/
  induction m with
  | zero =>
/-
> #### (i)
> Let `A ≈ 0` and `B ⊆ A`. Then it follows `A = B = ∅ = 0`. Since `0 ≤ 0`,
> `B ≈ 0`, and `A - B = ∅ ≈ 0 = 0 - 0`, it follows `0 ∈ S`.
-/
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
    refine ⟨by simp, hB', Set.equinumerous_emptyset_emptyset⟩
  | succ m ih =>
/-
> #### (ii)
> Suppose `m ∈ S` and consider `m⁺`. Let `A ≈ m⁺` and let `B ⊆ A`. By definition
> of equinumerous, there exists a one-to-one corerspondnece `f` between `A` and
> `m⁺`.
-/
    intro A ⟨f, hf⟩ B hB
/-
> Since `f` is one-to-one and onto, there exists a unique value `a ∈ A` such
> that `f(a) = m`.
-/
    have hfa := hf.right.right
    unfold Set.SurjOn at hfa
    have ⟨a, ha₁, ha₂⟩ := (Set.subset_def ▸ hfa) m (by simp)
/-
> Then `B - {a} ⊆A - {a}` and `f` is a one-to-one correspondence between
> `A - {a}` and `m`.
-/
    have hBA : B \ {a} ⊆ A \ {a} := Set.diff_subset_diff_left hB
    have hfBA : Set.BijOn f (A \ {a}) (Set.Iio m) := by
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        have := hf.left hx.left
        simp only [Set.mem_Iio, gt_iff_lt] at this ⊢
        apply Or.elim (Nat.lt_or_eq_of_lt this)
        · simp
        · intro h
          rw [← ha₂] at h
          exact absurd (hf.right.left hx.left ha₁ h) hx.right
      · intro x₁ hx₁ x₂ hx₂ h
        exact hf.right.left hx₁.left hx₂.left h
      · have := hf.right.right
        unfold Set.SurjOn Set.image at this ⊢
        rw [Set.subset_def] at this ⊢
        simp only [
          Set.mem_Iio,
          Set.mem_diff,
          Set.mem_singleton_iff,
          Set.mem_setOf_eq
        ] at this ⊢
        intro x hx
        have ⟨b, hb⟩ := this x (Nat.lt.step hx)
        refine ⟨b, ⟨hb.left, ?_⟩, hb.right⟩
        by_contra nb
        rw [← nb, hb.right] at ha₂
        exact absurd ha₂ (Nat.ne_of_lt hx)
/-
> By *(IH)*, there exists some `n ∈ ω` such that `n ≤ m`, `B - {a} ≈ n` and
>
> `(A - {a}) - (B - {a}) ≈ m - n`. (6.4)
>
> There are two cases to consider:
-/
    -- `(A - {a}) - (B - {a}) ≈ m - n`
    have ⟨n, hn₁, hn₂, hn₃⟩ := ih (A \ {a}) ⟨f, hfBA⟩ (B \ {a}) hBA
    by_cases hc : a ∈ B
    · refine ⟨n.succ, ?_, ?_, ?_⟩
/-
> ##### Case 1
> Assume `a ∈ B`. Then `B ≈ n⁺`.
-/
      · exact Nat.succ_le_succ hn₁
      · -- `B ≈ Set.Iio n.succ`
        have ⟨g, hg⟩ := hn₂
        let g' x := if x = a then n else g x
        refine ⟨g', ⟨?_, ?_, ?_⟩⟩
        · -- `Set.MapsTo g' B (Set.Iio n.succ)`
          intro x hx
          dsimp only
          by_cases hx' : x = a
          · rw [if_pos hx']
            simp
          · rw [if_neg hx']
            calc g x
              _ < n := hg.left ⟨hx, hx'⟩
              _ < n + 1 := by simp
        · -- `Set.InjOn g' B`
          intro x₁ hx₁ x₂ hx₂ h
          dsimp only at h
          by_cases hc₁ : x₁ = a <;> by_cases hc₂ : x₂ = a
          · rw [hc₁, hc₂]
          · rw [if_pos hc₁, if_neg hc₂] at h
            exact absurd h.symm (Nat.ne_of_lt $ hg.left ⟨hx₂, hc₂⟩)
          · rw [if_neg hc₁, if_pos hc₂] at h
            exact absurd h (Nat.ne_of_lt $ hg.left ⟨hx₁, hc₁⟩)
          · rw [if_neg hc₁, if_neg hc₂] at h
            exact hg.right.left ⟨hx₁, hc₁⟩ ⟨hx₂, hc₂⟩ h
        · -- `Set.SurjOn g' B (Set.Iio n.succ)`
          have := hg.right.right
          unfold Set.SurjOn Set.image at this ⊢
          rw [Set.subset_def] at this ⊢
          simp only [Set.mem_Iio, Set.mem_setOf_eq] at this ⊢
          intro x hx
          by_cases hc₁ : x = n
          · refine ⟨a, hc, ?_⟩
            simp only [ite_true]
            exact hc₁.symm
          · apply Or.elim (Nat.lt_or_eq_of_lt hx)
            · intro hx₁
              have ⟨b, ⟨hb₁, hb₂⟩, hb₃⟩ := this x hx₁
              refine ⟨b, hb₁, ?_⟩
              simp only [Set.mem_singleton_iff] at hb₂
              rwa [if_neg hb₂]
            · intro hx₁
              exact absurd hx₁ hc₁
/-
> Furthermore, by definition of the set difference,
>
> `...`
-/
      · have hA₁ : (A \ {a}) \ (B \ {a}) = (A \ B) \ {a} :=
          Set.diff_mem_diff_mem_eq_diff_diff_mem
/-
> Since `a ∈ A` and `a ∈ B`, `(A - B) - {a} = A - B`.
-/
        have hA₂ : (A \ B) \ {a} = A \ B := by
          refine Set.not_mem_diff_eq_self ?_
          by_contra na
          exact absurd hc na.right
/-
> Thus
>
> `(A - {a} - (B - {a})) = (A - B) - {a}`
>                      ` = A - B`
>                      ` ≈ m - n`          *(6.4)*
>                      ` ≈ m⁺ - n⁺`
-/
        rw [hA₁, hA₂] at hn₃
        exact Set.equinumerous_trans hn₃
          (Set.equinumerous_symm Set.succ_diff_succ_equinumerous_diff)
/-
> ##### Case 2
> Assume `a ∉ B`. Then `B - {a} = B` (i.e. `B ≈ n`) and
>
> `(A - {a}) - (B - {a}) = (A - {a}) - B`
>                      ` ≈ m - n`.         *(6.4)
-/
    · have hB : B \ {a} = B := Set.not_mem_diff_eq_self hc
      refine ⟨n, ?_, ?_, ?_⟩
      · calc n
          _ ≤ m := hn₁
          _ ≤ m + 1 := by simp
      · rwa [← hB]
/-
> The above implies that there exists a one-to-one correspondence `g` between
> `(A - {a}) - B` and `m - n`. Therefore `g ∪ {⟨a, m⟩}` is a one-to-one
> correspondence between `A - B` and `(m - n) ∪ {m}`.
-/
      · rw [hB] at hn₃
        have ⟨g, hg⟩ := hn₃
        have hAB : A \ B ≈ (Set.Iio m) \ (Set.Iio n) ∪ {m} := by
          refine ⟨fun x => if x = a then m else g x, ?_, ?_, ?_⟩
          · intro x hx
            dsimp only
            by_cases hc₁ : x = a
            · rw [if_pos hc₁]
              simp
            · rw [if_neg hc₁]
              have := hg.left ⟨⟨hx.left, hc₁⟩, hx.right⟩
              simp only [
                Set.Iio_diff_Iio,
                gt_iff_lt,
                not_lt,
                ge_iff_le,
                Set.union_singleton,
                Set.mem_Ico,
                lt_self_iff_false,
                and_false,
                Set.mem_insert_iff
              ] at this ⊢
              right
              exact this
          · intro x₁ hx₁ x₂ hx₂ h
            dsimp only at h
            by_cases hc₁ : x₁ = a <;> by_cases hc₂ : x₂ = a
            · rw [hc₁, hc₂]
            · rw [if_pos hc₁, if_neg hc₂] at h
              have := hg.left ⟨⟨hx₂.left, hc₂⟩, hx₂.right⟩
              simp at this
              exact absurd h.symm (Nat.ne_of_lt this.right)
            · rw [if_neg hc₁, if_pos hc₂] at h
              have := hg.left ⟨⟨hx₁.left, hc₁⟩, hx₁.right⟩
              simp only [Set.Iio_diff_Iio, gt_iff_lt, not_lt, ge_iff_le, Set.mem_Ico] at this
              exact absurd h (Nat.ne_of_lt this.right)
            · rw [if_neg hc₁, if_neg hc₂] at h
              exact hg.right.left ⟨⟨hx₁.left, hc₁⟩, hx₁.right⟩ ⟨⟨hx₂.left, hc₂⟩, hx₂.right⟩ h
          · have := hg.right.right
            unfold Set.SurjOn Set.image at this ⊢
            rw [Set.subset_def] at this ⊢
            simp at this ⊢
            refine ⟨⟨a, ⟨ha₁, hc⟩, ?_⟩, ?_⟩
            · intro ha
              simp at ha
            · intro x hx₁ hx₂
              have ⟨y, hy₁, hy₂⟩ := this x hx₁ hx₂
              refine ⟨y, ?_, ?_⟩
              · exact ⟨hy₁.left.left, hy₁.right⟩
              · rwa [if_neg hy₁.left.right]
/-
> Hence
>
> `A - B ≈ (m - n) ∪ {m} ≈ m⁺ - n`.
-/
        exact Set.equinumerous_trans hAB (Set.diff_union_equinumerous_succ_diff hn₁)
/-
> ##### Subconclusion
> The above two cases are exhaustive and both conclude the existence of some
> `n ∈ ω` such that `n ≤ m⁺`, `B ≈ n`, and `A - B ≈ m⁺ - n`. Hence `m⁺ ∈ S`.
>
> #### (iii)
> By *(i)* and *(ii)*, `S ⊆ ω` is an inductive set. Thus *Theorem 4B* implies
> `S = ω`. Hence, for all `A ≈ m` for some `m ∈ ω`, if `B ⊆ A`, then there
> exists some `n ∈ ω` such that `n ≤ m`, `B ≈ n`, and `A - B ≈ m - n`.
-/

lemma sdiff_size [DecidableEq α] [Nonempty α] {A B : Set α}
  (hB : B ⊆ A) (hA : A ≈ Set.Iio m)
  : ∃ n : ℕ, n ≤ m ∧ B ≈ Set.Iio n ∧ A \ B ≈ (Set.Iio m) \ (Set.Iio n) :=
  sdiff_size_aux A hA B hB

/-- ### Exercise 6.7

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

/-- ### Exercise 6.8

Prove that the union of two finites sets is finite, without any use of
arithmetic.
-/
theorem exercise_6_8 {A B : Set α} (hA : Set.Finite A) (hB : Set.Finite B)
  : Set.Finite (A ∪ B) := by
  sorry

/-- ### Exercise 6.9

Prove that the Cartesian product of two finites sets is finite, without any use
of arithmetic.
-/
theorem exercise_6_9 {A : Set α} {B : Set β}
  (hA : Set.Finite A) (hB : Set.Finite B)
  : Set.Finite (Set.prod A B) := by
  sorry

end Enderton.Set.Chapter_6
