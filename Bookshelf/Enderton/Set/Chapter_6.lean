import Common.Logic.Basic
import Common.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Data.Set.Function
import Mathlib.Data.Rel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LibrarySearch
import Std.Data.Fin.Lemmas

/-! # Enderton.Set.Chapter_6

Cardinal Numbers and the Axiom of Choice
-/

namespace Enderton.Set.Chapter_6

/-! #### Theorem 6A

For any sets `A`, `B`, and `C`,

(a) `A ≈ A`.
(b) If `A ≈ B`, then `B ≈ A`.
(c) If `A ≈ B` and `B ≈ C`, then `A ≈ C`.
-/

theorem theorem_6a_a (A : Set α)
  : ∃ F, Set.BijOn F A A := by
  refine ⟨fun x => x, ?_⟩
  unfold Set.BijOn Set.MapsTo Set.InjOn Set.SurjOn
  simp only [imp_self, implies_true, Set.image_id', true_and]
  exact Eq.subset rfl

theorem theorem_6a_b [Nonempty α] (A : Set α) (B : Set β)
  (F : α → β) (hF : Set.BijOn F A B)
  : ∃ G, Set.BijOn G B A := by
  refine ⟨Function.invFunOn F A, ?_⟩
  exact (Set.bijOn_comm $ Set.BijOn.invOn_invFunOn hF).mpr hF

theorem theorem_6a_c (A : Set α) (B : Set β) (C : Set γ)
  (F : α → β) (hF : Set.BijOn F A B)
  (G : β → γ) (hG : Set.BijOn G B C)
  : ∃ H, Set.BijOn H A C := by
  exact ⟨G ∘ F, Set.BijOn.comp hG hF⟩

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

/-- #### Pigeonhole Principle

No natural number is equinumerous to a proper subset of itself.
-/
theorem pigeonhole_principle (n : ℕ)
  : ∀ m : ℕ, m < n →
      ∀ f : Fin m → Fin n, Function.Injective f →
        ¬ Function.Surjective f := by
  induction n with
  | zero =>
    intro _ hm
    simp at hm
  | succ n ih =>
    intro m hm f hf_inj hf_surj

    by_cases hm' : m = 0
    · have ⟨a, ha⟩ := hf_surj 0
      rw [hm'] at a
      have := a.isLt
      simp only [not_lt_zero'] at this

    -- `m ≠ 0` so `∃ p, p + 1 = m`. Represent as both a `ℕ` and `Fin` type.
    have ⟨nat_p, hnat_p⟩ := Nat.exists_eq_succ_of_ne_zero hm'
    have hnat_p_lt_m : nat_p < m := calc nat_p
      _ < nat_p + 1 := by simp
      _ = m := hnat_p.symm
    let fin_p : Fin m := ⟨nat_p, hnat_p_lt_m⟩

    by_cases hn : ¬ ∃ t, f t = n
    -- Trivial case. `f` must not be onto if this is the case.
    · exact absurd (hf_surj n) hn

    -- Continue under the assumption `n ∈ ran f`.
    simp only [not_not] at hn
    have ⟨fin_t, hfin_t⟩ := hn

    -- `f'` is a variant of `f` in which the largest element of its domain
    -- (i.e. `p`) corresponds to value `n`.
    let f' : Fin m → Fin (n + 1) := fun x =>
      if x = fin_p then n
      else if x = fin_t then f fin_p
      else f x

    have hf'_inj : Function.Injective f' := by
      intro x₁ x₂ hf'
      by_cases hx₁ : x₁ = fin_p
      · by_cases hx₂ : x₂ = fin_p
        · rw [hx₁, hx₂]
        · rw [hx₁] at hf'
          simp only [ite_self, ite_true] at hf'
          by_cases ht : x₂ = fin_t
          · rw [if_neg hx₂, if_pos ht, ← hfin_t] at hf'
            have := (hf_inj hf').symm
            rwa [hx₁, ht]
          · rw [if_neg hx₂, if_neg ht, ← hfin_t] at hf'
            have := (hf_inj hf').symm
            exact absurd this ht
      · by_cases hx₂ : x₂ = fin_p
        · rw [hx₂] at hf'
          simp only [ite_self, ite_true] at hf'
          by_cases ht : x₁ = fin_t
          · rw [if_neg hx₁, if_pos ht, ← hfin_t] at hf'
            have := (hf_inj hf').symm
            rw [← ht] at this
            exact absurd this hx₁
          · rw [if_neg hx₁, if_neg ht, ← hfin_t] at hf'
            have := hf_inj hf'
            exact absurd this ht
        · dsimp only at hf'
          rw [if_neg hx₁, if_neg hx₂] at hf'
          by_cases ht₁ : x₁ = fin_t
          · by_cases ht₂ : x₂ = fin_t
            · rw [ht₁, ht₂]
            · rw [if_pos ht₁, if_neg ht₂] at hf'
              have := (hf_inj hf').symm
              exact absurd this hx₂
          · by_cases ht₂ : x₂ = fin_t
            · rw [if_neg ht₁, if_pos ht₂] at hf'
              have := hf_inj hf'
              exact absurd this hx₁
            · rw [if_neg ht₁, if_neg ht₂] at hf'
              exact hf_inj hf'

    -- `g = f' - {⟨p, n⟩}`. This restriction allows us to use the induction
    -- hypothesis to prove `g` isn't surjective. 
    let g : Fin nat_p → Fin n := fun x =>
      let hxm := calc ↑x
        _ < nat_p := x.isLt
        _ < m := hnat_p_lt_m
      let y := f' ⟨x, hxm⟩
      ⟨y, by
        suffices y ≠ ↑n by
          apply Or.elim (Nat.lt_or_eq_of_lt y.isLt)
          · simp
          · intro hy
            rw [← Fin.val_ne_iff] at this
            refine absurd ?_ this
            rw [hy]
            simp only [Fin.coe_ofNat_eq_mod]
            exact Eq.symm (Nat.mod_succ_eq_iff_lt.mpr (by simp))
        by_contra ny
        have hp₁ : f' fin_p = f' ⟨↑x, hxm⟩ := by
          rw [show f' fin_p = n by simp, ← ny]
        have hp₂ := Fin.val_eq_of_eq (hf'_inj hp₁)
        exact (lt_self_iff_false ↑x).mp $ calc ↑x
          _ < nat_p := x.isLt
          _ = ↑fin_p := by simp
          _ = ↑x := hp₂⟩

    have hg_inj : Function.Injective g := by
      intro x₁ x₂ hg
      simp only [Fin.mk.injEq] at hg
      rw [if_neg (Nat.ne_of_lt x₁.isLt), if_neg (Nat.ne_of_lt x₂.isLt)] at hg
      let x₁m : Fin m := ⟨↑x₁, calc ↑x₁
        _ < nat_p := x₁.isLt
        _ < m := hnat_p_lt_m⟩
      let x₂m : Fin m := ⟨↑x₂, calc ↑x₂
        _ < nat_p := x₂.isLt
        _ < m := hnat_p_lt_m⟩
      by_cases hx₁ : x₁m = fin_t
      · by_cases hx₂ : x₂m = fin_t
        · rw [Fin.ext_iff] at hx₁ hx₂ ⊢
          rw [show x₁.1 = x₁m.1 from rfl, show x₂.1 = x₂m.1 from rfl, hx₁, hx₂]
        · rw [if_pos hx₁, if_neg hx₂, ← Fin.ext_iff] at hg
          have := hf_inj hg
          rw [Fin.ext_iff] at this
          exact absurd this.symm (Nat.ne_of_lt x₂.isLt)
      · by_cases hx₂ : x₂m = fin_t
        · rw [if_neg hx₁, if_pos hx₂, ← Fin.ext_iff] at hg
          have := hf_inj hg
          rw [Fin.ext_iff] at this
          exact absurd this (Nat.ne_of_lt x₁.isLt)
        · rw [if_neg hx₁, if_neg hx₂, ← Fin.ext_iff] at hg
          have := hf_inj hg
          simp only [Fin.mk.injEq] at this
          exact Fin.ext_iff.mpr this

    have ng_surj : ¬ Function.Surjective g := ih nat_p (calc nat_p
        _ < m := hnat_p_lt_m
        _ ≤ n := Nat.lt_succ.mp hm) g hg_inj
    
    -- We have shown `g` isn't surjective. This is another way of saying that.
    have ⟨a, ha⟩ : ∃ a, a ∉ Set.range g := by
      unfold Function.Surjective at ng_surj
      unfold Set.range
      simp only [not_forall, not_exists] at ng_surj 
      have ⟨a, ha₁⟩ := ng_surj
      simp only [Fin.mk.injEq] at ha₁
      refine ⟨a, ?_⟩
      intro ha₂
      simp only [Fin.mk.injEq, Set.mem_setOf_eq] at ha₂
      have ⟨y, hy⟩ := ha₂
      exact absurd hy (ha₁ y)

    -- By construction, if `g` isn't surjective then neither is `f'`.
    have hf'a : ↑a ∉ Set.range f' := by

      -- It suffices to prove that `f'` and `g` agree on all values found in
      -- `g`'s domain. The only input that complicates things is `p`, which is
      -- found in the domains of `f'` and `f`. So long as we can prove
      -- `f' p ≠ a`, then we can be sure `a` appears nowhere in `ran f'`.
      suffices ∀ x : Fin m, (ht : x < fin_p) → f' x = g ⟨x, ht⟩ by
        unfold Set.range
        simp only [Set.mem_setOf_eq, not_exists]

        intro x
        by_cases hp : x = fin_p
        · intro nx
          rw [if_pos hp, Fin.ext_iff] at nx
          simp only [
            Fin.coe_ofNat_eq_mod,
            Fin.coe_eq_castSucc,
            Fin.coe_castSucc
          ] at nx
          rw [Nat.mod_succ_eq_iff_lt.mpr (show n < n + 1 by simp)] at nx
          exact absurd nx (Nat.ne_of_lt a.isLt).symm

        · show f' x ≠ ↑↑a
          rw [show ¬x = fin_p ↔ x ≠ fin_p from Iff.rfl, ← Fin.val_ne_iff] at hp

          -- Apply our `suffice` hypothesis.
          have hx_lt_fin_p : x < fin_p := by
            refine Or.elim (Nat.lt_or_eq_of_lt $ calc ↑x
              _ < m := x.isLt
              _ = nat_p + 1 := hnat_p) id ?_
            intro hxp
            exact absurd hxp hp
          rw [this x hx_lt_fin_p]

          have ha₁ : ¬∃ y, g y = a := ha
          simp only [not_exists] at ha₁
          have ha₂ : g ⟨↑x, _⟩ ≠ a :=
            ha₁ ⟨↑x, by rwa [Fin.lt_iff_val_lt_val] at hx_lt_fin_p⟩
          norm_cast at ha₂ ⊢
          intro nx
          exact absurd (Fin.castSucc_injective n nx) ha₂

      intro t ht
      rw [Fin.ext_iff]
      simp only [Fin.coe_ofNat_eq_mod]
      generalize (
        if t = fin_p then ↑n
        else if t = fin_t then f fin_p
        else f t
      ) = y
      exact (Nat.mod_succ_eq_iff_lt.mpr y.isLt).symm

    -- Likewise, if `f'` isn't surjective then neither is `f`.
    have hfa : ↑a ∉ Set.range f := by
      suffices Set.range f = Set.range f' by rw [this]; exact hf'a
      unfold Set.range
      ext x
      apply Iff.intro
      · intro ⟨y, hy⟩
        simp only [Set.mem_setOf_eq]
        by_cases hx₁ : x = n
        · refine ⟨fin_p, ?_⟩
          simp only [ite_self, ite_true]
          exact hx₁.symm
        · by_cases hx₂ : x = ⟨f fin_p, (f fin_p).isLt⟩
          · refine ⟨fin_t, ?_⟩
            by_cases ht : fin_t = fin_p
            · rw [if_pos ht, hx₂]
              rw [ht] at hfin_t
              exact hfin_t.symm
            · rw [if_neg ht, if_pos rfl, hx₂]
          · refine ⟨y, ?_⟩
            have hy₁ : y ≠ fin_p := by
              by_contra ny
              rw [ny] at hy
              exact absurd hy.symm hx₂
            have hy₂ : y ≠ fin_t := by
              by_contra ny
              rw [ny, hfin_t] at hy
              exact absurd hy.symm hx₁
            rw [if_neg hy₁, if_neg hy₂]
            exact hy
      · intro ⟨y, hy⟩
        dsimp only at hy
        by_cases hy₁ : y = fin_p
        · rw [if_pos hy₁] at hy
          have := hf_surj ⟨n, show n < n + 1 by simp⟩
          rwa [← hy]
        · rw [if_neg hy₁] at hy
          by_cases hy₂ : y = fin_t
          · rw [if_pos hy₂] at hy
            exact ⟨fin_p, hy⟩
          · rw [if_neg hy₂] at hy
            exact ⟨y, hy⟩

    simp only [Fin.coe_eq_castSucc, Set.mem_setOf_eq] at hfa
    exact absurd (hf_surj $ Fin.castSucc a) hfa

/-- #### Corollary 6C

No finite set is equinumerous to a proper subset of itself.
-/
theorem corollary_6c (S S' : Finset α) (hS : S' ⊂ S)
  : ∀ f : S → S', ¬ Function.Bijective f := by
  sorry

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
