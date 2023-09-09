import Common.Logic.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Data.Set.Function
import Mathlib.Data.Rel
import Mathlib.Tactic.Ring

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
  | zero => intro _ hm; simp at hm
  | succ n ih =>
    intro m hm f
    by_cases hm' : m = 0
    · intro inj_f surj_f
      have ⟨a, ha⟩ := surj_f 0
      rw [hm'] at a
      have := a.isLt
      simp only [not_lt_zero'] at this
    · have ⟨p, hp⟩ : ∃ p : ℕ, p.succ = m := by sorry
      by_cases hn : ∃ t, f t = n
      · have ⟨t, ht⟩ := hn
        let f' : Fin m → Fin n.succ := sorry
        let g : Fin p → Fin n := sorry
        have hg_inj : Function.Injective g := sorry
        have hg := ih p (calc p
          _ < p + 1 := by simp
          _ = m := hp
          _ ≤ n := Nat.lt_succ.mp hm) g hg_inj
        sorry
      · intro _ nf
        exact absurd (nf n) hn

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
