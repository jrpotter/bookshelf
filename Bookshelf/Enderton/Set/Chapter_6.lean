import Mathlib.Data.Set.Function
import Mathlib.Data.Rel

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
