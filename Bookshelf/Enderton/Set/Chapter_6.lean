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
  : ∃ f, Set.BijOn f A A := by
  refine ⟨fun x => x, ?_⟩
  unfold Set.BijOn Set.MapsTo Set.InjOn Set.SurjOn
  simp only [imp_self, implies_true, Set.image_id', true_and]
  exact Eq.subset rfl

theorem theorem_6a_b [Nonempty α] (A : Set α) (B : Set β)
  (f : α → β) (hf : Set.BijOn f A B)
  : ∃ g, Set.BijOn g B A := by
  refine ⟨Function.invFunOn f A, ?_⟩
  exact (Set.bijOn_comm $ Set.BijOn.invOn_invFunOn hf).mpr hf

theorem theorem_6a_c (A : Set α) (B : Set β) (C : Set γ)
  (f : α → β) (hf : Set.BijOn f A B)
  (g : β → γ) (hg : Set.BijOn g B C)
  : ∃ h, Set.BijOn h A C := by
  exact ⟨g ∘ f, Set.BijOn.comp hg hf⟩

end Enderton.Set.Chapter_6
