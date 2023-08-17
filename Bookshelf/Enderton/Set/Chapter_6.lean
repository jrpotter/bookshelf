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

end Enderton.Set.Chapter_6
