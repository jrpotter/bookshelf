import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Finite

/-! # Common.Set.Finite

Additional theorems around finite sets.
-/

namespace Set

/--
For any set `A`, `A ≈ A`.
-/
theorem equinumerous_refl (A : Set α)
  : ∃ F, Set.BijOn F A A := by
  refine ⟨fun x => x, ?_⟩
  unfold Set.BijOn Set.MapsTo Set.InjOn Set.SurjOn
  simp only [imp_self, implies_true, Set.image_id', true_and]
  exact Eq.subset rfl

/--
For any sets `A` and `B`, if `A ≈ B`. then `B ≈ A`.
-/
theorem equinumerous_symm [Nonempty α] {A : Set α} {B : Set β}
  {F : α → β} (hF : Set.BijOn F A B)
  : ∃ G, Set.BijOn G B A := by
  refine ⟨Function.invFunOn F A, ?_⟩
  exact (Set.bijOn_comm $ Set.BijOn.invOn_invFunOn hF).mpr hF

/--
For any sets `A`, `B`, and `C`, if `A ≈ B` and `B ≈ C`, then `A ≈ C`.
-/
theorem equinumerous_trans {A : Set α} {B : Set β} {C : Set γ}
  {F : α → β} (hF : Set.BijOn F A B)
  {G : β → γ} (hG : Set.BijOn G B C)
  : ∃ H, Set.BijOn H A C := by
  exact ⟨G ∘ F, Set.BijOn.comp hG hF⟩

/--
A set is finite if and only if it is equinumerous to a natural number.
-/
axiom finite_iff_equinumerous_nat {α : Type _} {S : Set α}
  : Set.Finite S ↔ ∃ n : ℕ, ∃ f, Set.BijOn f S (Set.Iio n)

end Set