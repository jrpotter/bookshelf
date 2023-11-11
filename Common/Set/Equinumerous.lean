import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Finite

/-! # Common.Set.Finite

Additional theorems around finite sets.
-/

namespace Set

/-! ## Definitions -/

/--
A set `A` is equinumerous to a set `B` (written `A ≈ B`) if and only if there is
a one-to-one function from `A` onto `B`.
-/
def Equinumerous (A : Set α) (B : Set β) : Prop := ∃ F, Set.BijOn F A B

infix:50 " ≈ " => Equinumerous

theorem equinumerous_def (A : Set α) (B : Set β)
  : A ≈ B ↔ ∃ F, Set.BijOn F A B := Iff.rfl

/--
A set `A` is not equinumerous to a set `B` (written `A ≉ B`) if and only if
there is no one-to-one function from `A` onto `B`.
-/
def NotEquinumerous (A : Set α) (B : Set β) : Prop := ¬ Equinumerous A B

infix:50 " ≉ " => NotEquinumerous

@[simp]
theorem not_equinumerous_def : A ≉ B ↔ ∀ F, ¬ Set.BijOn F A B := by
  apply Iff.intro
  · intro h
    unfold NotEquinumerous Equinumerous at h
    simp only [not_exists] at h
    exact h
  · intro h
    unfold NotEquinumerous Equinumerous
    simp only [not_exists]
    exact h

/--
For any set `A`, `A ≈ A`.
-/
theorem equinumerous_refl (A : Set α)
  : A ≈ A := by
  refine ⟨fun x => x, ?_⟩
  unfold Set.BijOn Set.MapsTo Set.InjOn Set.SurjOn
  simp only [imp_self, implies_true, Set.image_id', true_and]
  exact Eq.subset rfl

/--
For any sets `A` and `B`, if `A ≈ B`. then `B ≈ A`.
-/
theorem equinumerous_symm [Nonempty α] {A : Set α} {B : Set β}
  (h : A ≈ B) : B ≈ A := by
  have ⟨F, hF⟩ := h
  refine ⟨Function.invFunOn F A, ?_⟩
  exact (Set.bijOn_comm $ Set.BijOn.invOn_invFunOn hF).mpr hF

/--
For any sets `A`, `B`, and `C`, if `A ≈ B` and `B ≈ C`, then `A ≈ C`.
-/
theorem equinumerous_trans {A : Set α} {B : Set β} {C : Set γ}
  (h₁ : A ≈ B) (h₂ : B ≈ C)
  : ∃ H, Set.BijOn H A C := by
  have ⟨F, hF⟩ := h₁
  have ⟨G, hG⟩ := h₂
  exact ⟨G ∘ F, Set.BijOn.comp hG hF⟩

/--
If two sets are equal, they are trivially equinumerous.
-/
theorem eq_imp_equinumerous {A B : Set α} (h : A = B)
  : A ≈ B := by
  have := equinumerous_refl A
  conv at this => right; rw [h]
  exact this

/-! ## Finite Sets -/

/--
A set is finite if and only if it is equinumerous to a natural number.
-/
axiom finite_iff_equinumerous_nat {α : Type _} {S : Set α}
  : Set.Finite S ↔ ∃ n : ℕ, S ≈ Set.Iio n

/-! ## Emptyset -/

/--
Any set equinumerous to the emptyset is the emptyset.
-/
@[simp]
theorem equinumerous_zero_iff_emptyset {S : Set α}
  : S ≈ Set.Iio 0 ↔ S = ∅ := by
  apply Iff.intro
  · intro ⟨f, hf⟩
    by_contra nh
    rw [← Ne.def, ← Set.nonempty_iff_ne_empty] at nh
    have ⟨x, hx⟩ := nh
    have := hf.left hx
    simp at this
  · intro h
    rw [h]
    refine ⟨fun _ => ⊥, ?_, ?_, ?_⟩
    · intro _ hx
      simp at hx
    · intro _ hx
      simp at hx
    · unfold SurjOn
      simp only [bot_eq_zero', image_empty]
      show ∀ x, x ∈ Set.Iio 0 → x ∈ ∅
      intro _ hx
      simp at hx

/--
Empty sets are always equinumerous, regardless of their underlying type.
-/
theorem equinumerous_emptyset_emptyset [Bot β]
  : (∅ : Set α) ≈ (∅ : Set β) := by
  refine ⟨fun _ => ⊥, ?_, ?_, ?_⟩
  · intro _ hx
    simp at hx
  · intro _ hx
    simp at hx
  · unfold SurjOn
    simp

end Set
