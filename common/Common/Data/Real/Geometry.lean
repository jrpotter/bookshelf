import Mathlib.Data.Real.Sqrt
import Mathlib.Logic.Function.Basic

namespace Real

notation "ℝ²" => ℝ × ℝ

noncomputable def dist (x y : ℝ²) :=
  Real.sqrt ((abs (y.1 - x.1)) ^ 2 + (abs (y.2 - x.2)) ^ 2)

def similar (S T : Set ℝ²) : Prop :=
  ∃ f : ℝ² → ℝ², Function.Bijective f ∧
    ∃ s : ℝ, ∀ x y : ℝ², x ∈ S ∧ y ∈ T →
      s * dist x y = dist (f x) (f y)

def congruent (S T : Set (ℝ × ℝ)) : Prop :=
  ∃ f : ℝ² → ℝ², Function.Bijective f ∧
    ∀ x y : ℝ², x ∈ S ∧ y ∈ T →
      dist x y = dist (f x) (f y)

theorem congruent_similar {S T : Set ℝ²} : congruent S T → similar S T := by
  intro hc
  let ⟨f, ⟨hf, hs⟩⟩ := hc
  conv at hs => intro x y hxy; arg 1; rw [← one_mul (dist x y)]
  exact ⟨f, ⟨hf, ⟨1, hs⟩⟩⟩

end Real