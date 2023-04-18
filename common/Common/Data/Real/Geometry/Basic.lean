import Mathlib.Data.Real.Sqrt

notation "ℝ²" => ℝ × ℝ

namespace Real

/--
Determine the distance between two points in `ℝ²`.
-/
noncomputable def dist (x y : ℝ²) :=
  Real.sqrt ((abs (y.1 - x.1)) ^ 2 + (abs (y.2 - x.2)) ^ 2)

/--
Two sets `S` and `T` are `similar` iff there exists a one-to-one correspondence
between `S` and `T` such that the distance between any two points `P, Q ∈ S` and
corresponding points `P', Q' ∈ T` differ by some constant `α`. In other words,
`α|PQ| = |P'Q'|`.
-/
def similar (S T : Set ℝ²) : Prop :=
  ∃ f : ℝ² → ℝ², Function.Bijective f ∧
    ∃ s : ℝ, ∀ x y : ℝ², x ∈ S ∧ y ∈ T →
      s * dist x y = dist (f x) (f y)

/--
Two sets are congruent if they are similar with a scaling factor of `1`.
-/
def congruent (S T : Set (ℝ × ℝ)) : Prop :=
  ∃ f : ℝ² → ℝ², Function.Bijective f ∧
    ∀ x y : ℝ², x ∈ S ∧ y ∈ T →
      dist x y = dist (f x) (f y)

/--
Any two congruent sets must be similar to one another.
-/
theorem congruent_similar {S T : Set ℝ²} : congruent S T → similar S T := by
  intro hc
  let ⟨f, ⟨hf, hs⟩⟩ := hc
  conv at hs => intro x y hxy; arg 1; rw [← one_mul (dist x y)]
  exact ⟨f, ⟨hf, ⟨1, hs⟩⟩⟩

end Real