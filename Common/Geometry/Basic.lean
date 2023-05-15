import Common.Geometry.Point

/-! # Common.Geometry.Basic

Additional theorems and definitions useful in the context of geometry.
-/

namespace Geometry

/--
Two sets `S` and `T` are `similar` **iff** there exists a one-to-one
correspondence between `S` and `T` such that the distance between any two points
`P, Q ∈ S` and corresponding points `P', Q' ∈ T` differ by some constant `α`. In
other words, `α|PQ| = |P'Q'|`.
-/
def similar (S T : Set Point) : Prop :=
  ∃ f : Point → Point, Function.Bijective f ∧
    ∃ s : ℝ, ∀ x y : Point, x ∈ S ∧ y ∈ T →
      s * Point.dist x y = Point.dist (f x) (f y)

/--
Two sets are congruent if they are similar with a scaling factor of `1`.
-/
def congruent (S T : Set Point) : Prop :=
  ∃ f : Point → Point, Function.Bijective f ∧
    ∀ x y : Point, x ∈ S ∧ y ∈ T →
      Point.dist x y = Point.dist (f x) (f y)

/--
Any two `congruent` sets must be similar to one another.
-/
theorem congruent_similar {S T : Set Point} : congruent S T → similar S T := by
  intro hc
  let ⟨f, ⟨hf, hs⟩⟩ := hc
  conv at hs => intro x y hxy; arg 1; rw [← one_mul (Point.dist x y)]
  exact ⟨f, ⟨hf, ⟨1, hs⟩⟩⟩

end Geometry