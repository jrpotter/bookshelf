import Mathlib.Data.Real.Basic

/-! # Common.Real.Trigonometry

Additional theorems and definitions useful in the context of trigonometry. Most
of these will likely be deleted once the corresponding functions in `Mathlib`
are ported to Lean 4.
-/

namespace Real

/--
The standard `π` variable with value `3.14159...`.
-/
axiom pi : ℝ

/--
The undirected angle at `p₂` between the line segments to `p₁` and `p₃`. If
either of those points equals `p₂`, this is `π / 2`.
-/
axiom angle (p₁ p₂ p₃ : ℝ × ℝ) : ℝ

noncomputable def euclideanAngle (p₁ p₂ p₃ : ℝ × ℝ) :=
  if p₁ = p₂ ∨ p₂ = p₃ then pi / 2 else angle p₁ p₂ p₃

end Real