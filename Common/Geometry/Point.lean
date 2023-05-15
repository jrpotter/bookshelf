import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

import Common.Real.Trigonometry

/-! # Common.Geometry.Point

A representation of a point in the two-dimensional Cartesian plane.
-/

namespace Geometry

structure Point where
  x : ℝ
  y : ℝ

noncomputable instance : DecidableEq Point := by
  intro p₁ p₂
  have ⟨x₁, y₁⟩ := p₁
  have ⟨x₂, y₂⟩ := p₂
  if hp : x₁ = x₂ ∧ y₁ = y₂ then
    rw [hp.left, hp.right]
    exact isTrue rfl
  else
    rw [not_and_or] at hp
    refine isFalse ?_
    intro h
    injection h with hx hy
    apply Or.elim hp
    · intro nx
      exact absurd hx nx
    · intro ny
      exact absurd hy ny

namespace Point

/--
The function mapping a `Point` to a `2`-tuple of reals.
-/
def toTuple (p : Point) : ℝ × ℝ := (p.x, p.y)

/--
The function mapping a `2`-tuple of reals to a `Point`.
-/
def fromTuple (p : ℝ × ℝ) : Point := Point.mk p.1 p.2

/--
An isomorphism between a `Point` and a `2`-tuple.
-/
def isoTuple : Point ≃ ℝ × ℝ :=
  {
    toFun := toTuple,
    invFun := fromTuple,
    left_inv := by
      unfold Function.LeftInverse fromTuple toTuple
      simp,
    right_inv := by
      unfold Function.RightInverse Function.LeftInverse fromTuple toTuple
      simp
  }

/--
The length of the straight line segment connecting points `p` and `q`.
-/
noncomputable def dist (p q : Point) :=
  Real.sqrt ((abs (q.x - p.x)) ^ 2 + (abs (q.y - p.y)) ^ 2)

/--
The undirected angle at `p₂` between the line segments to `p₁` and `p₃`. If
either of those points equals `p₂`, this is `π / 2`.
-/
noncomputable def angle (p₁ p₂ p₃ : Point) : ℝ :=
  Real.euclideanAngle (toTuple p₁) (toTuple p₂) (toTuple p₃)

end Point

end Geometry