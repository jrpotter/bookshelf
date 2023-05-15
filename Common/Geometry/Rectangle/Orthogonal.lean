import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.LibrarySearch

import Common.Geometry.Point
import Common.Geometry.Segment
import Common.Geometry.Rectangle.Skew

/-! # Common.Geometry.Rectangle.Orthogonal

A characterization of an orthogonal rectangle.
-/

namespace Geometry.Rectangle

/--
An `Orthogonal` rectangle is characterized by two points on opposite corners. It
is assumed the edges of the rectangle are parallel to the coordinate axes.

A `Point` can alternatively be viewed as an `Orthogonal` rectangle in which the
two points coincide. A horizontal or vertical `Segment` can alternatively be
viewed as an `Orthogonal` rectangle with width or height (but not both) `0`.
-/
structure Orthogonal where
  bl : Point  -- bottom left
  tr : Point  -- top right

namespace Orthogonal

/--
The width of the `Orthogonal` rectangle.
-/
def width (r : Orthogonal) := r.tr.x - r.bl.x

/--
The height of the `Orthogonal` rectangle.
-/
def height (r : Orthogonal) := r.tr.y - r.bl.y

/--
The top-left corner of the `Orthogonal` rectangle.
-/
def tl (r : Orthogonal) : Point := ⟨r.bl.x, r.bl.y + r.height⟩

/--
The bottom-right corner of the `Orthogonal` rectangle.
-/
def br (r : Orthogonal) : Point := ⟨r.bl.x + r.width, r.bl.y⟩

/--
An `Orthogonal` rectangle's top side is equal in length to its bottom side.
-/
theorem dist_top_eq_dist_bottom (r : Orthogonal)
  : Point.dist r.tl r.tr = Point.dist r.bl r.br := by
  unfold tl br Point.dist width height
  norm_num

/--
An `Orthogonal` rectangle's left side is equal in length to its right side.
-/
theorem dist_left_eq_dist_right (r : Orthogonal)
  : Point.dist r.tl r.bl = Point.dist r.tr r.br := by
  unfold tl br Point.dist width height
  norm_num

/--
Convert an `Orthogonal` rectangle into a `Skew` one.
-/
def toSkew (r : Orthogonal) : Skew := ⟨r.tl, r.bl, r.br, sorry⟩

/--
The set of `Orthogonal` rectangles are embedded in the set of `Skew` rectangles.
-/
def skewEmbedding : Orthogonal ↪ Skew :=
  have : Function.Injective toSkew := by
    unfold Function.Injective
    intro r₁ r₂ h
    unfold toSkew at h
    have ⟨⟨blx₁, bly₁⟩, ⟨trx₁, try₁⟩⟩ := r₁
    have ⟨⟨blx₂, bry₂⟩, ⟨trx₂, try₂⟩⟩ := r₂
    simp
    simp at h
    unfold tl br width height at h
    simp at h
    exact ⟨⟨h.left.left, h.right.left.right⟩, ⟨h.right.right.left, h.left.right⟩⟩
  ⟨toSkew, this⟩

/-! ## Point -/

/--
A `Point` is an `Orthogonal` rectangle in which all points coincide.
-/
abbrev AsPoint := Subtype (fun r : Orthogonal => r.bl = r.tr)

namespace AsPoint

/--
The function mapping an `Orthogonal` rectangle with all points coinciding to a
`Point`.
-/
def toPoint (p : AsPoint) : Point := p.val.tl

/--
The function mapping a `Point` to an `Orthogonal` rectangle with all points
coinciding.
-/
def fromPoint (p : Point) : AsPoint := ⟨Orthogonal.mk p p, by simp⟩

/--
An isomorphism between an `Orthogonal` rectangle with all points coinciding and
a `Point`.
-/
def isoPoint : AsPoint ≃ Point :=
  {
    toFun := toPoint,
    invFun := fromPoint,
    left_inv := by
      unfold Function.LeftInverse fromPoint toPoint
      intro ⟨r, hr⟩
      congr
      repeat {
        simp only
        unfold tl height
        rw [hr]
        simp
      }
    right_inv := by
      unfold Function.RightInverse Function.LeftInverse fromPoint toPoint
      intro ⟨r, hr⟩
      unfold tl height
      simp
  }

/--
The width of an `AsPoint` is `0`.
-/
theorem width_eq_zero (p : AsPoint) : p.val.width = 0 := by
  unfold Orthogonal.width
  rw [p.property]
  simp

/--
The height of an `AsPoint` is `0`.
-/
theorem height_eq_zero (p : AsPoint) : p.val.height = 0 := by
  unfold Orthogonal.height
  rw [p.property]
  simp

end AsPoint

/-! ## Segment -/

/--
A `Segment` is an `Orthogonal` rectangle either width or height equal to `0`.
-/
abbrev AsSegment := Subtype (fun r : Orthogonal =>
  (r.bl.x = r.tr.x ∧ r.bl.y ≠ r.tr.y) ∨ (r.bl.x ≠ r.tr.x ∧ r.bl.y = r.tr.y))

namespace AsSegment

/--
Either the width or height of an `AsSegment` is zero.
-/
theorem width_or_height_eq_zero (s : AsSegment)
  : s.val.width = 0 ∨ s.val.height = 0 := by
  apply Or.elim s.property
  · intro h
    refine Or.inl ?_
    unfold width
    rw [h.left]
    simp
  · intro h
    refine Or.inr ?_
    unfold height
    rw [h.right]
    simp

end AsSegment

end Orthogonal

end Geometry.Rectangle