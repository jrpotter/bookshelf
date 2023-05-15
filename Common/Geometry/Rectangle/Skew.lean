import Common.Geometry.Point
import Common.Geometry.Segment
import Common.Real.Trigonometry

/-! # Common.Geometry.Rectangle.Skew

A characterization of a skew rectangle.
-/

namespace Geometry.Rectangle

/--
A `Skew` rectangle is characterized by three points and the angle formed between
them.

A `Point` can alternatively be viewed as a `Skew` rectangle in which all three
points coincide. A `Segment` can alternatively be viewed as a `Skew` rectangle
in which two of the three points coincide. Note that, by definition of
`Point.angle`, such a situation does indeed yield an angle of `π / 2`.
-/
structure Skew where
  tl : Point  -- top left
  bl : Point  -- bottom left
  br : Point  -- bottom right
  has_right_angle : Point.angle tl bl br = Real.pi / 2

namespace Skew

/--
The top-right corner of the `Skew` rectangle.
-/
def tr (r : Skew) : Point :=
  ⟨r.tl.x + r.br.x - r.bl.x, r.tl.y + r.br.y - r.bl.y⟩

/--
A `Skew` rectangle's top side is equal in length to its bottom side.
-/
theorem dist_top_eq_dist_bottom (r : Skew)
  : Point.dist r.tl r.tr = Point.dist r.bl r.br := by
  unfold tr Point.dist
  simp only
  repeat rw [add_comm, sub_right_comm, add_sub_cancel']

/--
A `Skew` rectangle's left side is equal in length to its right side.
-/
theorem dist_left_eq_dist_right (r : Skew)
  : Point.dist r.tl r.bl = Point.dist r.tr r.br := by
  unfold tr Point.dist
  simp only
  repeat rw [
    sub_sub_eq_add_sub,
    add_comm,
    sub_add_eq_sub_sub,
    sub_right_comm,
    add_sub_cancel'
  ]

/--
Computes the width of a `Skew` rectangle.
-/
noncomputable def width (r : Skew) : ℝ :=
  Point.dist r.bl r.br

/--
Computes the height of a `Skew` rectangle.
-/
noncomputable def height (r : Skew) : ℝ :=
  Point.dist r.bl r.tl

/--
A mapping from a `Skew` rectangle to the set describing the region enclosed by
the rectangle.
-/
def toSet (r : Skew) : Set Point := sorry

/-! ## Point -/

/--
A `Point` is a `Skew` rectangle in which all points coincide.
-/
abbrev AsPoint := Subtype (fun r : Skew => r.tl = r.bl ∧ r.bl = r.br)

namespace AsPoint

/--
The function mapping a `Skew` rectangle with all points coinciding to a `Point`.
-/
def toPoint (p : AsPoint) : Point := p.val.tl

/--
The function mapping a `Point` to a `Skew` rectangle with all points coinciding.
-/
def fromPoint (p : Point) : AsPoint :=
  have hp : Point.angle p p p = Real.pi / 2 := by
    unfold Point.angle Real.euclideanAngle
    simp
  ⟨Skew.mk p p p hp, by simp⟩

/--
An isomorphism between a `Skew` rectangle with all points coinciding and a
`Point`.
-/
def isoPoint : AsPoint ≃ Point :=
  {
    toFun := toPoint,
    invFun := fromPoint,
    left_inv := by
      unfold Function.LeftInverse fromPoint toPoint
      simp only
      intro p
      congr
      · exact p.property.left
      · rw [p.property.left]
        exact p.property.right
    right_inv := by
      unfold Function.RightInverse Function.LeftInverse fromPoint toPoint
      simp only
      intro _
      triv
  }

/--
The width of an `AsPoint` is `0`.
-/
theorem width_eq_zero (p : AsPoint) : p.val.width = 0 := by
  unfold Skew.width
  rw [p.property.right]
  unfold Point.dist
  simp

/--
The height of an `AsPoint` is `0`.
-/
theorem height_eq_zero (p : AsPoint) : p.val.height = 0 := by
  unfold Skew.height
  rw [p.property.left]
  unfold Point.dist
  simp

end AsPoint

/-! ## Segment -/

/--
A `Segment` is a `Skew` rectangle in which two of three points coincide.
-/
abbrev AsSegment := Subtype (fun r : Skew =>
  (r.tl = r.bl ∧ r.bl ≠ r.br) ∨ (r.tl ≠ r.bl ∧ r.bl = r.br))

namespace AsSegment

/--
Either the width or height of an `AsSegment` is zero.
-/
theorem width_or_height_eq_zero (s : AsSegment)
  : s.val.width = 0 ∨ s.val.height = 0 := by
  apply Or.elim s.property
  · intro h
    refine Or.inr ?_
    unfold height
    rw [h.left]
    unfold Point.dist
    simp
  · intro h
    refine Or.inl ?_
    unfold width
    rw [h.right]
    unfold Point.dist
    simp

end AsSegment

end Skew

end Geometry.Rectangle