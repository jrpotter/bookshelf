import OneVariableCalculus.Apostol.Real.Geometry.Basic

namespace Real

/--
A `Rectangle` is characterized by three distinct points and the angle formed
between line segments originating from the "bottom left" point.
-/
structure Rectangle where
  top_left : ℝ²
  bottom_left : ℝ²
  bottom_right : ℝ²
  forms_right_angle : ∠ top_left bottom_left bottom_right = π / 2

namespace Rectangle

/--
The top-right corner of the rectangle, oriented with respect to the other
vertices.
-/
def top_right (r : Rectangle) : ℝ² :=
  ( r.top_left.fst + r.bottom_right.fst - r.bottom_left.fst
  , r.top_left.snd + r.bottom_right.snd - r.bottom_left.snd
  )

/--
A `Rectangle` is the locus of points bounded by its edges.
-/
def set_def (r : Rectangle) : Set ℝ² :=
  sorry

theorem dist_top_eq_dist_bottom (r : Rectangle)
  : dist r.top_left r.top_right = dist r.bottom_left r.bottom_right := by
  unfold top_right dist
  repeat rw [add_comm, sub_right_comm, add_sub_cancel']

theorem dist_left_eq_dist_right (r : Rectangle)
  : dist r.top_left r.bottom_left = dist r.top_right r.bottom_right := by
  unfold top_right dist
  repeat rw [
    sub_sub_eq_add_sub,
    add_comm,
    sub_add_eq_sub_sub,
    sub_right_comm,
    add_sub_cancel'
  ]
  
/--
Computes the width of a `Rectangle`.
-/
noncomputable def width (r : Rectangle) : ℝ :=
  dist r.bottom_left r.bottom_right

/--
Computes the height of a `Rectangle`.
-/
noncomputable def height (r : Rectangle) : ℝ :=
  dist r.bottom_left r.top_left

end Rectangle

/--
A `Point` is a `Rectangle` in which all points coincide.
-/
abbrev Point := Subtype (fun r : Rectangle =>
  r.top_left = r.bottom_left ∧ r.bottom_left = r.bottom_right)

namespace Point

/--
A `Point` is the set consisting of just itself.
-/
def set_def (p : Point) : Set ℝ² :=
  { x : ℝ² | x = p.val.top_left }

/--
The width of a `Point` is `0`.
-/
theorem width_eq_zero (p : Point) : p.val.width = 0 := by
  unfold Rectangle.width
  rw [p.property.right]
  unfold dist
  simp

/--
The height of a `Point` is `0`.
-/
theorem height_eq_zero (p : Point) : p.val.height = 0 := by
  unfold Rectangle.height
  rw [p.property.left]
  unfold dist
  simp

end Point

/--
A `LineSegment` is a `Rectangle` in which two of the three points coincide.
-/
abbrev LineSegment := Subtype (fun r : Rectangle =>
  (r.top_left = r.bottom_left ∧ r.bottom_left ≠ r.bottom_right) ∨
  (r.top_left ≠ r.bottom_left ∧ r.bottom_left = r.bottom_right))

namespace LineSegment

def set_def (s : LineSegment) : Set ℝ² :=
  sorry

theorem width_or_height_eq_zero (s : LineSegment)
  : s.val.width = 0 ∨ s.val.height = 0 := by
  apply Or.elim s.property
  · intro h
    refine Or.inr ?_
    unfold Rectangle.height
    rw [h.left]
    unfold dist
    simp
  · intro h
    refine Or.inl ?_
    unfold Rectangle.width
    rw [h.right]
    unfold dist
    simp

end LineSegment

end Real