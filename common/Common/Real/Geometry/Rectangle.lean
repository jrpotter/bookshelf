import Common.Real.Geometry.Basic

namespace Real

/--
A `Rectangle` is characterized by three distinct points and the angle formed
between line segments originating from the "bottom left" point.
-/
structure Rectangle where
  top_left : ℝ²
  bottom_left : ℝ²
  bottom_right : ℝ²
  distinct_vertices :
    top_left ≠ bottom_left ∧ bottom_left ≠ bottom_right ∧ bottom_right ≠ top_left
  forms_right_angle :
    ∠ top_left bottom_left bottom_right distinct_vertices = π / 2

namespace Rectangle

/--
A calculation of the missing point.
-/
def top_right (r : Rectangle) : ℝ² :=
  sorry

/--
A `Rectangle` is the locus of points bounded by its edges.
-/
def set_def (r : Rectangle) : Set ℝ² :=
  sorry

/--
Computes the width of a `Rectangle`.
-/
noncomputable def width (r : Rectangle) : ℝ :=
  dist r.bottom_left r.top_left

/--
Computes the height of a `Rectangle`.
-/
noncomputable def height (r : Rectangle) : ℝ :=
  dist r.bottom_left r.bottom_right

end Real.Rectangle