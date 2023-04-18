import Common.Data.Real.Geometry.Basic

namespace Real

/--
A `Rectangle` is characterized by two points defining opposite corners. We
arbitrarily choose the bottom left and top right points to perform this
characterization.
-/
structure Rectangle (bottom_left : ℝ²) (top_right : ℝ²)

namespace Rectangle

/--
A `Rectangle` is the locus of points making up its edges.
-/
def set_eq (r : Rectangle x y) : Set ℝ² := sorry

/--
Computes the bottom right corner of a `Rectangle`.
-/
def bottom_right (r : Rectangle x y) : ℝ² := sorry

/--
Computes the top left corner of a `Rectangle`.
-/
def top_left (r : Rectangle x y) : ℝ² := sorry

/--
Computes the width of a `Rectangle`.
-/
def width (r : Rectangle x y) : ℝ := sorry

/--
Computes the height of a `Rectangle`.
-/
def height (r : Rectangle x y) : ℝ := sorry

end Real.Rectangle