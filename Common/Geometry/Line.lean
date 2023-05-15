import Common.Geometry.Point

/-! # Common.Geometry.Line

A representation of a line in the two-dimensional Cartesian plane.
-/

namespace Geometry

/--
A `Line` is represented in vector form (not to be confused with `Vector`).
It is completely characterized by a point `P` on the line in question and a
direction vector `dir` parallel to the line. Such a line is represented by
equation
```
\vec{r} = \vec{OP} + t\vec{d},
```
where `O` denotes the origin and `t ∈ ℝ`.
-/
structure Line where
  p : Point
  dir : ℝ × ℝ

end Geometry