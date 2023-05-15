import Common.Geometry.Point

/-! # Common.Geometry.Segment

A representation of a line segment in the two-dimensional Cartesian plane.
-/

namespace Geometry

/--
A characterization of a line segment.

The segment comprises of all points between points `p` and `q`, inclusive.
-/
structure Segment where
  p : Point
  q : Point

end Geometry