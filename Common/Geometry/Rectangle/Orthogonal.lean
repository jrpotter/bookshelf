import Mathlib.Data.Fin.Basic

import Common.Geometry.Point
import Common.Geometry.Segment
import Common.Geometry.Rectangle.Skew

/-! # Common.Geometry.Rectangle.Orthogonal

A characterization of an orthogonal rectangle.
-/

namespace Geometry.Rectangle

/--
An `Orthogonal` rectangle is a `Skew` rectangle with edges parallel to the
coordinate axes.
-/
def Orthogonal := { r : Skew // r.bl.x = r.tl.x ∧ r.bl.y = r.br.y }

namespace Orthogonal

/--
The `Set` of `Point`s enclosed in the region determined by the edges of the
`Orthogonal` rectangle. Edges of the rectangle are included in the result set.
-/
def toSet (r : Orthogonal) : Set Point :=
  { p | r.val.bl.x ≤ p.x ∧ p.x ≤ r.val.br.x ∧
        r.val.bl.y ≤ p.y ∧ p.y ≤ r.val.tl.y }

/--
Show the `toSet` definition of an `Orthogonal` rectangle is in agreement with
its `Skew` counterpart.
-/
theorem orthogonal_set_eq_skew_set (r : Orthogonal)
  : r.toSet = r.val.toSet := sorry

end Orthogonal

end Geometry.Rectangle