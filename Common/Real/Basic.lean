import Mathlib.Data.Real.Basic

/-! # Common.Real.Basic

A collection of basic notational conveniences.
-/

/--
An abbreviation of `ℝ²` as the Cartesian product `ℝ × ℝ`.
-/
notation "ℝ²" => ℝ × ℝ

namespace Real

/--
Definitionally, the area of a unit circle.

###### PORT

As of now, this remains an `axiom`, but it should be replaced by the definition
in `Mathlib` once ported to Lean 4.
-/
axiom pi : ℝ

/--
An abbreviation of `pi` as symbol `π`.
-/
notation "π" => pi

end Real