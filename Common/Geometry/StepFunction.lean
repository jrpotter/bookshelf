import Common.Geometry.Point
import Common.Set.Partition

/-! # Common.Geometry.StepFunction

Characterization of step functions.
-/

namespace Geometry

open Set Partition

/--
A function `f`, whose domain is a closed interval `[a, b]`, is a `StepFunction`
if there exists a `Partition` `P = {x₀, x₁, …, xₙ}` of `[a, b]` such that `f` is
constant on each open subinterval of `P`.
-/
structure StepFunction where
  p : Partition ℝ
  toFun : ∀ x ∈ p.toIcc, ℝ
  const_open_subintervals :
    ∀ (hI : I ∈ p.openSubintervals), ∃ c, ∀ (hy : y ∈ I),
      toFun y (mem_open_subinterval_mem_closed_interval hI hy) = c

namespace StepFunction

/--
The ordinate set of the function.
-/
def toSet (s : StepFunction) : Set Point := sorry

end StepFunction

end Geometry