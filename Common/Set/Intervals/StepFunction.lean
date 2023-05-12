import Common.List.Basic
import Common.Set.Intervals.Partition

/-! # Common.Set.Intervals.StepFunction

Characterization of step functions.
-/

namespace Set.Intervals

/--
A function `f`, whose domain is a closed interval `[a, b]`, is a `StepFunction`
if there exists a `Partition` `P = {x₀, x₁, …, xₙ}` of `[a, b]` such that `f` is
constant on each open subinterval of `P`.
-/
structure StepFunction (α : Type _) [Preorder α] [@DecidableRel α LT.lt] where
  /- A partition of some closed interval `[a, b]`. -/
  partition : Partition α
  /-- A function whose domain is a closed interval `[a, b]`. -/
  function : ∀ x ∈ Icc partition.a partition.b, α
  /-- Ensure the function is constant on each open subinterval of `p`. -/
  const_open_subintervals :
    ∀ (hI : I ∈ partition.openSubintervals), ∃ c : α, ∀ (hy : y ∈ I),
      function y (Partition.mem_open_subinterval_mem_closed_interval hI hy) = c

namespace StepFunction

/--
The locus of points between the `x`-axis and the function.
-/
def toSet [Preorder α] [@DecidableRel α LT.lt]
  (s : StepFunction α) : Set (α × α) := sorry

end StepFunction

end Set.Intervals