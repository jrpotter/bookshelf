import Common.List.Basic
import Common.Set.Intervals.Partition

/-! # Common.Set.Intervals.StepFunction

Characterization of step functions.
-/

namespace Set.Intervals

open Partition

/--
A function `f`, whose domain is a closed interval `[a, b]`, is a `StepFunction`
if there exists a `Partition` `P = {x₀, x₁, …, xₙ}` of `[a, b]` such that `f` is
constant on each open subinterval of `P`.
-/
structure StepFunction (α : Type _) [Preorder α] [@DecidableRel α LT.lt] where
  p : Partition α
  toFun : ∀ x ∈ p.toIcc, α
  const_open_subintervals :
    ∀ (hI : I ∈ p.openSubintervals), ∃ c : α, ∀ (hy : y ∈ I),
      toFun y (mem_open_subinterval_mem_closed_interval hI hy) = c

namespace StepFunction

/--
The locus of points between the `x`-axis and the function.
-/
def toSet [Preorder α] [@DecidableRel α LT.lt]
  (s : StepFunction α) : Set (α × α) := sorry

end StepFunction

end Set.Intervals