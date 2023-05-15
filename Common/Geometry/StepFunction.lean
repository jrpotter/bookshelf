import Common.Finset
import Common.Geometry.Rectangle.Orthogonal
import Common.List.Basic
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

Instead of maintaining a function from `[a, b]` to `ℝ`, we instead maintain a
function that maps each `Partition` index to some constant value. 
-/
structure StepFunction where
  p : Partition ℝ
  toFun : Fin p.ivls.length → ℝ

namespace StepFunction

/--
The ordinate set of the `StepFunction`.
-/
def toSet (sf : StepFunction) : Set Point :=
  ⋃ i ∈ Finset.finRange sf.p.ivls.length,
    let I := sf.p.ivls[i]
    Rectangle.Orthogonal.toSet
      ⟨
        {
          tl := ⟨I.left, sf.toFun i⟩,
          bl := ⟨I.left, 0⟩,
          br := ⟨I.right, 0⟩,
          has_right_angle := sorry
        },
        by simp
      ⟩

end StepFunction

end Geometry