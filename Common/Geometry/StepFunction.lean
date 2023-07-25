import Common.Finset
import Common.Geometry.Rectangle.Orthogonal
import Common.List.Basic
import Common.List.NonEmpty

/-! # Common.Geometry.StepFunction

Characterization of step functions.
-/

namespace Geometry

/--
An interval defines a range of values, characterized by a "left" value and a
"right" value. We require these values to be distinct; we do not support the
notion of an empty interval.
-/
structure Interval (α : Type _) [LT α] where
  left : α
  right : α
  h : left < right

namespace Interval

/--
Computes the size of the interval.
-/
def size [LT α] [Sub α] (i : Interval α) : α := i.right - i.left

/--
Computes the midpoint of the interval.
-/
def midpoint [LT α] [Add α] [HDiv α ℝ α] (i : Interval α) : α :=
  (i.left + i.right) / (2 : ℝ)

/--
Convert an `Interval` into a `Set.Ico`.
-/
def toIco [Preorder α] (i : Interval α) : Set α := Set.Ico i.left i.right

/--
Convert an `Interval` into a `Set.Ioc`.
-/
def toIoc [Preorder α] (i : Interval α) : Set α := Set.Ioc i.left i.right

/--
Convert an `Interval` into a `Set.Icc`.
-/
def toIcc [Preorder α] (i : Interval α) : Set α := Set.Icc i.left i.right

/--
Convert an `Interval` into a `Set.Ioo`.
-/
def toIoo [Preorder α] (i : Interval α) : Set α := Set.Ioo i.left i.right

end Interval

/--
A function `f`, whose domain is a closed interval `[a, b]`, is a `StepFunction`
if there exists a partition `P = {x₀, x₁, …, xₙ}` of `[a, b]` such that `f` is
constant on each open subinterval of `P`.

Instead of maintaining a function from `[a, b]` to `ℝ`, we instead maintain a
function that maps each partition index to some constant value. 
-/
structure StepFunction where
  ivls : List.NonEmpty (Interval ℝ)
  connected : ∀ I ∈ ivls.toList.pairwise (·.right = ·.left), I
  toFun : Fin ivls.length → ℝ

namespace StepFunction

/--
The ordinate set of the `StepFunction`.
-/
def toSet (sf : StepFunction) : Set Point :=
  ⋃ i ∈ Finset.finRange sf.ivls.length,
    let I := sf.ivls[i]
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