import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Intervals.Basic

import Common.List.Basic

/-! # Common.Set.Interval

A representation of a range of values.
-/

namespace Set

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

end Set