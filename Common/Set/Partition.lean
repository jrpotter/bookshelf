import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.Set.Intervals.Basic

import Common.List.Basic
import Common.List.NonEmpty
import Common.Set.Interval

/-! # Common.Set.Partition

Additional theorems and definitions useful in the context of sets.
-/

namespace Set

/--
A `Partition` is a finite subset of `[a, b]` containing points `a` and `b`.

We use a `List.NonEmpty` internally to ensure the existence of at least one
`Interval`, which cannot be empty. Thus our `Partition` can never be empty.
The intervals are sorted via the `connected` proposition.
-/
structure Partition (α : Type _) [LT α] where
  ivls : List.NonEmpty (Interval α)
  connected : ∀ I ∈ ivls.toList.pairwise (·.right = ·.left), I

namespace Partition

/--
Return the left-most endpoint of the `Partition`.
-/
def left [LT α] (p : Partition α) := p.ivls.head.left

/--
Return the right-most endpoint of the `Partition`.
-/
def right [LT α] (p : Partition α) := p.ivls.last.right

end Partition

end Set