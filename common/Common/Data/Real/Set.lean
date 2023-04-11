import Mathlib.Data.Real.Basic

namespace Real

/--
The Minkowski sum of two sets `s` and `t` is the set
`s + t = { a + b : a ∈ s, b ∈ t }`.
-/
def minkowski_sum (s t : Set ℝ) :=
  { x | ∃ a ∈ s, ∃ b ∈ t, x = a + b }

end Real
