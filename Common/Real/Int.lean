import Mathlib.Data.Real.Basic

/-! # Common.Real.Int

Additional theorems and definitions useful in the context of integers.
-/

namespace Real

/--
Check whether a real number is an integer.
-/
def isInt (x : ℝ) := x = Int.floor x

end Real