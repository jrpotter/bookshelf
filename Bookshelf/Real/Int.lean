import Mathlib.Data.Real.Basic

namespace Real

/--
Check whether a real number is an integer.
-/
def isInt (x : ℝ) := x = Int.floor x

end Real