import Mathlib.Data.Set.Basic
import Mathlib.Tactic.NormNum

namespace Nat

/--
If `n < m⁺`, then `n < m` or `n = m`.
-/
theorem lt_or_eq_of_lt {n m : Nat} (h : n < m.succ) : n < m ∨ n = m :=
  lt_or_eq_of_le (lt_succ.mp h)

end Nat
