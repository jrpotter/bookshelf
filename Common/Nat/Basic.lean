import Mathlib.Data.Set.Basic
import Mathlib.Tactic.NormNum

namespace Nat

/--
If `n < m⁺`, then `n < m` or `n = m`.
-/
theorem lt_or_eq_of_lt {n m : Nat} (h : n < m.succ) : n < m ∨ n = m :=
  lt_or_eq_of_le (lt_succ.mp h)

/--
The following cancellation law holds for `m`, `n`, and `p` in `ω`:
```
m ⬝ p = n ⬝ p ∧ p ≠ 0 → m = n
```
-/
theorem mul_right_cancel (m n p : ℕ) (hp : 0 < p) : m * p = n * p → m = n := by
  intro hmn
  match @trichotomous ℕ LT.lt _ m n with
  | Or.inl h =>
    have : m * p < n * p := Nat.mul_lt_mul_of_pos_right h hp
    rw [hmn] at this
    simp at this
  | Or.inr (Or.inl h) => exact h
  | Or.inr (Or.inr h) =>
    have : n * p < m * p := Nat.mul_lt_mul_of_pos_right h hp
    rw [hmn] at this
    simp at this

end Nat