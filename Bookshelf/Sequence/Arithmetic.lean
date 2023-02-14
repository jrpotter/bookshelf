import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/--
A 0th-indexed arithmetic sequence.
-/
structure Arithmetic where
  a₀ : Int
  Δ : Int

namespace Arithmetic

/--
Returns the value of the `n`th term of an arithmetic sequence.
-/
def termClosed (seq : Arithmetic) (n : Nat) : Int := seq.a₀ + seq.Δ * n

/--
Returns the value of the `n`th term of an arithmetic sequence.
-/
def termRecursive : Arithmetic → Nat → Int
  | seq,       0 => seq.a₀
  | seq, (n + 1) => seq.Δ + seq.termRecursive n

/--
The recursive definition and closed definitions of an arithmetic sequence are
equivalent.
-/
theorem term_recursive_closed (seq : Arithmetic) (n : Nat)
        : seq.termRecursive n = seq.termClosed n :=
  Nat.recOn
    n
    (by unfold termRecursive termClosed; norm_num)
    (fun n ih => calc
      termRecursive seq (Nat.succ n)
          = seq.Δ + seq.termRecursive n := rfl
        _ = seq.Δ + seq.termClosed n := by rw [ih]
        _ = seq.Δ + (seq.a₀ + seq.Δ * n) := rfl
        _ = seq.a₀ + seq.Δ * (n + 1) := by ring
        _ = termClosed seq (n + 1) := rfl)

/--
Summation of the first `n` terms of an arithmetic sequence.
-/
def sum : Arithmetic → Nat → Int
  |   _,       0 => 0
  | seq, (n + 1) => seq.termClosed n + seq.sum n

/--
The closed formula of the summation of the first `n` terms of an arithmetic
series.
--/
theorem sum_closed_formula (seq : Arithmetic) (n : Nat)
        : seq.sum n = (n / 2) * (seq.a₀ + seq.termClosed (n - 1)) :=
  Nat.recOn
    n
    (by unfold sum termClosed; norm_num)
    (fun n ih => calc
      sum seq n.succ
          = seq.termClosed n + seq.sum n := rfl
        _ = seq.termClosed n + (n / 2 * (seq.a₀ + seq.termClosed (n - 1))) := by rw [ih]
        _ = seq.a₀ + seq.Δ * n + (n / 2 * (seq.a₀ + (seq.a₀ + seq.Δ * ↑(n - 1)))) := rfl
        -- TODO: To continue, need to find how to deal with division.
        _ = ↑(n + 1) / 2 * (seq.a₀ + seq.termClosed n) := by sorry)

end Arithmetic