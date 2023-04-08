import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/--[1]
A 0th-indexed arithmetic sequence.
-/
structure Arithmetic where
  a₀ : Int
  Δ : Int

namespace Arithmetic

/--[1]
Returns the value of the `n`th term of an arithmetic sequence.
-/
def termClosed (seq : Arithmetic) (n : Nat) : Int := seq.a₀ + seq.Δ * n

/--[1]
Returns the value of the `n`th term of an arithmetic sequence.
-/
def termRecursive : Arithmetic → Nat → Int
  | seq,       0 => seq.a₀
  | seq, (n + 1) => seq.Δ + seq.termRecursive n

/--[1]
The recursive definition and closed definitions of an arithmetic sequence are
equivalent.
-/
theorem term_recursive_closed (seq : Arithmetic) (n : Nat)
        : seq.termRecursive n = seq.termClosed n := by
  induction n with
  | zero => unfold termRecursive termClosed; norm_num
  | succ n ih => calc
      termRecursive seq (Nat.succ n)
        = seq.Δ + seq.termRecursive n := rfl
      _ = seq.Δ + seq.termClosed n := by rw [ih]
      _ = seq.Δ + (seq.a₀ + seq.Δ * n) := rfl
      _ = seq.a₀ + seq.Δ * (n + 1) := by ring
      _ = termClosed seq (n + 1) := rfl

/--[1]
Summation of the first `n` terms of an arithmetic sequence.
-/
def sum : Arithmetic → Nat → Int
  |   _,       0 => 0
  | seq, (n + 1) => seq.termClosed n + seq.sum n

end Arithmetic
