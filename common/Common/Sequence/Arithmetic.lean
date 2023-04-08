import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/--
A `0`th-indexed arithmetic sequence.
-/
structure Arithmetic where
  a₀ : Real
  Δ : Real

namespace Arithmetic

/--
Returns the value of the `n`th term of an arithmetic sequence.

This function calculates the value of this term directly. Keep in mind the
sequence is `0`th-indexed.
-/
def termClosed (seq : Arithmetic) (n : Nat) : Real :=
  seq.a₀ + seq.Δ * n

/--
Returns the value of the `n`th term of an arithmetic sequence.

This function calculates the value of this term recursively. Keep in mind the
sequence is `0`th-indexed.
-/
def termRecursive : Arithmetic → Nat → Real
  | seq,       0 => seq.a₀
  | seq, (n + 1) => seq.Δ + seq.termRecursive n

/--
The recursive and closed term definitions of an arithmetic sequence agree with
one another.
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
      _ = seq.a₀ + seq.Δ * (↑n + 1) := by ring
      _ = seq.a₀ + seq.Δ * ↑(n + 1) := by simp
      _ = termClosed seq (n + 1) := rfl

/--
The summation of the first `n + 1` terms of an arithmetic sequence.

This function calculates the sum directly.
-/
noncomputable def sum_closed (seq : Arithmetic) (n : Nat) : Real :=
  ((n + 1) * (seq.a₀ + seq.termClosed n)) / 2

/--
The summation of the first `n + 1` terms of an arithmetic sequence.

This function calculates the sum recursively.
-/
def sum_recursive : Arithmetic → Nat → Real
  |   _,       0 => 0
  | seq, (n + 1) => seq.termClosed (n + 1) + seq.sum_recursive n

/--
The recursive and closed definitions of the sum of an arithmetic sequence agree
with one another.
-/
theorem sum_recursive_closed (seq : Arithmetic) (n : Nat)
  : sum_recursive seq n = sum_closed seq n :=
  sorry

end Arithmetic
