import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/--
A `0th`-indexed geometric sequence.
-/
structure Geometric where
  a₀ : Real
  r : Real

namespace Geometric

/--
Returns the value of the `n`th term of a geometric sequence.

This function calculates the value of this term directly. Keep in mind the
sequence is `0`th-indexed.
-/
def termClosed (seq : Geometric) (n : Nat) : Real :=
  seq.a₀ * seq.r ^ n

/--
Returns the value of the `n`th term of a geometric sequence.

This function calculates the value of this term recursively. Keep in mind the
sequence is `0`th-indexed.
-/
def termRecursive : Geometric → Nat → Real
  | seq,       0 => seq.a₀
  | seq, (n + 1) => seq.r * (seq.termRecursive n)

/--
The recursive and closed term definitions of a geometric sequence agree with
one another.
-/
theorem term_recursive_closed (seq : Geometric) (n : Nat)
  : seq.termRecursive n = seq.termClosed n := by
  induction n with
  | zero => unfold termClosed termRecursive; norm_num
  | succ n ih => calc
      seq.termRecursive (n + 1)
      _ = seq.r * (seq.termRecursive n) := rfl
      _ = seq.r * (seq.termClosed n) := by rw [ih]
      _ = seq.r * (seq.a₀ * seq.r ^ n) := rfl
      _ = seq.a₀ * seq.r ^ (n + 1) := by ring
      _ = seq.termClosed (n + 1) := rfl

/--
The summation of the first `n + 1` terms of a geometric sequence.

This function calculates the sum directly.
-/
noncomputable def sum_closed_ratio_neq_one (seq : Geometric) (n : Nat)
  : seq.r ≠ 1 → Real :=
  fun _ => (seq.a₀ * (1 - seq.r ^ (n + 1))) / (1 - seq.r)

/--
The summation of the first `n + 1` terms of a geometric sequence.

This function calculates the sum recursively.
-/
def sum_recursive : Geometric → Nat → Real
  | seq,       0 => seq.a₀
  | seq, (n + 1) => seq.termClosed (n + 1) + seq.sum_recursive n

/--
The recursive and closed definitions of the sum of a geometric sequence agree
with one another.
-/
theorem sum_recursive_closed (seq : Geometric) (n : Nat) (p : seq.r ≠ 1)
  : sum_recursive seq n = sum_closed_ratio_neq_one seq n p := by
  have h : 1 - seq.r ≠ 0 := by
    intro h
    rw [sub_eq_iff_eq_add, zero_add] at h
    exact False.elim (p (Eq.symm h))
  induction n with
  | zero =>
    unfold sum_recursive sum_closed_ratio_neq_one
    simp
    rw [mul_div_assoc, div_self h, mul_one] 
  | succ n ih =>
    calc
      sum_recursive seq (n + 1)
      _ = seq.termClosed (n + 1) + seq.sum_recursive n := rfl
      _ = seq.termClosed (n + 1) + sum_closed_ratio_neq_one seq n p := by rw [ih]
      _ = seq.a₀ * seq.r ^ (n + 1) + (seq.a₀ * (1 - seq.r ^ (n + 1))) / (1 - seq.r) := rfl
      _ = seq.a₀ * seq.r ^ (n + 1) * (1 - seq.r) / (1 - seq.r) + (seq.a₀ * (1 - seq.r ^ (n + 1))) / (1 - seq.r) := by rw [mul_div_cancel _ h]
      _ = (seq.a₀ * (1 - seq.r ^ (n + 1 + 1))) / (1 - seq.r) := by ring_nf
      _ = sum_closed_ratio_neq_one seq (n + 1) p := rfl

end Geometric
