import Mathlib.Data.Real.Basic

/-! # Common.Real.Sequence.Arithmetic

A characterization of an arithmetic sequence, i.e. a sequence with a common
difference between each term.
-/

namespace Real

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
  | succ n ih =>
    calc
      termRecursive seq (Nat.succ n)
      _ = seq.Δ + seq.termRecursive n := rfl
      _ = seq.Δ + seq.termClosed n := by rw [ih]
      _ = seq.Δ + (seq.a₀ + seq.Δ * n) := rfl
      _ = seq.a₀ + seq.Δ * (↑n + 1) := by ring
      _ = seq.a₀ + seq.Δ * ↑(n + 1) := by simp
      _ = termClosed seq (n + 1) := rfl

/--
A term is equal to the next in the sequence minus the common difference.
-/
theorem term_closed_sub_succ_delta {seq : Arithmetic}
  : seq.termClosed n = seq.termClosed (n + 1) - seq.Δ :=
  calc
    seq.termClosed n
    _ = seq.a₀ + seq.Δ * n := rfl
    _ = seq.a₀ + seq.Δ * n + seq.Δ - seq.Δ := by rw [add_sub_cancel]
    _ = seq.a₀ + seq.Δ * (↑n + 1) - seq.Δ := by ring_nf
    _ = seq.a₀ + seq.Δ * ↑(n + 1) - seq.Δ := by simp only [Nat.cast_add, Nat.cast_one]
    _ = seq.termClosed (n + 1) - seq.Δ := rfl

/--
The summation of the first `n + 1` terms of an arithmetic sequence.

This function calculates the sum directly.
-/
noncomputable def sumClosed (seq : Arithmetic) (n : Nat) : Real :=
  (n + 1) * (seq.a₀ + seq.termClosed n) / 2

/--
The summation of the first `n + 1` terms of an arithmetic sequence.

This function calculates the sum recursively.
-/
def sumRecursive : Arithmetic → Nat → Real
  | seq,       0 => seq.a₀
  | seq, (n + 1) => seq.termClosed (n + 1) + seq.sumRecursive n

/--
Simplify a summation of terms found in the proof of `sum_recursive_closed`.
-/
private lemma sub_delta_summand_eq_two_mul_a₀ {seq : Arithmetic}
  : seq.a₀ + seq.termClosed (n + 1) - (n + 1) * seq.Δ = 2 * seq.a₀ :=
  calc
    seq.a₀ + seq.termClosed (n + 1) - (n + 1) * seq.Δ
    _ = seq.a₀ + (seq.a₀ + seq.Δ * ↑(n + 1)) - (n + 1) * seq.Δ := rfl
    _ = seq.a₀ + seq.a₀ + seq.Δ * ↑(n + 1) - (n + 1) * seq.Δ := by rw [←add_assoc]
    _ = seq.a₀ + seq.a₀ + seq.Δ * (n + 1) - (n + 1) * seq.Δ := by simp only [Nat.cast_add, Nat.cast_one]
    _ = 2 * seq.a₀ := by ring_nf

/--
The recursive and closed definitions of the sum of an arithmetic sequence agree
with one another.
-/
theorem sum_recursive_closed (seq : Arithmetic) (n : Nat)
  : seq.sumRecursive n = seq.sumClosed n := by
  induction n with
  | zero =>
    unfold sumRecursive sumClosed termClosed
    norm_num
  | succ n ih =>
    calc
      seq.sumRecursive (n + 1)
      _ = seq.termClosed (n + 1) + seq.sumRecursive n := rfl
      _ = seq.termClosed (n + 1) + seq.sumClosed n := by rw [ih]
      _ = seq.termClosed (n + 1) + ((n + 1) * (seq.a₀ + seq.termClosed n)) / 2 := rfl
      _ = (2 * seq.termClosed (n + 1) + n * seq.a₀ + n * seq.termClosed n + seq.a₀ + seq.termClosed n) / 2 := by ring_nf
      _ = (2 * seq.termClosed (n + 1) + n * seq.a₀ + n * (seq.termClosed (n + 1) - seq.Δ) + seq.a₀ + (seq.termClosed (n + 1) - seq.Δ)) / 2 := by rw [@term_closed_sub_succ_delta n]
      _ = (2 * seq.termClosed (n + 1) + n * seq.a₀ + n * seq.termClosed (n + 1) + (seq.a₀ + seq.termClosed (n + 1) - (n + 1) * seq.Δ)) / 2 := by ring_nf
      _ = (2 * seq.termClosed (n + 1) + n * seq.a₀ + n * seq.termClosed (n + 1) + 2 * seq.a₀) / 2 := by rw [sub_delta_summand_eq_two_mul_a₀]
      _ = ((n + 1) + 1) * (seq.a₀ + seq.termClosed (n + 1)) / 2 := by ring_nf
      _ = (↑(n + 1) + 1) * (seq.a₀ + seq.termClosed (n + 1)) / 2 := by simp only [Nat.cast_add, Nat.cast_one]
      _ = seq.sumClosed (n + 1) := rfl

end Real.Arithmetic