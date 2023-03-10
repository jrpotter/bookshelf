/-
# References

1. Levin, Oscar. Discrete Mathematics: An Open Introduction. 3rd ed., n.d.
   https://discrete.openmathbooks.org/pdfs/dmoi3-tablet.pdf.
-/

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/--[1]
A 0th-indexed geometric sequence.
-/
structure Geometric where
  a₀ : Int
  r : Int

namespace Geometric

/--[1]
The value of the `n`th term of an geometric sequence.
-/
def termClosed (seq : Geometric) (n : Nat) : Int := seq.a₀ * seq.r ^ n

/--[1]
The value of the `n`th term of an geometric sequence.
-/
def termRecursive : Geometric → Nat → Int
  | seq,       0 => seq.a₀
  | seq, (n + 1) => seq.r * (seq.termRecursive n)

/--[1]
The recursive definition and closed definitions of a geometric sequence are
equivalent.
-/
theorem term_recursive_closed (seq : Geometric) (n : Nat)
        : seq.termRecursive n = seq.termClosed n :=
  Nat.recOn
    n
    (by unfold termClosed termRecursive; norm_num)
    (fun n ih => calc
      seq.termRecursive (n + 1)
          = seq.r * (seq.termRecursive n) := rfl
        _ = seq.r * (seq.termClosed n) := by rw [ih]
        _ = seq.r * (seq.a₀ * seq.r ^ n) := rfl
        _ = seq.a₀ * seq.r ^ (n + 1) := by ring
        _ = seq.termClosed (n + 1) := rfl)

/--[1]
Summation of the first `n` terms of a geometric sequence.
-/
def sum : Geometric → Nat → Int
  |   _,       0 => 0
  | seq, (n + 1) => seq.termClosed n + seq.sum n

end Geometric