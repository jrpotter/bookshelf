import Mathlib.Data.Real.Basic

/-! # Common.Real.Set.Interval

A syntactic description of the various types of continuous intervals permitted
on the real number line.
-/

/--
Representation of a closed interval.
-/
syntax (priority := high) "i[" term "," term "]" : term

macro_rules
  | `(i[$a, $b]) => `({ z | $a ≤ z ∧ z ≤ $b })

/--
Representation of an open interval.
-/
syntax (priority := high) "i(" term "," term ")" : term

macro_rules
  | `(i($a, $b)) => `({ z | $a < z ∧ z < $b })

/--
Representation of a left half-open interval.
-/
syntax (priority := high) "i(" term "," term "]" : term

macro_rules
  | `(i($a, $b]) => `({ z | $a < z ∧ z ≤ $b })

/--
Representation of a right half-open interval.
-/
syntax (priority := high) "i[" term "," term ")" : term

macro_rules
  | `(i[$a, $b)) => `({ z | $a ≤ z ∧ z < $b })