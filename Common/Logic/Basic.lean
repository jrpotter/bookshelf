import Mathlib.Logic.Basic
import Mathlib.Tactic.Tauto

/-! # Common.Logic.Basic

Additional theorems and definitions related to basic logic.
-/

/--
The de Morgan law that distributes negation across a conjunction.
-/
theorem not_and_de_morgan {a b : Prop} : (¬(a ∧ b)) ↔ (¬ a ∨ ¬ b) := by
  tauto

/--
Renaming of `not_or` to indicate its relationship to de Morgan's laws.
-/
theorem not_or_de_morgan : ¬(p ∨ q) ↔ ¬p ∧ ¬q := not_or