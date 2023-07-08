import Mathlib.Logic.Basic
import Mathlib.Tactic.Tauto

/-! # Common.Logic.Basic

Additional theorems and definitions related to basic logic.
-/

/--
The de Morgan law that distributes negation across a conjunction.
-/
theorem not_and_de_morgan : (¬(p ∧ q)) ↔ (¬p ∨ ¬q) := by
  tauto

/--
Renaming of `not_or` to indicate its relationship to de Morgan's laws.
-/
theorem not_or_de_morgan : ¬(p ∨ q) ↔ ¬p ∧ ¬q := not_or

/--
The principle of contraposition.
-/
theorem contraposition : (p → q) ↔ (¬q → ¬p) := by
  apply Iff.intro
  · intro h nq hp
    exact absurd (h hp) nq
  · intro h hp
    by_contra nq
    exact absurd hp (h nq)

/--
Universal quantification across nested set memberships can be commuted in either
order.
-/
theorem forall_mem_comm {X : Set α} {Y : Set β} (p : α → β → Prop)
  : (∀ u ∈ X, (∀ v, v ∈ Y → p u v)) = (∀ v ∈ Y, (∀ u, u ∈ X → p u v)) := by
  refine propext ?_
  apply Iff.intro
  · intro h v hv u hu
    exact h u hu v hv
  · intro h u hu v hv
    exact h v hv u hu