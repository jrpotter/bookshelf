/-
# References

1. Enderton, Herbert B. A Mathematical Introduction to Logic. 2nd ed. San Diego:
   Harcourt/Academic Press, 2001.
-/

import Mathlib.Tactic.Ring

universe u

/--[1]
An n-tuple is defined recursively as:

  ⟨x₁, ..., xₙ₊₁⟩ = ⟨⟨x₁, ..., xₙ⟩, xₙ₊₁⟩

As [1] notes, it is also useful to define ⟨x⟩ = x.
--/
inductive Tuple (α : Type u) : Nat → Type u where
  | nil : Tuple α 0
  | cons : {n : Nat} → Tuple α n → α → Tuple α (n + 1)

syntax (priority := high) "⟨" term,+ "⟩" : term

macro_rules
  | `(⟨$x⟩) => `(Tuple.cons Tuple.nil $x)
  | `(⟨$xs:term,*, $x⟩) => `(Tuple.cons ⟨$xs,*⟩ $x)

namespace Tuple

/--
Returns the value at the nth-index of the given tuple.
-/
def index (t : Tuple α n) (m : Nat) : 1 ≤ m ∧ m ≤ n → α := by
  intro h
  cases t
  · case nil =>
    have ff : 1 ≤ 0 := Nat.le_trans h.left h.right
    ring_nf at ff
    exact False.elim ff
  . case cons n' init last =>
    by_cases k : m = n' + 1
    · exact last
    · exact index init m (And.intro h.left (by
        have h₂ : m + 1 ≤ n' + 1 := Nat.lt_of_le_of_ne h.right k
        norm_num at h₂
        exact h₂))

-- TODO: Prove the following theorem

theorem eq_by_index (t₁ t₂ : Tuple α n)
  : (t₁ = t₂) ↔ (∀ i : Nat, 1 ≤ i ∧ i ≤ n → index t₁ i = index t₂ i) := by
  apply Iff.intro
  · sorry
  · sorry

-- TODO: [1] Lemma 0A

end Tuple