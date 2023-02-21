/-
# References

1. Enderton, Herbert B. A Mathematical Introduction to Logic. 2nd ed. San Diego:
   Harcourt/Academic Press, 2001.
2. Axler, Sheldon. Linear Algebra Done Right. Undergraduate Texts in
   Mathematics. Cham: Springer International Publishing, 2015.
   https://doi.org/10.1007/978-3-319-11080-6.
-/

import Mathlib.Tactic.Ring

universe u

/--[1]
An `n`-tuple is defined recursively as:

  `⟨x₁, ..., xₙ₊₁⟩ = ⟨⟨x₁, ..., xₙ⟩, xₙ₊₁⟩`

As [1] notes, it is useful to define `⟨x⟩ = x`. It is not clear this would be
possible in Lean though.

Though [1] does not describe a notion of an empty tuple, [2] does (though under
the name of a "list").
--/
inductive Tuple : (α : Type u) → Nat → Type u where
  | nil : Tuple α 0
  | snoc : {n : Nat} → Tuple α n → α → Tuple α (n + 1)

syntax (priority := high) "⟨" term,+ "⟩" : term

-- Notice the ambiguity this syntax introduces. For example, pattern `⟨a, b⟩`
-- could refer to a `2`-tuple or an `n`-tuple, where `a` is an `(n-1)`-tuple.
macro_rules
  | `(⟨$x⟩) => `(Tuple.snoc Tuple.nil $x)
  | `(⟨$xs:term,*, $x⟩) => `(Tuple.snoc ⟨$xs,*⟩ $x)

namespace Tuple

def length : Tuple α n → Nat
  | Tuple.nil => 0
  | Tuple.snoc init _ => length init + 1

theorem nil_length_zero : length (@Tuple.nil α) = 0 :=
  rfl

theorem snoc_length_succ : length (Tuple.snoc init last) = length init + 1 :=
  rfl

theorem tuple_length {n : Nat} (t : Tuple α n) : length t = n :=
  Tuple.recOn t nil_length_zero
    fun _ _ ih => by
      rw [snoc_length_succ]
      norm_num
      exact ih

def head : {n : Nat} → Tuple α n → n ≥ 1 → α
  | n + 1, Tuple.snoc init last, h => by
    by_cases k : 0 = n
    · exact last
    · have h' : 0 ≤ n := Nat.le_of_succ_le_succ h
      exact head init (Nat.lt_of_le_of_ne h' k)

def last : Tuple α n → n ≥ 1 → α
  | Tuple.snoc _ last, _ => last

def index : {n : Nat} → Tuple α n → (k : Nat) → 1 ≤ k ∧ k ≤ n → α
  | 0, _, m, h => by
    have ff : 1 ≤ 0 := Nat.le_trans h.left h.right
    ring_nf at ff
    exact False.elim ff
  | n + 1, Tuple.snoc init last, k, h => by
    by_cases hₖ : k = n + 1
    · exact last
    · exact index init k $ And.intro
        h.left
        (Nat.le_of_lt_succ $ Nat.lt_of_le_of_ne h.right hₖ)

/-

-- TODO: Prove `eq_by_index`.
-- TODO: Prove Lemma 0A [1].

theorem eq_by_index (t₁ t₂ : Tuple α n)
  : (t₁ = t₂) ↔ (∀ i : Nat, (p : 1 ≤ i ∧ i ≤ n) → index t₁ i p = index t₂ i p) := by
  apply Iff.intro
  · intro teq i hᵢ
    sorry
  · sorry

-/

end Tuple
