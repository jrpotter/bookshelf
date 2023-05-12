import Mathlib.Data.Set.Basic

/-! # Common.Set.Basic

Additional theorems and definitions useful in the context of sets.
-/

namespace Set

/-
The Minkowski sum of two sets `s` and `t` is the set
`s + t = { a + b : a ∈ s, b ∈ t }`.
-/
def minkowskiSum {α : Type u} [Add α] (s t : Set α) :=
  { x | ∃ a ∈ s, ∃ b ∈ t, x = a + b }

/--
The sum of two sets is nonempty **iff** the summands are nonempty.
-/
theorem nonempty_minkowski_sum_iff_nonempty_add_nonempty {α : Type u} [Add α]
  {s t : Set α}
  : (minkowskiSum s t).Nonempty ↔ s.Nonempty ∧ t.Nonempty := by
  apply Iff.intro
  · intro h
    have ⟨x, hx⟩ := h
    have ⟨a, ⟨ha, ⟨b, ⟨hb, _⟩⟩⟩⟩ := hx
    apply And.intro
    · exact ⟨a, ha⟩
    · exact ⟨b, hb⟩
  · intro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨a + b, ⟨a, ⟨ha, ⟨b, ⟨hb, rfl⟩⟩⟩⟩⟩

/--
The characteristic function of a set `S`.

It returns `1` if the specified input belongs to `S` and `0` otherwise.
-/
def characteristic (S : Set α) (x : α) [Decidable (x ∈ S)] : Nat :=
  if x ∈ S then 1 else 0

end Set