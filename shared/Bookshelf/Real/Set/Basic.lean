import Mathlib.Data.Real.Basic

namespace Real

/--
The Minkowski sum of two sets `s` and `t` is the set
`s + t = { a + b : a ∈ s, b ∈ t }`.
-/
def minkowski_sum (s t : Set ℝ) :=
  { x | ∃ a ∈ s, ∃ b ∈ t, x = a + b }

/--
The sum of two sets is nonempty if and only if the summands are nonempty.
-/
def nonempty_minkowski_sum_iff_nonempty_add_nonempty {s t : Set ℝ}
  : (minkowski_sum s t).Nonempty ↔ s.Nonempty ∧ t.Nonempty := by
  apply Iff.intro
  · intro h
    have ⟨x, hx⟩ := h
    have ⟨a, ⟨ha, ⟨b, ⟨hb, _⟩⟩⟩⟩ := hx
    apply And.intro
    · exact ⟨a, ha⟩
    · exact ⟨b, hb⟩
  · intro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨a + b, ⟨a, ⟨ha, ⟨b, ⟨hb, rfl⟩⟩⟩⟩⟩

end Real
