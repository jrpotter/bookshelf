import Common.Nat.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

/-! # Enderton.Logic.Chapter_1

Sentential Logic
-/

namespace Enderton.Logic.Chapter_1

/--
An abstract representation of a well-formed formula as defined by Enderton.
-/
inductive Wff where
  |   SS : Nat → Wff        -- e.g. **S**entence **S**ymbol `Aₙ`
  |  Not : Wff → Wff        -- e.g. `(¬ α)`
  |  And : Wff → Wff → Wff  -- e.g. `(α ∧ β)`
  |   Or : Wff → Wff → Wff  -- e.g. `(α ∨ β)`
  | Cond : Wff → Wff → Wff  -- e.g. `(α → β)`
  |  Iff : Wff → Wff → Wff  -- e.g. `(α ↔ β)`

namespace Wff

/--
Returns the length of the expression, including symbols.
-/
def length : Wff → ℕ
  | Wff.SS   _     => 1
  | Wff.Not  e     => length e + 3
  | Wff.And  e₁ e₂
  | Wff.Or   e₁ e₂
  | Wff.Cond e₁ e₂
  | Wff.Iff  e₁ e₂ => length e₁ + length e₂ + 3

/--
Every well-formed formula has a positive length.
-/
theorem length_gt_zero (φ : Wff)
  : length φ > 0 := by
  unfold length
  match φ with
  |   SS _
  |  Not _
  |  And _ _
  |   Or _ _
  | Cond _ _
  |  Iff _ _ => simp

end Wff

/-! #### Exercise 1.1.2

Show that there are no wffs of length `2`, `3`, or `6`, but that any other
positive length is possible.
-/

section Exercise_1_1_2

private lemma eq_3_by_cases (m n : ℕ) (h : m + n = 3)
  : m = 0 ∧ n = 3 ∨
    m = 1 ∧ n = 2 ∨
    m = 2 ∧ n = 1 ∨
    m = 3 ∧ n = 0 := by
  have m_le_3 : m ≤ 3 := by
    have : m = 3 - n := Eq.symm $ Nat.sub_eq_of_eq_add (Eq.symm h)
    rw [this]
    norm_num
  apply Or.elim (Nat.lt_or_eq_of_le m_le_3)
  · intro hm₁
    apply Or.elim (Nat.lt_or_eq_of_lt hm₁)
    · intro hm₂
      apply Or.elim (Nat.lt_or_eq_of_lt hm₂)
      · intro hm₃
        refine Or.elim (Nat.lt_or_eq_of_lt hm₃) (by simp) ?_
        intro m_eq_0
        rw [m_eq_0, zero_add] at h
        left
        exact ⟨m_eq_0, h⟩
      · intro m_eq_1
        rw [m_eq_1, add_comm] at h
        norm_num at h
        right; left
        exact ⟨m_eq_1, h⟩
    · intro m_eq_2
      rw [m_eq_2, add_comm] at h
      norm_num at h
      right; right; left
      exact ⟨m_eq_2, h⟩
  · intro m_eq_3
    rw [m_eq_3, add_comm] at h
    norm_num at h
    right; right; right
    exact ⟨m_eq_3, h⟩

theorem exercise_1_1_2_i (φ : Wff)
  : φ.length ≠ 2 ∧ φ.length ≠ 3 ∧ φ.length ≠ 6 := by
  induction φ with
  | SS c =>
    unfold Wff.length
    simp
  | Not e ih =>
    unfold Wff.length
    refine ⟨by norm_num, ?_, ?_⟩
    · intro h
      norm_num at h
      have := e.length_gt_zero
      rw [h] at this
      simp at this
    · intro h
      norm_num at h
      rw [h] at ih
      simp at ih
  | And  e₁ e₂ ih₁ ih₂
  | Or   e₁ e₂ ih₁ ih₂
  | Cond e₁ e₂ ih₁ ih₂
  | Iff  e₁ e₂ ih₁ ih₂ =>
    unfold Wff.length
    refine ⟨by norm_num, ?_, ?_⟩
    · intro h
      norm_num at h
      have := e₁.length_gt_zero
      rw [h.left] at this
      simp at this
    · intro h
      norm_num at h
      apply Or.elim (eq_3_by_cases e₁.length e₂.length h)
      · intro h₁
        have := e₁.length_gt_zero
        rw [h₁.left] at this
        simp at this
      · intro h₁
        apply Or.elim h₁
        · intro h₂
          exact absurd h₂.right ih₂.left
        intro h₂
        apply Or.elim h₂
        · intro h₃
          exact absurd h₃.left ih₁.left
        intro h₃
        exact absurd h₃.left ih₁.right.left

theorem exercise_1_1_2_ii (n : ℕ) (h : n ≠ 2 ∧ n ≠ 3 ∧ n ≠ 6)
  : ∃ φ : Wff, φ.length = n := by
  let φ₁ := Wff.SS 1
  let φ₂ := Wff.And φ₁ (Wff.SS 2)
  let φ₃ := Wff.And φ₂ (Wff.SS 3)
  sorry

end Exercise_1_1_2

/-! #### Exercise 1.1.3

Let `α` be a wff; let `c` be the number of places at which binary connective
symbols (`∧`, `∨`, `→`, `↔`) occur in `α`; let `s` be the number of places at
which sentence symbols occur in `α`. (For example, if `α` is `(A → (¬ A))` then
`c = 1` and `s = 2`.) Show by using the induction principle that `s = c + 1`.
-/

section Exercise_1_1_3

private def binary_symbol_count : Wff → ℕ
  | Wff.SS   _     => 0
  | Wff.Not  e     => binary_symbol_count e
  | Wff.And  e₁ e₂
  | Wff.Or   e₁ e₂
  | Wff.Cond e₁ e₂
  | Wff.Iff  e₁ e₂ => binary_symbol_count e₁ + binary_symbol_count e₂ + 1

private def sentence_symbol_count : Wff → ℕ
  | Wff.SS   _     => 1
  | Wff.Not  e     => sentence_symbol_count e
  | Wff.And  e₁ e₂
  | Wff.Or   e₁ e₂
  | Wff.Cond e₁ e₂
  | Wff.Iff  e₁ e₂ => sentence_symbol_count e₁ + sentence_symbol_count e₂

theorem exercise_1_1_3 (φ : Wff)
  : sentence_symbol_count φ = binary_symbol_count φ + 1 := by
  sorry

end Exercise_1_1_3

end Enderton.Logic.Chapter_1
