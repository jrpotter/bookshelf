import Common.Logic.Basic
import Common.Nat.Basic
import Mathlib.Algebra.Parity
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Setoid.Partition
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

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
Returns the length of the expression, i.e. a count of all symbols..
-/
def length : Wff → ℕ
  | Wff.SS   _     => 1
  | Wff.Not  e     => length e + 3
  | Wff.And  e₁ e₂
  | Wff.Or   e₁ e₂
  | Wff.Cond e₁ e₂
  | Wff.Iff  e₁ e₂ => length e₁ + length e₂ + 3

/--
Every `Wff` has a positive length.
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

/--
The number of sentence symbols found in the provided `Wff`.
-/
def sentenceSymbolCount : Wff → ℕ
  | Wff.SS   _     => 1
  | Wff.Not  e     => sentenceSymbolCount e
  | Wff.And  e₁ e₂
  | Wff.Or   e₁ e₂
  | Wff.Cond e₁ e₂
  | Wff.Iff  e₁ e₂ => sentenceSymbolCount e₁ + sentenceSymbolCount e₂

/--
The number of sentential connective symbols found in the provided `Wff`.
-/
def sententialSymbolCount : Wff → ℕ
  | Wff.SS   _     => 0
  | Wff.Not  e     => sententialSymbolCount e + 1
  | Wff.And  e₁ e₂
  | Wff.Or   e₁ e₂
  | Wff.Cond e₁ e₂
  | Wff.Iff  e₁ e₂ => sententialSymbolCount e₁ + sententialSymbolCount e₂ + 1

/--
The number of binary connective symbols found in the provided `Wff`.
-/
def binarySymbolCount : Wff → ℕ
  | Wff.SS   _     => 0
  | Wff.Not  e     => binarySymbolCount e
  | Wff.And  e₁ e₂
  | Wff.Or   e₁ e₂
  | Wff.Cond e₁ e₂
  | Wff.Iff  e₁ e₂ => binarySymbolCount e₁ + binarySymbolCount e₂ + 1

/--
The number of parentheses found in the provided `Wff`.
-/
def parenCount : Wff → ℕ
  | Wff.SS   _     => 0
  | Wff.Not  e     => 2 + parenCount e
  | Wff.And  e₁ e₂
  | Wff.Or   e₁ e₂
  | Wff.Cond e₁ e₂
  | Wff.Iff  e₁ e₂ => 2 + parenCount e₁ + parenCount e₂

/--
Whether or not the `Wff` contains a `¬`.
-/
def hasNotSymbol : Wff → Prop
  | Wff.SS   _     => False
  | Wff.Not  _     => True
  | Wff.And  e₁ e₂
  | Wff.Or   e₁ e₂
  | Wff.Cond e₁ e₂
  | Wff.Iff  e₁ e₂ => hasNotSymbol e₁ ∨ hasNotSymbol e₂

/--
If a `Wff` does not contain the `¬` symbol, it has the same number of sentential
connective symbols as it does binary connective symbols. In other words, the
negation symbol is the only non-binary sentential connective.
-/
lemma no_neg_sentential_count_eq_binary_count {φ : Wff} (h : ¬φ.hasNotSymbol)
  : φ.sententialSymbolCount = φ.binarySymbolCount := by
  induction φ with
  | SS _ =>
    unfold sententialSymbolCount binarySymbolCount
    rfl
  | Not  _ _ =>
    unfold hasNotSymbol at h
    exfalso
    exact h trivial
  | And  e₁ e₂ ih₁ ih₂
  | Or   e₁ e₂ ih₁ ih₂
  | Cond e₁ e₂ ih₁ ih₂
  | Iff  e₁ e₂ ih₁ ih₂ =>
    unfold hasNotSymbol at h
    rw [not_or_de_morgan] at h
    unfold sententialSymbolCount binarySymbolCount
    rw [ih₁ h.left, ih₂ h.right]

/-- #### Parentheses Count

Let `φ` be a well-formed formula and `c` be the number of places at which a
sentential connective symbol exists. Then there is `2c` parentheses in `φ`.
-/
theorem paren_count_double_sentential_count (φ : Wff)
  : φ.parenCount = 2 * φ.sententialSymbolCount := by
  induction φ with
  | SS _ =>
    unfold parenCount sententialSymbolCount
    simp
  | Not e ih =>
    unfold parenCount sententialSymbolCount
    rw [ih]
    ring
  | And  e₁ e₂ ih₁ ih₂
  | Or   e₁ e₂ ih₁ ih₂
  | Cond e₁ e₂ ih₁ ih₂
  | Iff  e₁ e₂ ih₁ ih₂ =>
    unfold parenCount sententialSymbolCount
    rw [ih₁, ih₂]
    ring

/--
The length of a `Wff` corresponds to the summation of sentence symbols,
sentential connective symbols, and parentheses.
-/
theorem length_eq_sum_symbol_count (φ : Wff)
  : φ.length = φ.sentenceSymbolCount +
               φ.sententialSymbolCount +
               φ.parenCount := by
  induction φ with
  | SS _ =>
    unfold length sentenceSymbolCount sententialSymbolCount parenCount
    simp
  | Not e ih =>
    unfold length sentenceSymbolCount sententialSymbolCount parenCount
    rw [ih]
    ac_rfl
  | And  e₁ e₂ ih₁ ih₂
  | Or   e₁ e₂ ih₁ ih₂
  | Cond e₁ e₂ ih₁ ih₂
  | Iff  e₁ e₂ ih₁ ih₂ =>
    unfold length sentenceSymbolCount sententialSymbolCount parenCount
    rw [ih₁, ih₂]
    ac_rfl

end Wff

/-! #### Exercise 1.1.2

Show that there are no wffs of length `2`, `3`, or `6`, but that any other
positive length is possible.
-/

section Exercise_1_1_2

/--
An enumeration of values `m` and `n` can take on in equation `m + n = 3`.
-/
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
  | SS _ =>
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

private def recNot : ℕ → Wff → Wff
  |     0, φ => φ
  | n + 1, φ => Wff.Not (recNot n φ)

theorem exercise_1_1_2_ii (n : ℕ) (hn : n ≠ 2 ∧ n ≠ 3 ∧ n ≠ 6)
  : ∃ φ : Wff, φ.length = n := by
  let φ₁ := Wff.SS 1
  let φ₂ := Wff.And φ₁ (Wff.SS 2)
  let φ₃ := Wff.And φ₂ (Wff.SS 3)

  let S : Set (Set { n : ℕ // n ≠ 2 ∧ n ≠ 3 ∧ n ≠ 6 }) := {
    { m | ∃ n : ℕ, (recNot n φ₁).length = m.1 },
    { m | ∃ n : ℕ, (recNot n φ₂).length = m.1 },
    { m | ∃ n : ℕ, (recNot n φ₃).length = m.1 }
  }
  have hS : Setoid.IsPartition S := by
    sorry

  sorry

end Exercise_1_1_2

/-- #### Exercise 1.1.3

Let `α` be a wff; let `c` be the number of places at which binary connective
symbols (`∧`, `∨`, `→`, `↔`) occur in `α`; let `s` be the number of places at
which sentence symbols occur in `α`. (For example, if `α` is `(A → (¬ A))` then
`c = 1` and `s = 2`.) Show by using the induction principle that `s = c + 1`.
-/
theorem exercise_1_1_3 (φ : Wff)
  : φ.sentenceSymbolCount = φ.binarySymbolCount + 1 := by
  induction φ with
  | SS _ =>
    unfold Wff.sentenceSymbolCount Wff.binarySymbolCount
    simp
  | Not e ih =>
    unfold Wff.sentenceSymbolCount Wff.binarySymbolCount
    exact ih
  | And  e₁ e₂ ih₁ ih₂
  | Or   e₁ e₂ ih₁ ih₂
  | Cond e₁ e₂ ih₁ ih₂
  | Iff  e₁ e₂ ih₁ ih₂ =>
    unfold Wff.sentenceSymbolCount Wff.binarySymbolCount
    rw [ih₁, ih₂]
    ring

/-- #### Exercise 1.1.5 (a)

Suppose that `α` is a wff not containing the negation symbol `¬`. Show that the
length of `α` (i.e., the number of symbols in the string) is odd.

*Suggestion*: Apply induction to show that the length is of the form `4k + 1`.
-/
theorem exercise_1_1_5a (α : Wff) (hα : ¬α.hasNotSymbol)
  : Odd α.length := by
  suffices ∃ k : ℕ, α.length = 4 * k + 1 by
    have ⟨k, hk⟩ := this
    unfold Odd
    exact ⟨2 * k, by rw [hk, ← mul_assoc]; norm_num⟩
  induction α with
  | SS _ =>
    refine ⟨0, ?_⟩
    unfold Wff.length
    simp
  | Not e _ =>
    unfold Wff.hasNotSymbol at hα
    exfalso
    exact hα trivial
  | And  e₁ e₂ ih₁ ih₂
  | Or   e₁ e₂ ih₁ ih₂
  | Cond e₁ e₂ ih₁ ih₂
  | Iff  e₁ e₂ ih₁ ih₂  =>
    unfold Wff.hasNotSymbol at hα
    rw [not_or_de_morgan] at hα
    have ⟨k₁, hk₁⟩ := ih₁ hα.left
    have ⟨k₂, hk₂⟩ := ih₂ hα.right
    refine ⟨k₁ + k₂ + 1, ?_⟩
    unfold Wff.length
    rw [hk₁, hk₂]
    ring

/-- #### Exercise 1.1.5 (b)

Suppose that `α` is a wff not containing the negation symbol `¬`. Show that more
than a quarter of the symbols are sentence symbols.

*Suggestion*: Apply induction to show that the number of sentence symbols is
`k + 1`.
-/
theorem exercise_1_1_5b (α : Wff) (hα : ¬α.hasNotSymbol)
  : α.sentenceSymbolCount > (Nat.cast α.length : ℝ) / 4 := by
  rw [
    α.length_eq_sum_symbol_count,
    Wff.paren_count_double_sentential_count α,
    Wff.no_neg_sentential_count_eq_binary_count hα,
    exercise_1_1_3 α
  ]
  generalize Wff.binarySymbolCount α = k
  simp only [
    Nat.cast_add,
    Nat.cast_one,
    Nat.cast_mul,
    Nat.cast_ofNat,
    gt_iff_lt
  ]
  ring_nf
  simp only [
    Int.ofNat_eq_coe,
    Nat.cast_one,
    Int.cast_one,
    Nat.cast_ofNat,
    one_div,
    add_lt_add_iff_right
  ]
  exact inv_lt_one (by norm_num)

/-! #### Exercise 1.2.1

Show that neither of the following two formulas tautologically implies the
other:
```
(A ↔ (B ↔ C))
((A ∧ (B ∧ C)) ∨ ((¬ A) ∧ ((¬ B) ∧ (¬ C)))).
```
*Suggestion*: Only two truth assignments are needed, not eight.
-/
section Exercise_1_2_1

private def f₁ (A B C : Prop) : Prop :=
  A ↔ (B ↔ C)

private def f₂ (A B C : Prop) : Prop :=
  ((A ∧ (B ∧ C)) ∨ ((¬ A) ∧ ((¬ B) ∧ (¬ C))))

theorem exercise_1_2_1_i
  : f₁ True False False ≠ f₂ True False False := by
  unfold f₁ f₂
  simp

theorem exercise_1_2_1_ii
  : f₁ False False False ≠ f₂ False False False := by
  unfold f₁ f₂
  simp

end Exercise_1_2_1

section Exercise_1_2_2

/-- #### Exercise 1.2.2 (a)

Is `(((P → Q) → P) → P)` a tautology?
-/
theorem exercise_1_2_2a (P Q : Prop)
  : (((P → Q) → P) → P) := by
  tauto

/-! #### Exercise 1.2.2 (b)

Define `σₖ` recursively as follows: `σ₀ = (P → Q)` and `σₖ₊₁ = (σₖ → P)`. For
which values of `k` is `σₖ` a tautology? (Part (a) corresponds to `k = 2`.)
-/

private def σ (P Q : Prop) : ℕ → Prop
  | 0 => P → Q
  | n + 1 => σ P Q n → P

theorem exercise_1_2_2b_i (P Q : Prop) {k : ℕ} (h : k > 0)
  : σ P Q (2 * k) := by
  induction k with
  | zero => simp at h
  | succ k ih =>
    by_cases hk : k = 0
    · rw [hk]
      simp only [Nat.mul_one]
      unfold σ σ σ
      exact exercise_1_2_2a P Q
    · have := ih (Nat.pos_of_ne_zero hk)
      unfold σ σ
      have hk₁ := calc 2 * k.succ
        _ = 2 * (k + 1) := rfl
        _ = 2 * k + 2 * 1 := rfl
        _ = 2 * k + 2 := by simp
      rw [hk₁]
      simp only [Nat.add_eq, add_zero]
      tauto

theorem exercise_1_2_2b_ii
  : ¬ σ True False 0 := by
  unfold σ
  simp

theorem exercise_1_2_2b_iii {k : ℕ} (h : Odd k)
  : ¬ σ False Q k := by
  by_cases hk : k = 1
  · unfold σ σ
    rw [hk]
    simp
  · have ⟨n, hn₁, hn₂⟩ : ∃ n : ℕ, k = (2 * n) + 1 ∧ n > 0 := by
      have ⟨r, hr⟩ := h
      refine ⟨r, hr, ?_⟩
      by_contra nr
      have : r = 0 := Nat.eq_zero_of_nonpos r nr
      rw [this] at hr
      simp only [mul_zero, zero_add] at hr
      exact absurd hr hk
    unfold σ
    rw [hn₁]
    simp only [Nat.add_eq, add_zero, not_forall, exists_prop, and_true]
    exact exercise_1_2_2b_i False Q hn₂

end Exercise_1_2_2

/-- #### Exercise 1.2.3 (a)

Determine whether or not `((P → Q)) ∨ (Q → P)` is a tautology.
-/
theorem exercise_1_2_3a (P Q : Prop)
  : ((P → Q) ∨ (Q → P)) := by
  tauto

/-- #### Exercise 1.2.3 (b)

Determine whether or not `((P ∧ Q) → R))` tautologically implies
`((P → R) ∨ (Q → R))`.
-/
theorem exercise_1_2_3b (P Q R : Prop)
  : ((P ∧ Q) → R) ↔ ((P → R) ∨ (Q → R)) := by
  tauto

/-! #### Exercise 1.2.5

Prove or refute each of the following assertions:

(a) If either `Σ ⊨ α` or `Σ ⊨ β`, then `Σ ⊨ (α ∨ β)`.
(b) If `Σ ⊨ (α ∨ β)`, then either `Σ ⊨ α` or `Σ ⊨ β`.
-/

theorem exercise_1_2_5a (P α β : Prop)
  : ((P → α) ∨ (P → β)) → (P → (α ∨ β)) := by
  tauto

theorem exercise_1_2_6b
  : (False ∨ True) ∧ ¬ False := by
  simp

/-! #### Exercise 1.2.15

Of the following three formulas, which tautologically implies which?
(a) `(A ↔ B)`
(b) `(¬((A → B) →(¬(B → A))))`
(c) `(((¬ A) ∨ B) ∧ (A ∨ (¬ B)))`
-/

theorem exercise_1_2_15_i (A B : Prop)
  : (A ↔ B) ↔ (¬((A → B) → (¬(B → A)))) := by
  tauto

theorem exercise_1_2_15_ii (A B : Prop)
  : (A ↔ B) ↔ (((¬ A) ∨ B) ∧ (A ∨ (¬ B))) := by
  tauto

end Enderton.Logic.Chapter_1
