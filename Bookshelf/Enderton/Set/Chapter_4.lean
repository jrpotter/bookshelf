import Common.Logic.Basic
import Mathlib.Data.Set.Basic

/-! # Enderton.Set.Chapter_4

Natural Numbers
-/

namespace Enderton.Set.Chapter_4

/-- #### Theorem 4C

Every natural number except `0` is the successor of some natural number.
-/
theorem theorem_4c (n : ℕ)
  : n = 0 ∨ (∃ m : ℕ, n = m.succ) := by
  match n with
  | 0 => simp
  | m + 1 => simp

/-- #### Exercise 4.1

Show that `1 ≠ 3` i.e., that `∅⁺ ≠ ∅⁺⁺⁺`.
-/
theorem exercise_4_1 : 1 ≠ 3 := by
  simp

/-- #### Exercise 4.13

Let `m` and `n` be natural numbers such that `m ⬝ n = 0`. Show that either
`m = 0` or `n = 0`.
-/
theorem exercise_4_13 (m n : ℕ) (h : m * n = 0)
  : m = 0 ∨ n = 0 := by
  by_contra nh
  rw [not_or_de_morgan] at nh
  have ⟨p, hp⟩ : ∃ p, m = p.succ := Nat.exists_eq_succ_of_ne_zero nh.left
  have ⟨q, hq⟩ : ∃ q, n = q.succ := Nat.exists_eq_succ_of_ne_zero nh.right
  have : m * n = (m * q + p).succ := calc m * n
    _ = m * q.succ := by rw [hq]
    _ = m * q + m := rfl
    _ = m * q + p.succ := by rw [hp]
    _ = (m * q + p).succ := rfl
  rw [this] at h
  simp only [Nat.succ_ne_zero] at h

/--
Call a natural number *even* if it has the form `2 ⬝ m` for some `m`.
-/
def even (n : ℕ) : Prop := ∃ m, 2 * m = n

/--
Call a natural number *odd* if it has the form `(2 ⬝ p) + 1` for some `p`.
-/
def odd (n : ℕ) : Prop := ∃ p, (2 * p) + 1 = n

/-- #### Exercise 4.14

Show that each natural number is either even or odd, but never both.
-/
theorem exercise_4_14 (n : ℕ)
  : (even n ∧ ¬ odd n) ∨ (¬ even n ∧ odd n) := by
  induction n with
  | zero =>
    left
    refine ⟨⟨0, by simp⟩, ?_⟩
    intro ⟨p, hp⟩
    simp only [Nat.zero_eq, Nat.succ_ne_zero] at hp
  | succ n ih =>
    apply Or.elim ih
    · -- Assumes `n` is even meaning `n⁺` is odd.
      intro ⟨⟨m, hm⟩, h⟩
      right
      refine ⟨?_, ⟨m, by rw [← hm]⟩⟩
      by_contra nh
      have ⟨p, hp⟩ := nh
      by_cases hp' : p = 0
      · rw [hp'] at hp
        simp at hp
      · have ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero hp'
        rw [hq] at hp
        have hq₁ : (q.succ + q).succ = n.succ := calc (q.succ + q).succ
          _ = q.succ + q.succ := rfl
          _ = 2 * q.succ := by rw [Nat.two_mul]
          _ = n.succ := hp
        injection hq₁ with hq₂
        have : odd n := by
          refine ⟨q, ?_⟩
          calc 2 * q + 1
            _ = q + q + 1 := by rw [Nat.two_mul]
            _ = q + q.succ := rfl
            _ = q.succ + q := by rw [Nat.add_comm]
            _ = n := hq₂
        exact absurd this h
    · -- Assumes `n` is odd meaning `n⁺` is even.
      intro ⟨h, ⟨p, hp⟩⟩
      have hp' : 2 * p.succ = n.succ := congrArg Nat.succ hp
      left
      refine ⟨⟨p.succ, by rw [← hp']⟩, ?_⟩
      by_contra nh
      unfold odd at nh
      have ⟨q, hq⟩ := nh
      injection hq with hq'
      simp only [Nat.add_eq, Nat.add_zero] at hq'
      have : even n := ⟨q, hq'⟩
      exact absurd this h

end Enderton.Set.Chapter_4