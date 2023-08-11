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

#check Nat.exists_eq_succ_of_ne_zero

/-- #### Theorem 4I

For natural numbers `m` and `n`,
```
m + 0 = m,
m + n⁺ = (m + n)⁺
```
-/
theorem theorem_4i (m n : ℕ)
  : m + 0 = m ∧ m + n.succ = (m + n).succ := ⟨rfl, rfl⟩

/-- #### Theorem 4J

For natural numbers `m` and `n`,
```
m ⬝ 0 = 0,
m ⬝ n⁺ = m ⬝ n + m .
```
-/
theorem theorem_4j (m n : ℕ)
  : m * 0 = 0 ∧ m * n.succ = m * n + m := ⟨rfl, rfl⟩

/-- #### Left Additive Identity

For all `n ∈ ω`, `A₀(n) = n`. In other words, `0 + n = n`.
-/
lemma left_additive_identity (n : ℕ)
  : 0 + n = n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc 0 + n.succ
      _ = (0 + n).succ := rfl
      _ = n.succ := by rw [ih]

#check Nat.zero_add

/-- #### Lemma 2

For all `m, n ∈ ω`, `Aₘ₊(n) = Aₘ(n⁺)`. In other words, `m⁺ + n = m + n⁺`.
-/
lemma lemma_2 (m n : ℕ)
  : m.succ + n = m + n.succ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc m.succ + n.succ
    _ = (m.succ + n).succ := rfl
    _ = (m + n.succ).succ := by rw [ih]
    _ = m + n.succ.succ := rfl

#check Nat.succ_add_eq_succ_add

/-- #### Theorem 4K-1

Associatve law for addition. For `m, n, p ∈ ω`,
```
m + (n + p) = (m + n) + p.
```
-/
theorem theorem_4k_1 (m n p : ℕ)
  : m + (n + p) = (m + n) + p := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc m.succ + (n + p)
    _ = m + (n + p).succ := by rw [lemma_2]
    _ = (m + (n + p)).succ := rfl
    _ = ((m + n) + p).succ := by rw [ih]
    _ = (m + n) + p.succ := rfl
    _ = (m + n).succ + p := by rw [lemma_2]
    _ = (m + n.succ) + p := rfl
    _ = (m.succ + n) + p := by rw [lemma_2]

#check Nat.add_assoc

/-- #### Theorem 4K-2

Commutative law for addition. For `m, n ∈ ω`,
```
m + n = n + m.
```
-/
theorem theorem_4k_2 {m n : ℕ}
  : m + n = n + m := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc m.succ + n
    _ = m + n.succ := by rw [lemma_2]
    _ = (m + n).succ := rfl
    _ = (n + m).succ := by rw [ih]
    _ = n + m.succ := by rfl

#check Nat.add_comm

/-- #### Zero Multiplicand

For all `n ∈ ω`, `M₀(n) = 0`. In other words, `0 ⬝ n = 0`.
-/
theorem zero_multiplicand (n : ℕ)
  : 0 * n = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc 0 * n.succ
    _ = 0 * n + 0 := rfl
    _ = 0 * n := rfl
    _ = 0 := by rw [ih]

#check Nat.zero_mul

/-- #### Successor Distribution

For all `m, n ∈ ω`, `Mₘ₊(n) = Mₘ(n) + n`. In other words,
```
m⁺ ⬝ n = m ⬝ n + n.
```
-/
theorem succ_distrib (m n : ℕ)
  : m.succ * n = m * n + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc m.succ * n.succ
    _ = m.succ * n + m.succ := rfl
    _ = (m * n + n) + m.succ := by rw [ih]
    _ = m * n + (n + m.succ) := by rw [theorem_4k_1]
    _ = m * n + (n.succ + m) := by rw [lemma_2]
    _ = m * n + (m + n.succ) := by
      conv => left; arg 2; rw [theorem_4k_2]
    _ = (m * n + m) + n.succ := by rw [theorem_4k_1]
    _ = m * n.succ + n.succ := rfl

#check Nat.succ_mul

/-- #### Theorem 4K-3

Distributive law. For `m, n, p ∈ ω`,
```
m ⬝ (n + p) = m ⬝ n + m ⬝ p.
```
-/
theorem theorem_4k_3 (m n p : ℕ)
  : m * (n + p) = m * n + m * p := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc m.succ * (n + p)
    _ = m * (n + p) + (n + p) := by rw [succ_distrib]
    _ = m * (n + p) + n + p := by rw [← theorem_4k_1]
    _ = m * n + m * p + n + p := by rw [ih]
    _ = m * n + (m * p + n) + p := by rw [theorem_4k_1]
    _ = m * n + (n + m * p) + p := by
      conv => left; arg 1; arg 2; rw [theorem_4k_2]
    _ = (m * n + n) + (m * p + p) := by rw [theorem_4k_1, theorem_4k_1]
    _ = m.succ * n + m.succ * p := by rw [succ_distrib, succ_distrib]

/-- #### Successor Identity

For all `m ∈ ω`, `Aₘ(1) = m⁺`. In other words, `m + 1 = m⁺`.
-/
theorem succ_identity (m : ℕ)
  : m + 1 = m.succ := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc m.succ + 1
      _ = m + (Nat.succ Nat.zero).succ := by rw [lemma_2]
      _ = (m + 1).succ := rfl
      _ = m.succ.succ := by rw [ih]

#check Nat.succ_eq_one_add

/-- #### Right Multiplicative Identity

For all `m ∈ ω`, `Mₘ(1) = m`. In other words, `m ⬝ 1 = m`.
-/
theorem right_mul_id (m : ℕ)
  : m * 1 = m := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc m.succ * 1
    _ = m * 1 + 1 := by rw [succ_distrib]
    _ = m + 1 := by rw [ih]
    _ = m.succ := by rw [succ_identity]

#check Nat.mul_one

/-- #### Theorem 4K-5

Commutative law for multiplication. For `m, n ∈ ω`, `m ⬝ n = n ⬝ m`. 
-/
theorem theorem_4k_5 (m n : ℕ)
  : m * n = n * m := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc m.succ * n
    _ = m * n + n := by rw [succ_distrib]
    _ = n * m + n := by rw [ih]
    _ = n * m + n * 1 := by
      conv => left; arg 2; rw [← right_mul_id n]
    _ = n * (m + 1) := by rw [← theorem_4k_3]
    _ = n * m.succ := by rw [succ_identity]

#check Nat.mul_comm

/-- #### Theorem 4K-4

Associative law for multiplication. For `m, n, p ∈ ω`,
```
m ⬝ (n ⬝ p) = (m ⬝ n) ⬝ p.
```
-/
theorem theorem_4k_4 (m n p : ℕ)
  : m * (n * p) = (m * n) * p := by
  induction p with
  | zero => simp
  | succ p ih =>
    calc m * (n * p.succ)
    _ = m * (n * p + n) := rfl
    _ = m * (n * p) + m * n := by rw [theorem_4k_3]
    _ = (m * n) * p + m * n := by rw [ih]
    _ = p * (m * n) + m * n := by rw [theorem_4k_5]
    _ = p.succ * (m * n) := by rw [succ_distrib]
    _ = (m * n) * p.succ := by rw [theorem_4k_5]

#check Nat.mul_assoc

/-- #### Lemma 4L(b)

No natural number is a member of itself.
-/
lemma lemma_4l_b (n : ℕ)
  : ¬ n < n := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_contra nh
    rw [Nat.succ_lt_succ_iff] at nh
    exact absurd nh ih

#check Nat.lt_irrefl

/-- #### Lemma 10

For every natural number `n ≠ 0`, `0 ∈ n`.
-/
theorem zero_least_nat (n : ℕ)
  : 0 = n ∨ 0 < n := by
  by_cases h : n = 0
  · left
    rw [h]
  · right
    have ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero h
    rw [hm]
    exact Nat.succ_pos m

/-! #### Theorem 4N

For any natural numbers `n`, `m`, and `p`,
```
m ∈ n ↔ m ⬝ p ∈ n ⬝ p.
```
If, in addition, `p ≠ 0`, then
```
m ∈ n ↔ m ⬝ p ∈ n ⬝ p.
```
-/

theorem theorem_4n_i (m n p : ℕ)
  : m < n ↔ m + p < n + p := by
  have hf : ∀ m n : ℕ, m < n → m + p < n + p := by
    induction p with
    | zero => simp
    | succ p ih =>
      intro m n hp
      have := ih m n hp
      rw [← Nat.succ_lt_succ_iff] at this
      have h₁ : (m + p).succ = m + p.succ := rfl
      have h₂ : (n + p).succ = n + p.succ := rfl
      rwa [← h₁, ← h₂]
  apply Iff.intro
  · exact hf m n
  · intro h
    match @trichotomous ℕ LT.lt _ m n with
    | Or.inl h₁ =>
      exact h₁
    | Or.inr (Or.inl h₁) =>
      rw [← h₁] at h
      exact absurd h (lemma_4l_b (m + p))
    | Or.inr (Or.inr h₁) =>
      have := hf n m h₁
      exact absurd this (Nat.lt_asymm h)

#check Nat.add_lt_add_iff_right

theorem theorem_4n_ii (m n p : ℕ)
  : m < n ↔ m * p.succ < n * p.succ := by
  have hf : ∀ m n : ℕ, m < n → m * p.succ < n * p.succ := by
    intro m n hp₁
    induction p with
    | zero =>
      simp only [Nat.mul_one]
      exact hp₁
    | succ p ih =>
      have hp₂ : m * p.succ < n * p.succ := by
        by_cases hp₃ : p = 0
        · rw [hp₃] at *
          simp only [Nat.mul_one] at *
          exact hp₁
        · exact ih
      calc m * p.succ.succ
        _ = m * p.succ + m := rfl
        _ < n * p.succ + m := (theorem_4n_i (m * p.succ) (n * p.succ) m).mp hp₂
        _ = m + n * p.succ := by rw [theorem_4k_2]
        _ < n + n * p.succ := (theorem_4n_i m n (n * p.succ)).mp hp₁
        _ = n * p.succ + n := by rw [theorem_4k_2]
        _ = n * p.succ.succ := rfl
  apply Iff.intro
  · exact hf m n
  · intro hp
    match @trichotomous ℕ LT.lt _ m n with
    | Or.inl h₁ =>
      exact h₁
    | Or.inr (Or.inl h₁) =>
      rw [← h₁] at hp
      exact absurd hp (lemma_4l_b (m * p.succ))
    | Or.inr (Or.inr h₁) =>
      have := hf n m h₁
      exact absurd this (Nat.lt_asymm hp)

#check Nat.mul_lt_mul_of_pos_right

/-! #### Corollary 4P

The following cancellation laws hold for `m`, `n`, and `p` in `ω`:
```
m + p = n + p ⇒ m = n,
m ⬝ p = n ⬝ p ∧ p ≠ 0 ⇒ m = n.
```
-/

theorem corollary_4p_i (m n p : ℕ) (h : m + p = n + p)
  : m = n := by
  match @trichotomous ℕ LT.lt _ m n with
  | Or.inl h₁ =>
    rw [theorem_4n_i m n p, h] at h₁
    exact absurd h₁ (lemma_4l_b (n + p))
  | Or.inr (Or.inl h₁) =>
    exact h₁
  | Or.inr (Or.inr h₁) =>
    rw [theorem_4n_i n m p, h] at h₁
    exact absurd h₁ (lemma_4l_b (n + p))

#check Nat.add_right_cancel

/-- #### Well Ordering of ω

Let `A` be a nonempty subset of `ω`. Then there is some `m ∈ A` such that
`m ≤ n` for all `n ∈ A`.
-/
theorem well_ordering_nat (A : Set ℕ) (hA : Set.Nonempty A)
  : ∃ m ∈ A, ∀ n, n ∈ A → m ≤ n := by
  sorry

/-- #### Strong Induction Principle for ω

Let `A` be a subset of `ω`, and assume that for every `n ∈ ω`, if every number
less than `n` is in `A`, then `n ∈ A`. Then `A = ω`.
-/
theorem strong_induction_principle_nat (A : Set ℕ)
  (h : ∀ n : ℕ, (∀ m : ℕ, m < n → m ∈ A) → n ∈ A)
  : A = Set.univ := by
  sorry

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