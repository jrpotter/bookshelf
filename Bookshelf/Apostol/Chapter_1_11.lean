import Mathlib.Data.Real.Basic
import Mathlib.Tactic.LibrarySearch

import Common.Real.Floor

/-! # Apostol.Chapter_1_11 -/

namespace Apostol.Chapter_1_11

open BigOperators

/-! ## Exercise 4

Prove that the greatest-integer function has the properties indicated.
-/

/-- ### Exercise 4a

`⌊x + n⌋ = ⌊x⌋ + n` for every integer `n`.
-/
theorem exercise_4a (x : ℝ) (n : ℤ) : ⌊x + n⌋ = ⌊x⌋ + n :=
  Int.floor_add_int x n

/-- ### Exercise 4b.1

`⌊-x⌋ = -⌊x⌋` if `x` is an integer.
-/
theorem exercise_4b_1 (x : ℤ) : ⌊-x⌋ = -⌊x⌋ := by
  simp only [Int.floor_int, id_eq]

/-- ### Exercise 4b.2

`⌊-x⌋ = -⌊x⌋ - 1` otherwise.
-/
theorem exercise_4b_2 (x : ℝ) (h : ∃ n : ℤ, x ∈ Set.Ioo ↑n (↑n + (1 : ℝ)))
  : ⌊-x⌋ = -⌊x⌋ - 1 := by
  rw [Int.floor_neg]
  suffices ⌈x⌉ = ⌊x⌋ + 1 by
    have := congrArg (HMul.hMul (-1)) this
    simp only [neg_mul, one_mul, neg_add_rev, add_comm] at this
    exact this
  have ⟨n, hn⟩ := h
  have hn' : x ∈ Set.Ico ↑n (↑n + (1 : ℝ)) :=
    Set.mem_of_subset_of_mem Set.Ioo_subset_Ico_self hn
  rw [Int.ceil_eq_iff, Int.floor_eq_on_Ico n x hn']
  simp only [Int.cast_add, Int.cast_one, add_sub_cancel]
  apply And.intro
  · exact (Set.mem_Ioo.mp hn).left
  · exact le_of_lt (Set.mem_Ico.mp hn').right

/-- ### Exercise 4c

`⌊x + y⌋ = ⌊x⌋ + ⌊y⌋` or `⌊x⌋ + ⌊y⌋ + 1`.
-/
theorem exercise_4c (x y : ℝ)
  : ⌊x + y⌋ = ⌊x⌋ + ⌊y⌋ ∨ ⌊x + y⌋ = ⌊x⌋ + ⌊y⌋ + 1 := by
  have hx : x = Int.floor x + Int.fract x := Eq.symm (add_eq_of_eq_sub' rfl)
  have hy : y = Int.floor y + Int.fract y := Eq.symm (add_eq_of_eq_sub' rfl)
  by_cases Int.fract x + Int.fract y < 1
  · refine Or.inl ?_
    rw [Int.floor_eq_iff]
    simp only [Int.cast_add]
    apply And.intro
    · exact add_le_add (Int.floor_le x) (Int.floor_le y)
    · conv => lhs; rw [hx, hy, add_add_add_comm]; arg 1; rw [add_comm]
      rwa [add_comm, ← add_assoc, ← sub_lt_iff_lt_add', ← sub_sub, add_sub_cancel, add_sub_cancel]
  · refine Or.inr ?_
    rw [Int.floor_eq_iff]
    simp only [Int.cast_add, Int.cast_one]
    have h := le_of_not_lt h
    apply And.intro
    · conv => lhs; rw [← add_rotate]
      conv => rhs; rw [hx, hy, add_add_add_comm]; arg 1; rw [add_comm]
      rwa [← sub_le_iff_le_add', ← sub_sub, add_sub_cancel, add_sub_cancel]
    · conv => lhs; rw [hx, hy, add_add_add_comm]; arg 1; rw [add_comm]
      conv => lhs; rw [add_comm, ← add_assoc]
      conv => rhs; rw [add_assoc]
      rw [← sub_lt_iff_lt_add', ← sub_sub, add_sub_cancel, add_sub_cancel]
      exact add_lt_add (Int.fract_lt_one x) (Int.fract_lt_one y)

/-- ### Exercise 5

The formulas in Exercises 4(d) and 4(e) suggest a generalization for `⌊nx⌋`.
State and prove such a generalization.
-/
theorem exercise_5 (n : ℕ) (x : ℝ)
  : ⌊n * x⌋ = Finset.sum (Finset.range n) (fun i => ⌊x + i/n⌋) :=
  Real.Floor.floor_mul_eq_sum_range_floor_add_index_div n x

/-- ### Exercise 4d

`⌊2x⌋ = ⌊x⌋ + ⌊x + 1/2⌋`
-/
theorem exercise_4d (x : ℝ)
  : ⌊2 * x⌋ = ⌊x⌋ + ⌊x + 1/2⌋ := by
  suffices ⌊x⌋ + ⌊x + 1/2⌋ = Finset.sum (Finset.range 2) (fun i => ⌊x + i/2⌋) by
    rw [this]
    exact exercise_5 2 x
  unfold Finset.sum
  simp
  rw [add_comm]

/-- ### Exercise 4e

`⌊3x⌋ = ⌊x⌋ + ⌊x + 1/3⌋ + ⌊x + 2/3⌋`
-/
theorem exercise_4e (x : ℝ)
  : ⌊3 * x⌋ = ⌊x⌋ + ⌊x + 1/3⌋ + ⌊x + 2/3⌋ := by
  suffices ⌊x⌋ + ⌊x + 1/3⌋ + ⌊x + 2/3⌋ = Finset.sum (Finset.range 3) (fun i => ⌊x + i/3⌋) by
    rw [this]
    exact exercise_5 3 x
  unfold Finset.sum
  simp
  conv => rhs; rw [← add_rotate']; arg 2; rw [add_comm]
  rw [← add_assoc]

/-- ### Exercise 7b

If `a` and `b` are positive integers with no common factor, we have the formula
`∑_{n=1}^{b-1} ⌊na / b⌋ = ((a - 1)(b - 1)) / 2`. When `b = 1`, the sum on the
left is understood to be `0`.

Derive the result analytically as follows: By changing the index of summation,
note that `Σ_{n=1}^{b-1} ⌊na / b⌋ = Σ_{n=1}^{b-1} ⌊a(b - n) / b⌋`. Now apply
Exercises 4(a) and (b) to the bracket on the right.
-/
theorem exercise_7b (ha : a > 0) (hb : b > 0) (hp : Nat.coprime a b)
  : ∑ n in (Finset.range b).filter (· > 0), ⌊n * ((a : ℕ) : ℝ) / b⌋ =
      ((a - 1) * (b - 1)) / 2 := by
  sorry

/-- ### Exercise 8

Let `S` be a set of points on the real line. The *characteristic function* of
`S` is, by definition, the function `Χ` such that `Χₛ(x) = 1` for every `x` in
`S`, and `Χₛ(x) = 0` for those `x` not in `S`. Let `f` be a step function which
takes the constant value `cₖ` on the `k`th open subinterval `Iₖ` of some
partition of an interval `[a, b]`. Prove that for each `x` in the union
`I₁ ∪ I₂ ∪ ⋯ ∪ Iₙ` we have

```
f(x) = ∑_{k=1}^n cₖΧ_{Iₖ}(x).
```

This property is described by saying that every step function is a linear
combination of characteristic functions of intervals.
-/
theorem exercise_8 : True := sorry

end Apostol.Chapter_1_11
