/-
Exercises I 3.12

A Set of Axioms for the Real-Number System
-/
import Mathlib.Algebra.Order.Floor
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.LibrarySearch

import Bookshelf.Real.Rational
import OneVariableCalculus.Apostol.Chapter_I_3

-- ========================================
-- Exercise 1
--
-- If `x` and `y` are arbitrary real numbers with `x < y`, prove that there is
-- at least one real `z` satisfying `x < z < y`.
-- ========================================

example (x y : ℝ) (h : x < y) : ∃ z, x < z ∧ z < y := by
  have ⟨z, hz⟩ := exists_pos_add_of_lt' h
  refine ⟨x + z / 2, ⟨?_, ?_⟩⟩
  · have hz' : z / 2 > 0 := by
      have hr := div_lt_div_of_lt (show (0 : ℝ) < 2 by simp) hz.left
      rwa [zero_div] at hr
    exact (lt_add_iff_pos_right x).mpr hz'
  · have hz' : z / 2 < z := div_lt_self hz.left (show 1 < 2 by norm_num)
    calc x + z / 2
      _ < x + z := (add_lt_add_iff_left x).mpr hz'
      _ = y := hz.right

-- ========================================
-- Exercise 2
--
-- If `x` is an arbitrary real number, prove that there are integers `m` and `n`
-- such that `m < x < n`.
-- ========================================

example (x : ℝ) : ∃ m n : ℝ, m < x ∧ x < n := by
  refine ⟨x - 1, ⟨x + 1, ⟨?_, ?_⟩⟩⟩ <;> norm_num

-- ========================================
-- Exercise 3
--
-- If `x > 0`, prove that there is a positive integer `n` such that `1 / n < x`.
-- ========================================

example (x : ℝ) (h : x > 0) : ∃ n : ℕ+, 1 / n < x := by
  have ⟨n, hn⟩ := @Real.exists_pnat_mul_self_geq_of_pos x 1 h
  refine ⟨n, ?_⟩
  have hr := mul_lt_mul_of_pos_right hn (show 0 < 1 / ↑↑n by norm_num)
  conv at hr => arg 2; rw [mul_comm, ← mul_assoc]; simp
  rwa [one_mul] at hr

-- ========================================
-- Exercise 4
--
-- If `x` is an arbitrary real number, prove that there is exactly one integer
-- `n` which satisfies the inequalities `n ≤ x < n + 1`. This `n` is called the
-- greatest integer in `x` and is denoted by `⌊x⌋`. For example, `⌊5⌋ = 5`,
-- `⌊5 / 2⌋ = 2`, `⌊-8/3⌋ = -3`.
-- ========================================

example (x : ℝ) : ∃! n : ℤ, n ≤ x ∧ x < n + 1 := by
  let n := Int.floor x
  refine ⟨n, ⟨?_, ?_⟩⟩
  · exact ⟨Int.floor_le x, Int.lt_floor_add_one x⟩
  · intro y hy
    rw [← Int.floor_eq_iff] at hy
    exact Eq.symm hy

-- ========================================
-- Exercise 5
--
-- If `x` is an arbitrary real number, prove that there is exactly one integer
-- `n` which satisfies `x ≤ n < x + 1`.
-- ========================================

example (x : ℝ) : ∃! n : ℤ, x ≤ n ∧ n < x + 1 := by
  let n := Int.ceil x
  refine ⟨n, ⟨?_, ?_⟩⟩
  · exact ⟨Int.le_ceil x, Int.ceil_lt_add_one x⟩
  · simp only
    intro y hy
    suffices y - 1 < x ∧ x ≤ y by
      rw [← Int.ceil_eq_iff] at this
      exact Eq.symm this
    apply And.intro
    · have := (sub_lt_sub_iff_right 1).mpr hy.right
      rwa [add_sub_cancel] at this
    · exact hy.left

-- ========================================
-- Exercise 6
--
-- If `x` and `y` are arbitrary real numbers, `x < y`, prove that there exists
-- at least one rational number `r` satisfying `x < r < y`, and hence infinitely
-- many. This property is often described by saying that the rational numbers
-- are *dense* in the real-number system.
-- ========================================

example (x y : ℝ) (h : x < y) : ∃ r : ℚ, x < r ∧ r < y := by
  sorry

-- ========================================
-- Exercise 7
--
-- If `x` is rational, `x ≠ 0`, and `y` irrational, prove that `x + y`, `x - y`,
-- `xy`, `x / y`, and `y / x` are all irrational.
-- ========================================

example (x : ℚ) (hx : x ≠ 0) (y : ℝ) (hy : irrational y)
  : irrational (x + y) :=
  sorry

example (x : ℚ) (hx : x ≠ 0) (y : ℝ) (hy : irrational y)
  : irrational (x - y) :=
  sorry

example (x : ℚ) (hx : x ≠ 0) (y : ℝ) (hy : irrational y)
  : irrational (x * y) :=
  sorry

example (x : ℚ) (hx : x ≠ 0) (y : ℝ) (hy : irrational y)
  : y ≠ 0 → irrational (x / y) :=
  sorry

example (x : ℚ) (hx : x ≠ 0) (y : ℝ) (hy : irrational y)
  : irrational (y / x) :=
  sorry

-- ========================================
-- Exercise 8
--
-- Is the sum or product of two irrational numbers always irrational?
-- ========================================

-- No. Here is a counterexample.

example (hx : x = Real.sqrt 2): irrational x ∧ rational (x * x) := by
  sorry

-- ========================================
-- Exercise 9
--
-- If `x` and `y` are arbitrary real numbers, `x < y`, prove that there exists
-- at least one irrational number `z` satisfying `x < z < y`, and hence
-- infinitely many.
-- ========================================

example (x y : ℝ) (h : x < y) : ∃ z : ℝ, irrational z ∧ x < z ∧ z < y := by
  sorry

-- ========================================
-- Exercise 10
--
-- An integer `n` is called *even* if `n = 2m` for some integer `m`, and *odd*
-- if `n + 1` is even. Prove the following statements:
--
-- (e) Every rational number can be expressed in the form `a / b`, where `a` and
-- `b` are integers, at least one of which is odd.
-- ========================================

def is_even (n : ℤ) := ∃ m : ℤ, n = 2 * m

def is_odd (n : ℤ) := is_even (n + 1)

-- ----------------------------------------
-- (a) An integer cannot be both even and odd.
-- ----------------------------------------

example (n : ℤ) : is_even n = ¬ is_odd n := sorry

-- ----------------------------------------
-- (b) Every integer is either even or odd.
-- ----------------------------------------

example (n : ℤ) : is_even n ∨ is_odd n := sorry

-- ----------------------------------------
-- (c) The sum or product of two even integers is even. What can you say about
-- the sum or product of two odd integers?
-- ----------------------------------------

example (m n : ℤ) : is_even m ∧ is_even n → is_even (m * n) := sorry

example (m n : ℤ) :
  (∃ m n : ℤ, is_odd m ∧ is_odd n ∧ is_even (m * n)) ∧
  (∃ m n : ℤ, is_odd m ∧ is_odd n ∧ is_odd (m * n)) :=
  sorry

-- ----------------------------------------
-- (d) If `n²` is even, so is `n`. If `a² = 2b²`, where `a` and `b` are
-- integers, then both `a` and `b` are even.
-- ----------------------------------------

example (n : ℤ) (h : is_even (n ^ 2)) : is_even n := sorry

example (a b : ℤ) (h : a ^ 2 = 2 * b ^ 2) : is_even a ∧ is_even b := sorry

-- ========================================
-- Exercise 11
--
-- Prove that there is no rational number whose square is `2`.
--
-- [Hint: Argue by contradiction. Assume `(a / b)² = 2`, where `a` and `b` are
-- integers, at least one of which is odd. Use parts of Exercise 10 to deduce a
-- contradiction.]
-- ========================================

example : ¬ ∃ n : ℝ, rational n → n ^ 2 = 2 := sorry

-- ========================================
-- Exercise 12
--
-- The Archimedean property of the real-number system was deduced as a
-- consequence of the least-upper-bound axiom. Prove that the set of rational
-- numbers satisfies the Archimedean property but not the least-upper-bound
-- property. This shows that the Archimedean property does not imply the
-- least-upper-bound axiom.
-- ========================================

/--
Shows the set of rational numbers satisfies the Archimedean property.
-/
theorem exists_pnat_mul_self_geq_of_pos {x y : ℚ}
  : x > 0 → ∃ n : ℕ+, n * x > y := sorry

/--
Show the Archimedean property does not imply the least-upper-bound axiom.
-/
example (S : Set ℚ) (hne : S.Nonempty) (hbdd : BddAbove S)
  : ¬ ∃ x, IsLUB S x :=
  sorry