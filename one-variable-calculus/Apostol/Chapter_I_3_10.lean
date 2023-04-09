import Mathlib.Data.PNat.Basic
import Mathlib.Data.Real.Basic

#check Archimedean

namespace Real

/--
Every real should be less than or equal to the absolute value of its ceiling.
-/
lemma leq_nat_abs_ceil_self (x : ℝ) : x ≤ Int.natAbs ⌈x⌉ := by
  by_cases h : x ≥ 0
  · let k : ℤ := ⌈x⌉
    unfold Int.natAbs
    have k' : k = ⌈x⌉ := rfl
    rw [←k']
    have _ : k ≥ 0 := by  -- Hint for match below
      rw [k', ge_iff_le]
      exact Int.ceil_nonneg (ge_iff_le.mp h)
    match k with
    | Int.ofNat m => calc x
      _ ≤ ⌈x⌉ := Int.le_ceil x
      _ = Int.ofNat m := by rw [←k']
  · have h' : ((Int.natAbs ⌈x⌉) : ℝ) ≥ 0 := by simp
    calc x
      _ ≤ 0 := le_of_lt (lt_of_not_le h)
      _ ≤ ↑(Int.natAbs ⌈x⌉) := GE.ge.le h'    

/--
Theorem 1.29

For every real `x` there exists a positive integer `n` such that `n > x`.
-/
theorem exists_pnat_geq_self (x : ℝ) : ∃ n : ℕ+, ↑n > x := by
  let x' : ℕ+ := ⟨Int.natAbs ⌈x⌉ + 1, by simp⟩
  have h : x < x' := calc x
    _ ≤ Int.natAbs ⌈x⌉ := leq_nat_abs_ceil_self x
    _ < ↑↑(Int.natAbs ⌈x⌉ + 1) := by simp
    _ = x' := rfl
  exact ⟨x', h⟩

/--
Theorem 1.30

If `x > 0` and if `y` is an arbitrary real number, there exists a positive
integer `n` such that `nx > y`.

This is known as the *Archimedean Property of the Reals*.
-/
theorem pos_imp_exists_pnat_mul_self_geq {x y : ℝ}
  : x > 0 → ∃ n : ℕ+, n * x > y := by
  intro hx
  let ⟨n, p⟩ := exists_pnat_geq_self (y / x)
  have p' := mul_lt_mul_of_pos_right p hx
  rw [div_mul, div_self (show x ≠ 0 from LT.lt.ne' hx), div_one] at p'
  exact ⟨n, p'⟩

end Real
