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
Theorem I.29

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
Theorem I.30

If `x > 0` and if `y` is an arbitrary real number, there exists a positive
integer `n` such that `nx > y`.

This is known as the *Archimedean Property of the Reals*.
-/
theorem exists_pnat_mul_self_geq_of_pos {x y : ℝ}
  : x > 0 → ∃ n : ℕ+, n * x > y := by
  intro hx
  let ⟨n, p⟩ := exists_pnat_geq_self (y / x)
  have p' := mul_lt_mul_of_pos_right p hx
  rw [div_mul, div_self (show x ≠ 0 from LT.lt.ne' hx), div_one] at p'
  exact ⟨n, p'⟩

/--
Theorem I.31

If three real numbers `a`, `x`, and `y` satisfy the inequalities
`a ≤ x ≤ a + y / n` for every integer `n ≥ 1`, then `x = a`.
-/
theorem forall_pnat_leq_self_leq_frac_iff_eq {x y a : ℝ}
  : (∀ n : ℕ+, a ≤ x ∧ x ≤ a + (y / n)) → x = a := by
  intro h
  match @trichotomous ℝ LT.lt _ x a with
  | -- x = a
    Or.inr (Or.inl r) => exact r
  | -- x < a
    Or.inl r => 
    have z : a < a := lt_of_le_of_lt (h 1).left r
    simp at z
  | -- x > a
    Or.inr (Or.inr r) =>
    let ⟨c, hc⟩ := exists_pos_add_of_lt' r
    let ⟨n, hn⟩ := @exists_pnat_mul_self_geq_of_pos c y hc.left
    have hn := mul_lt_mul_of_pos_left hn $
      have hp : 0 < (↑↑n : ℝ) := by simp
      show 0 < ((↑↑n)⁻¹ : ℝ) from inv_pos.mpr hp
    rw [inv_mul_eq_div, ←mul_assoc, mul_comm (n⁻¹ : ℝ), ←one_div, mul_one_div] at hn
    simp at hn
    have hn := add_lt_add_left hn a
    have := calc a + y / ↑↑n
      _ < a + c := hn
      _ = x := hc.right
      _ ≤ a + y / ↑↑n := (h n).right
    simp at this

end Real
