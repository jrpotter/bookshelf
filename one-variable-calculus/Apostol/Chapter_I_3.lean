import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Pointwise.Basic
import Mathlib.Tactic.LibrarySearch

#check Archimedean
#check Real.exists_isLUB

namespace Real

/--
A property holds for the negation of elements in set `S` if and only if it also
holds for the elements of the negation of `S`.
-/
lemma set_neg_prop_iff_neg_set_prop (S : Set ℝ) (p : ℝ → Prop)
  : (∀ y, y ∈ S → p (-y)) ↔ (∀ y, y ∈ -S → p y) := by
  apply Iff.intro
  · intro h y hy
    rw [← neg_neg y, Set.neg_mem_neg] at hy
    have := h (-y) hy
    simp at this
    exact this
  · intro h y hy
    rw [← Set.neg_mem_neg] at hy
    exact h (-y) hy

/--
The upper bounds of the negation of a set is the negation of the lower bounds of
the set.
-/
lemma upper_bounds_neg_eq_neg_lower_bounds (S : Set ℝ)
  : upperBounds (-S) = -lowerBounds S := by
  suffices (∀ x, x ∈ upperBounds (-S) ↔ x ∈ -(lowerBounds S)) from
    Set.ext this
  intro x
  apply Iff.intro
  · intro hx
    unfold lowerBounds
    show -x ∈ { x | ∀ ⦃a : ℝ⦄, a ∈ S → x ≤ a }
    show ∀ ⦃a : ℝ⦄, a ∈ S → (-x) ≤ a
    intro a ha; rw [neg_le]; revert ha a
    rw [set_neg_prop_iff_neg_set_prop S (fun a => a ≤ x)]
    exact hx
  · intro hx
    unfold upperBounds
    show ∀ ⦃a : ℝ⦄, a ∈ -S → a ≤ x
    rw [← set_neg_prop_iff_neg_set_prop S (fun a => a ≤ x)]
    intro y hy; rw [neg_le]; revert hy y
    exact hx

/--
The negation of the upper bounds of a set is the lower bounds of the negation of
the set.
-/
lemma neg_upper_bounds_eq_lower_bounds_neg (S : Set ℝ)
  : -upperBounds S = lowerBounds (-S) := by
  suffices (∀ x, x ∈ -upperBounds S ↔ x ∈ lowerBounds (-S)) from
    Set.ext this
  intro x
  apply Iff.intro
  · intro hx
    unfold lowerBounds
    show ∀ ⦃a : ℝ⦄, a ∈ -S → x ≤ a
    rw [← set_neg_prop_iff_neg_set_prop S (fun a => x ≤ a)]
    intro y hy; rw [le_neg]; revert hy y
    exact hx
  · intro hx
    unfold upperBounds
    show -x ∈ { x | ∀ ⦃a : ℝ⦄, a ∈ S → a ≤ x }
    show ∀ ⦃a : ℝ⦄, a ∈ S → a ≤ (-x)
    intro a ha; rw [le_neg]; revert ha a
    rw [set_neg_prop_iff_neg_set_prop S (fun a => x ≤ a)]
    exact hx

/--
An element `x` is the least element of the negation of a set if and only if `-x`
if the greatest element of the set.
-/
lemma is_least_neg_set_eq_is_greatest_set_neq (S : Set ℝ)
  : IsLeast (-S) x = IsGreatest S (-x) := by
  unfold IsLeast IsGreatest
  rw [← neg_upper_bounds_eq_lower_bounds_neg S]
  rfl

/--
At least with respect to `ℝ`, `x` is the least upper bound of set `-S` if and
only if `-x` is the greatest lower bound of `S`.
-/
theorem is_lub_neg_set_iff_is_glb_set_neg (S : Set ℝ)
  : IsLUB (-S) x = IsGLB S (-x) :=
  calc IsLUB (-S) x
    _ = IsLeast (upperBounds (-S)) x := rfl
    _ = IsLeast (-lowerBounds S) x := by rw [upper_bounds_neg_eq_neg_lower_bounds S]
    _ = IsGreatest (lowerBounds S) (-x) := by rw [is_least_neg_set_eq_is_greatest_set_neq]
    _ = IsGLB S (-x) := rfl

/--
Theorem I.27

Every nonempty set `S` that is bounded below has a greatest lower bound; that
is, there is a real number `L` such that `L = inf S`.
-/
theorem exists_isGLB (S : Set ℝ) (hne : S.Nonempty) (hbdd : BddBelow S)
  : ∃ x, IsGLB S x := by
  -- First we show the negation of a nonempty set bounded below is a nonempty
  -- set bounded above. In that case, we can then apply the completeness axiom
  -- to argue the existence of a supremum.
  have hne' : (-S).Nonempty := Set.nonempty_neg.mpr hne
  have hbdd' : ∃ x, ∀ (y : ℝ), y ∈ -S → y ≤ x := by
    rw [bddBelow_def] at hbdd
    let ⟨lb, lbp⟩ := hbdd
    refine ⟨-lb, ?_⟩
    rw [← set_neg_prop_iff_neg_set_prop S (fun y => y ≤ -lb)]
    intro y hy
    exact neg_le_neg (lbp y hy)
  rw [←bddAbove_def] at hbdd'
  -- Once we have found a supremum for `-S`, we argue the negation of this value
  -- is the same as the infimum of `S`.
  let ⟨ub, ubp⟩ := exists_isLUB (-S) hne' hbdd'
  exact ⟨-ub, (is_lub_neg_set_iff_is_glb_set_neg S).mp ubp⟩

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
theorem forall_pnat_leq_self_leq_frac_imp_eq {x y a : ℝ}
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

/--
Theorem I.32a

Let `h` be a given positive number and let `S` be a set of real numbers. If `S`
has a supremum, then for some `x` in `S` we have `x > sup S - h`.
-/
theorem arb_close_to_sup (S : Set ℝ) (s h : ℝ) (hp : h > 0)
  : IsLUB S s → ∃ x : S, x > s - h := sorry

/--
Theorem I.32b

Let `h` be a given positive number and let `S` be a set of real numbers. If `S`
has an infimum, then for some `x` in `S` we have `x < inf S + h`.
-/
theorem arb_close_to_inf (S : Set ℝ) (s h : ℝ) (hp : h > 0)
  : IsGLB S s → ∃ x : S, x < s + h := sorry

end Real
