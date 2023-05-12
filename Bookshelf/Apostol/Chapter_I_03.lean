import Mathlib.Data.Real.Basic

import Common.Set

/-! # Apostol.Chapter_I_03

A Set of Axioms for the Real-Number System
-/

namespace Apostol.Chapter_I_03

#check Archimedean
#check Real.exists_isLUB

/-! ## The least-upper-bound axiom (completeness axiom) -/

/--
A property holds for the negation of elements in set `S` **iff** it also holds
for the elements of the negation of `S`.
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
An element `x` is the least element of the negation of a set **iff** `-x` is the
greatest element of the set.
-/
lemma is_least_neg_set_eq_is_greatest_set_neq (S : Set ℝ)
  : IsLeast (-S) x = IsGreatest S (-x) := by
  unfold IsLeast IsGreatest
  rw [← neg_upper_bounds_eq_lower_bounds_neg S]
  rfl

/--
At least with respect to `ℝ`, `x` is the least upper bound of set `-S` **iff**
`-x` is the greatest lower bound of `S`.
-/
theorem is_lub_neg_set_iff_is_glb_set_neg (S : Set ℝ)
  : IsLUB (-S) x = IsGLB S (-x) :=
  calc IsLUB (-S) x
    _ = IsLeast (upperBounds (-S)) x := rfl
    _ = IsLeast (-lowerBounds S) x := by rw [upper_bounds_neg_eq_neg_lower_bounds S]
    _ = IsGreatest (lowerBounds S) (-x) := by rw [is_least_neg_set_eq_is_greatest_set_neq]
    _ = IsGLB S (-x) := rfl

/-- #### Theorem I.27

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
  let ⟨ub, ubp⟩ := Real.exists_isLUB (-S) hne' hbdd'
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
    have : k ≥ 0 := by  -- Hint for match below
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

/-! ## The Archimedean property of the real-number system -/

/-- #### Theorem I.29

For every real `x` there exists a positive integer `n` such that `n > x`.
-/
theorem exists_pnat_geq_self (x : ℝ) : ∃ n : ℕ+, ↑n > x := by
  let n : ℕ+ := ⟨Int.natAbs ⌈x⌉ + 1, by simp⟩
  have : x < n := calc x
    _ ≤ Int.natAbs ⌈x⌉ := leq_nat_abs_ceil_self x
    _ < ↑↑(Int.natAbs ⌈x⌉ + 1) := by simp
    _ = n := rfl
  exact ⟨n, this⟩

/-- #### Theorem I.30

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

/-- #### Theorem I.31

If three real numbers `a`, `x`, and `y` satisfy the inequalities
`a ≤ x ≤ a + y / n` for every integer `n ≥ 1`, then `x = a`.
-/
theorem forall_pnat_leq_self_leq_frac_imp_eq {x y a : ℝ}
  : (∀ n : ℕ+, a ≤ x ∧ x ≤ a + (y / n)) → x = a := by
  intro h
  match @trichotomous ℝ LT.lt _ x a with
  | Or.inr (Or.inl r) =>  -- x = a
    exact r
  | Or.inl r =>  -- x < a
    have z : a < a := lt_of_le_of_lt (h 1).left r
    simp at z
  | Or.inr (Or.inr r) =>  -- x > a
    let ⟨c, hc⟩ := exists_pos_add_of_lt' r
    let ⟨n, hn⟩ := @exists_pnat_mul_self_geq_of_pos c y hc.left
    have hn := mul_lt_mul_of_pos_left hn $
      have hp : 0 < (↑↑n : ℝ) := by simp
      show 0 < ((↑↑n)⁻¹ : ℝ) from inv_pos.mpr hp
    rw [
      inv_mul_eq_div,
      ← mul_assoc, mul_comm (n⁻¹ : ℝ),
      ← one_div,
      mul_one_div
    ] at hn
    simp at hn
    have := calc a + y / ↑↑n
      _ < a + c := add_lt_add_left hn a
      _ = x := hc.right
      _ ≤ a + y / ↑↑n := (h n).right
    simp at this

/--
If three real numbers `a`, `x`, and `y` satisfy the inequalities
`a - y / n ≤ x ≤ a` for every integer `n ≥ 1`, then `x = a`.
-/
theorem forall_pnat_frac_leq_self_leq_imp_eq {x y a : ℝ}
  : (∀ n : ℕ+, a - (y / n) ≤ x ∧ x ≤ a) → x = a := by
  intro h
  match @trichotomous ℝ LT.lt _ x a with
  | Or.inr (Or.inl r) =>  -- x = a
    exact r
  | Or.inl r =>  -- x < a
    let ⟨c, hc⟩ := exists_pos_add_of_lt' r
    let ⟨n, hn⟩ := @exists_pnat_mul_self_geq_of_pos c y hc.left
    have hn := mul_lt_mul_of_pos_left hn $
      have hp : 0 < (↑↑n : ℝ) := by simp
      show 0 < ((↑↑n)⁻¹ : ℝ) from inv_pos.mpr hp
    rw [
      inv_mul_eq_div,
      ← mul_assoc, mul_comm (n⁻¹ : ℝ),
      ← one_div,
      mul_one_div
    ] at hn
    simp at hn
    have := calc a - y / ↑↑n
      _ > a - c := sub_lt_sub_left hn a
      _ = x := sub_eq_of_eq_add (Eq.symm hc.right)
      _ ≥ a - y / ↑↑n := (h n).left
    simp at this
  | Or.inr (Or.inr r) =>  -- x > a
    have z : x < x := lt_of_le_of_lt (h 1).right r
    simp at z

/-! ## Fundamental properties of the supremum and infimum -/

/--
Every member of a set `S` is less than or equal to some value `ub` if and only
if `ub` is an upper bound of `S`. 
-/
lemma mem_upper_bounds_iff_forall_le {S : Set ℝ}
  : ub ∈ upperBounds S ↔ ∀ x ∈ S, x ≤ ub := by
  apply Iff.intro
  · intro h _ hx
    exact (h hx)
  · exact id

/--
If a set `S` has a least upper bound, it follows every member of `S` is less
than or equal to that value.
-/
lemma forall_lub_imp_forall_le {S : Set ℝ}
  : IsLUB S ub → ∀ x ∈ S, x ≤ ub := by
  intro h
  rw [← mem_upper_bounds_iff_forall_le]
  exact h.left

/--
Any member of the upper bounds of a set must be greater than or equal to the
least member of that set.
-/
lemma mem_imp_ge_lub {x : ℝ} (h : IsLUB S s) : x ∈ upperBounds S → x ≥ s := by
  intro hx
  exact h.right hx

/-- #### Theorem I.32a

Let `h` be a given positive number and let `S` be a set of real numbers. If `S`
has a supremum, then for some `x` in `S` we have `x > sup S - h`.
-/
theorem sup_imp_exists_gt_sup_sub_delta {S : Set ℝ} {s h : ℝ} (hp : h > 0)
  : IsLUB S s → ∃ x ∈ S, x > s - h := by
  intro hb
  -- Suppose all members of our set was less than `s - h`. Then `s` couldn't be
  -- the *least* upper bound.
  by_contra nb
  suffices s - h ∈ upperBounds S by
    have h' : h < h := calc h
      _ ≤ 0 := (le_sub_self_iff s).mp (hb.right this)
      _ < h := hp
    simp at h'
  rw [not_exists] at nb
  have nb' : ∀ x ∈ S, x ≤ s - h := by
    intro x hx
    exact le_of_not_gt (not_and.mp (nb x) hx)
  rwa [← mem_upper_bounds_iff_forall_le] at nb'

/--
Every member of a set `S` is greater than or equal to some value `lb` if and
only if `lb` is a lower bound of `S`. 
-/
lemma mem_lower_bounds_iff_forall_ge {S : Set ℝ}
  : lb ∈ lowerBounds S ↔ ∀ x ∈ S, x ≥ lb := by
  apply Iff.intro
  · intro h _ hx
    exact (h hx)
  · exact id

/--
If a set `S` has a greatest lower bound, it follows every member of `S` is
greater than or equal to that value.
-/
lemma forall_glb_imp_forall_ge {S : Set ℝ}
  : IsGLB S lb → ∀ x ∈ S, x ≥ lb := by
  intro h
  rw [← mem_lower_bounds_iff_forall_ge]
  exact h.left

/--
Any member of the lower bounds of a set must be less than or equal to the
greatest member of that set.
-/
lemma mem_imp_le_glb {x : ℝ} (h : IsGLB S s) : x ∈ lowerBounds S → x ≤ s := by
  intro hx
  exact h.right hx

/-- #### Theorem I.32b

Let `h` be a given positive number and let `S` be a set of real numbers. If `S`
has an infimum, then for some `x` in `S` we have `x < inf S + h`.
-/
theorem inf_imp_exists_lt_inf_add_delta {S : Set ℝ} {s h : ℝ} (hp : h > 0)
  : IsGLB S s → ∃ x ∈ S, x < s + h := by
  intro hb
  -- Suppose all members of our set was greater than `s + h`. Then `s` couldn't
  -- be the *greatest* lower bound.
  by_contra nb
  suffices s + h ∈ lowerBounds S by
    have h' : h < h := calc h
      _ ≤ 0 := (add_le_iff_nonpos_right s).mp (hb.right this)
      _ < h := hp
    simp at h'
  rw [not_exists] at nb
  have nb' : ∀ x ∈ S, x ≥ s + h := by
    intro x hx
    exact le_of_not_gt (not_and.mp (nb x) hx)
  rwa [← mem_lower_bounds_iff_forall_ge] at nb'

/-- #### Theorem I.33a (Additive Property)

Given nonempty subsets `A` and `B` of `ℝ`, let `C` denote the set
`C = {a + b : a ∈ A, b ∈ B}`. If each of `A` and `B` has a supremum, then `C`
has a supremum, and `sup C = sup A + sup B`.
-/
theorem sup_minkowski_sum_eq_sup_add_sup (A B : Set ℝ) (a b : ℝ)
  (hA : A.Nonempty) (hB : B.Nonempty)
  (ha : IsLUB A a) (hb : IsLUB B b)
  : IsLUB (Set.minkowski_sum A B) (a + b) := by
  let C := Set.minkowski_sum A B
  -- First we show `a + b` is an upper bound of `C`.
  have hub : a + b ∈ upperBounds C := by
    rw [mem_upper_bounds_iff_forall_le]
    intro x hx
    have ⟨a', ⟨ha', ⟨b', ⟨hb', hxab⟩⟩⟩⟩: ∃ a ∈ A, ∃ b ∈ B, x = a + b := hx
    have hs₁ : a' ≤ a := (forall_lub_imp_forall_le ha) a' ha'
    have hs₂ : b' ≤ b := (forall_lub_imp_forall_le hb) b' hb'
    exact calc x
      _ = a' + b' := hxab
      _ ≤ a + b := add_le_add hs₁ hs₂
  -- Now we show `a + b` is the *least* upper bound of `C`. We know a least
  -- upper bound `c` exists; show that `c = a + b`.
  have ⟨c, hc⟩ := Real.exists_isLUB C
    (Set.nonempty_minkowski_sum_iff_nonempty_add_nonempty.mpr ⟨hA, hB⟩)
    ⟨a + b, hub⟩
  suffices (∀ n : ℕ+, c ≤ a + b ∧ a + b ≤ c + (1 / n)) by
    rwa [← forall_pnat_leq_self_leq_frac_imp_eq this] at hc
  intro n
  apply And.intro
  · exact hc.right hub
  · have hd : 1 / (2 * n) > (0 : ℝ) := by norm_num
    have ⟨a', ha'⟩ := sup_imp_exists_gt_sup_sub_delta hd ha
    have ⟨b', hb'⟩ := sup_imp_exists_gt_sup_sub_delta hd hb
    have hab' : a + b < a' + b' + 1 / n := by
      have ha'' := add_lt_add_right ha'.right (1 / (2 * ↑↑n))
      have hb'' := add_lt_add_right hb'.right (1 / (2 * ↑↑n))
      rw [sub_add_cancel] at ha'' hb''
      have hr := add_lt_add ha'' hb''
      ring_nf at hr
      ring_nf
      rwa [add_assoc, add_comm b' (↑↑n)⁻¹, ← add_assoc]
    have hc' : a' + b' ≤ c := by
      refine forall_lub_imp_forall_le hc (a' + b') ?_
      show ∃ a ∈ A, ∃ b ∈ B, a' + b' = a + b
      exact ⟨a', ⟨ha'.left, ⟨b', ⟨hb'.left, rfl⟩⟩⟩⟩
    calc a + b
      _ ≤ a' + b' + 1 / n := le_of_lt hab'
      _ ≤ c + 1 / n := add_le_add_right hc' (1 / n)

/-- #### Theorem I.33b (Additive Property)

Given nonempty subsets `A` and `B` of `ℝ`, let `C` denote the set
`C = {a + b : a ∈ A, b ∈ B}`. If each of `A` and `B` has an infimum, then `C`
has an infimum, and `inf C = inf A + inf B`.
-/
theorem inf_minkowski_sum_eq_inf_add_inf (A B : Set ℝ)
  (hA : A.Nonempty) (hB : B.Nonempty)
  (ha : IsGLB A a) (hb : IsGLB B b)
  : IsGLB (Set.minkowski_sum A B) (a + b) := by
  let C := Set.minkowski_sum A B
  -- First we show `a + b` is a lower bound of `C`.
  have hlb : a + b ∈ lowerBounds C := by
    rw [mem_lower_bounds_iff_forall_ge]
    intro x hx
    have ⟨a', ⟨ha', ⟨b', ⟨hb', hxab⟩⟩⟩⟩: ∃ a ∈ A, ∃ b ∈ B, x = a + b := hx
    have hs₁ : a' ≥ a := (forall_glb_imp_forall_ge ha) a' ha'
    have hs₂ : b' ≥ b := (forall_glb_imp_forall_ge hb) b' hb'
    exact calc x
      _ = a' + b' := hxab
      _ ≥ a + b := add_le_add hs₁ hs₂
  -- Now we show `a + b` is the *greatest* lower bound of `C`. We know a
  -- greatest lower bound `c` exists; show that `c = a + b`.
  have ⟨c, hc⟩ := exists_isGLB C
    (Set.nonempty_minkowski_sum_iff_nonempty_add_nonempty.mpr ⟨hA, hB⟩)
    ⟨a + b, hlb⟩
  suffices (∀ n : ℕ+, c - (1 / n) ≤ a + b ∧ a + b ≤ c) by
    rwa [← forall_pnat_frac_leq_self_leq_imp_eq this] at hc
  intro n
  apply And.intro
  · have hd : 1 / (2 * n) > (0 : ℝ) := by norm_num
    have ⟨a', ha'⟩ := inf_imp_exists_lt_inf_add_delta hd ha
    have ⟨b', hb'⟩ := inf_imp_exists_lt_inf_add_delta hd hb
    have hab' : a' + b' - 1 / n < a + b := by
      have ha'' := sub_lt_sub_right ha'.right (1 / (2 * ↑↑n))
      have hb'' := sub_lt_sub_right hb'.right (1 / (2 * ↑↑n))
      rw [add_sub_cancel] at ha'' hb''
      have hr := add_lt_add ha'' hb''
      ring_nf at hr
      ring_nf
      rwa [← add_sub_assoc, add_sub_right_comm]
    have hc' : c ≤ a' + b' := by
      refine forall_glb_imp_forall_ge hc (a' + b') ?_
      show ∃ a ∈ A, ∃ b ∈ B, a' + b' = a + b
      exact ⟨a', ⟨ha'.left, ⟨b', ⟨hb'.left, rfl⟩⟩⟩⟩
    calc c - 1 / n
      _ ≤ a' + b' - 1 / n := sub_le_sub_right hc' (1 / n)
      _ ≤ a + b := le_of_lt hab'
  · exact hc.right hlb

/-- #### Theorem I.34

Given two nonempty subsets `S` and `T` of `ℝ` such that `s ≤ t` for every `s` in
`S` and every `t` in `T`. Then `S` has a supremum, and `T` has an infimum, and
they satisfy the inequality `sup S ≤ inf T`.
-/
theorem forall_mem_le_forall_mem_imp_sup_le_inf (S T : Set ℝ)
  (hS : S.Nonempty) (hT : T.Nonempty)
  (p : ∀ s ∈ S, ∀ t ∈ T, s ≤ t)
  : ∃ (s : ℝ), IsLUB S s ∧ ∃ (t : ℝ), IsGLB T t ∧ s ≤ t := by
  -- Show a supremum of `S` and an infimum of `T` exists (since each set bounds
  -- above and below the other, respectively).
  let ⟨s, hs⟩ := hS
  let ⟨t, ht⟩ := hT
  have ps : t ∈ upperBounds S := by
    intro x hx
    exact p x hx t ht
  have pt : s ∈ lowerBounds T  := by
    intro x hx
    exact p s hs x hx
  have ⟨S_lub, hS_lub⟩ := Real.exists_isLUB S hS ⟨t, ps⟩
  have ⟨T_glb, hT_glb⟩ := exists_isGLB T hT ⟨s, pt⟩
  refine ⟨S_lub, ⟨hS_lub, ⟨T_glb, ⟨hT_glb, ?_⟩⟩⟩⟩
  -- Assume `T_glb < S_lub`. Then `∃ c, T_glb + c < S_lub` which in turn implies
  -- existence of some `x ∈ S` such that `T_glb < S_lub - c / 2 < x < S_lub`.
  by_contra nr
  rw [not_le] at nr
  have ⟨c, hc⟩ := exists_pos_add_of_lt' nr
  have c_div_two_gt_zero : c / 2 > 0 := by
    have hr := div_lt_div_of_lt (show (0 : ℝ) < 2 by simp) hc.left
    rwa [zero_div] at hr
  have T_glb_lt_S_lub_sub_c_div_two : T_glb < S_lub - c / 2 := by
    have hr := congrFun (congrArg HSub.hSub hc.right) (c / 2)
    rw [add_sub_assoc, sub_half c] at hr
    calc T_glb
      _ < T_glb + c / 2 := (lt_add_iff_pos_right T_glb).mpr c_div_two_gt_zero
      _ = S_lub - c / 2 := hr
  -- Since `x ∈ S`, `p` implies `x ≤ t` for all `t ∈ T`. So `x ≤ T_glb`. But the
  -- above implies `T_glb < x`.
  have ⟨x, hx⟩ := sup_imp_exists_gt_sup_sub_delta c_div_two_gt_zero hS_lub
  have : x < x := calc x
    _ ≤ T_glb := mem_imp_le_glb hT_glb (p x hx.left)
    _ < S_lub - c / 2 := T_glb_lt_S_lub_sub_c_div_two
    _ < x := hx.right
  simp at this

/-! ## Exercises -/

/-- #### Exercise 1

If `x` and `y` are arbitrary real numbers with `x < y`, prove that there is at
least one real `z` satisfying `x < z < y`.
-/
theorem exercise_1 (x y : ℝ) (h : x < y) : ∃ z, x < z ∧ z < y := by
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

/-- #### Exercise 2

If `x` is an arbitrary real number, prove that there are integers `m` and `n`
such that `m < x < n`.
-/
theorem exercise_2 (x : ℝ) : ∃ m n : ℝ, m < x ∧ x < n := by
  refine ⟨x - 1, ⟨x + 1, ⟨?_, ?_⟩⟩⟩ <;> norm_num

/-- #### Exercise 3

If `x > 0`, prove that there is a positive integer `n` such that `1 / n < x`.
-/
theorem exercise_3 (x : ℝ) (h : x > 0) : ∃ n : ℕ+, 1 / n < x := by
  have ⟨n, hn⟩ := @exists_pnat_mul_self_geq_of_pos x 1 h
  refine ⟨n, ?_⟩
  have hr := mul_lt_mul_of_pos_right hn (show 0 < 1 / ↑↑n by norm_num)
  conv at hr => arg 2; rw [mul_comm, ← mul_assoc]; simp
  rwa [one_mul] at hr

/-- #### Exercise 4

If `x` is an arbitrary real number, prove that there is exactly one integer `n`
which satisfies the inequalities `n ≤ x < n + 1`. This `n` is called the
greatest integer in `x` and is denoted by `⌊x⌋`. For example, `⌊5⌋ = 5`,
`⌊5 / 2⌋ = 2`, `⌊-8/3⌋ = -3`.
-/
theorem exercise_4 (x : ℝ) : ∃! n : ℤ, n ≤ x ∧ x < n + 1 := by
  let n := Int.floor x
  refine ⟨n, ⟨?_, ?_⟩⟩
  · exact ⟨Int.floor_le x, Int.lt_floor_add_one x⟩
  · intro y hy
    rw [← Int.floor_eq_iff] at hy
    exact Eq.symm hy

/-- #### Exercise 5

If `x` is an arbitrary real number, prove that there is exactly one integer `n`
which satisfies `x ≤ n < x + 1`.
-/
theorem exercise_5 (x : ℝ) : ∃! n : ℤ, x ≤ n ∧ n < x + 1 := by
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

/-! #### Exercise 6

If `x` and `y` are arbitrary real numbers, `x < y`, prove that there exists at
least one rational number `r` satisfying `x < r < y`, and hence infinitely many.
This property is often described by saying that the rational numbers are *dense*
in the real-number system.

###### TODO
-/

/-! #### Exercise 7

If `x` is rational, `x ≠ 0`, and `y` irrational, prove that `x + y`, `x - y`,
`xy`, `x / y`, and `y / x` are all irrational.

###### TODO
-/

/-! #### Exercise 8

Is the sum or product of two irrational numbers always irrational?

###### TODO
-/

/-! #### Exercise 9

If `x` and `y` are arbitrary real numbers, `x < y`, prove that there exists at
least one irrational number `z` satisfying `x < z < y`, and hence infinitely
many.

###### TODO
-/

/-! #### Exercise 10

An integer `n` is called *even* if `n = 2m` for some integer `m`, and *odd* if
`n + 1` is even. Prove the following statements:

(a) An integer cannot be both even and odd.

(b) Every integer is either even or odd.

(c) The sum or product of two even integers is even. What can you say about the
    sum or product of two odd integers?

(d) If `n²` is even, so is `n`. If `a² = 2b²`, where `a` and `b` are integers,
    then both `a` and `b` are even.

(e) Every rational number can be expressed in the form `a / b`, where `a` and
    `b` are integers, at least one of which is odd.

###### TODO
-/


def is_even (n : ℤ) := ∃ m : ℤ, n = 2 * m

def is_odd (n : ℤ) := is_even (n + 1)

/-! #### Exercise 11

Prove that there is no rational number whose square is `2`.

[Hint: Argue by contradiction. Assume `(a / b)² = 2`, where `a` and `b` are
integers, at least one of which is odd. Use parts of Exercise 10 to deduce a
contradiction.]

###### TODO
-/

/-! #### Exercise 12

The Archimedean property of the real-number system was deduced as a consequence
of the least-upper-bound axiom. Prove that the set of rational numbers satisfies
the Archimedean property but not the least-upper-bound property. This shows that
the Archimedean property does not imply the least-upper-bound axiom.

###### TODO
-/

end Apostol.Chapter_I_03
