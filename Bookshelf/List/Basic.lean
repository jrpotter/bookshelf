import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.NormNum

namespace List

-- ========================================
-- Length
-- ========================================

/--
Only the empty list has length zero.
-/
theorem length_zero_iff_self_eq_nil : length xs = 0 ↔ xs = [] := by
  apply Iff.intro
  · intro h
    cases xs with
    | nil => rfl
    | cons a as => simp at h
  · intro h
    rw [h]
    simp

/--
If the length of a list is greater than zero, it cannot be `List.nil`.
-/
theorem length_gt_zero_imp_not_nil : xs.length > 0 → xs ≠ [] := by
  intro h
  by_contra nh
  rw [nh] at h
  have : 0 > 0 := calc 0
    _ = length [] := by rw [← length_zero_iff_self_eq_nil.mpr nh, nh]
    _ > 0 := h
  simp at this

-- ========================================
-- Membership
-- ========================================

/--
A list is nonempty if and only if it can be written as a head concatenated with
a tail.
-/
theorem self_nonempty_imp_exists_mem : xs ≠ [] ↔ (∃ a as, xs = a :: as) := by
  apply Iff.intro
  · intro h
    cases hx : xs with
    | nil => rw [hx] at h; simp at h
    | cons a as => exact ⟨a, ⟨as, rfl⟩⟩
  · intro ⟨a, ⟨as, hx⟩⟩
    rw [hx]
    simp

/--
If there exists a member of a list, the list must be nonempty.
-/
theorem nonempty_iff_mem : xs ≠ [] ↔ ∃ x, x ∈ xs := by
  apply Iff.intro
  · intro hx
    cases xs with
    | nil => simp at hx
    | cons a as => exact ⟨a, by simp⟩
  · intro ⟨x, hx⟩
    induction hx <;> simp

/--
Getting an element `i` from a list is equivalent to `get`ting an element `i + 1`
from that list as a tail.
-/
theorem get_cons_succ_self_eq_get_tail_self
  : get (x :: xs) (Fin.succ i) = get xs i := by
  conv => lhs; unfold get; simp only

/--
Any value that can be retrieved via `get` must be a member of the list argument.
-/
theorem get_mem_self {xs : List α} {i : Fin xs.length} : get xs i ∈ xs := by
  induction xs with
  | nil => have ⟨_, hj⟩ := i; simp at hj
  | cons a as ih =>
    by_cases hk : i = ⟨0, by simp⟩
    · -- If `i = 0`, we are `get`ting the head of our list. This element is
      -- trivially a member of `xs`.
      conv => lhs; unfold get; rw [hk]; simp only
      simp
    · -- Otherwise we are `get`ting an element in the tail. Our induction
      -- hypothesis closes this case.
      have ⟨k', hk'⟩ : ∃ k', i = Fin.succ k' := by
        have ni : ↑i ≠ (0 : ℕ) := fun hi => hk (Fin.ext hi)
        have ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero ni
        refine ⟨⟨j, ?_⟩, Fin.ext hj⟩
        have hi : ↑i < length (a :: as) := i.2
        unfold length at hi
        rwa [hj, show Nat.succ j = j + 1 by rfl, add_lt_add_iff_right] at hi
      conv => lhs; rw [hk', get_cons_succ_self_eq_get_tail_self]
      exact mem_append_of_mem_right [a] ih

/--
`x` is a member of list `xs` if and only if there exists some index of `xs` that
`x` corresponds to.
-/
theorem mem_iff_exists_get {xs : List α}
  : x ∈ xs ↔ ∃ i : Fin xs.length, xs.get i = x := by
  apply Iff.intro
  · intro h
    induction h with
    | head _ => refine ⟨⟨0, ?_⟩, ?_⟩ <;> simp
    | @tail b as _ ih =>
      let ⟨i, hi⟩ := ih
      refine ⟨⟨i.1 + 1, ?_⟩, ?_⟩
      · unfold length; simp
      · simp; exact hi 
  · intro ⟨i, hi⟩
    induction xs with
    | nil => have nh := i.2; simp at nh
    | cons a bs => rw [← hi]; exact get_mem_self

-- ========================================
-- Zips
-- ========================================

/--
The length of a list zipped with its tail is the length of the tail.
-/
theorem length_zip_with_self_tail_eq_length_sub_one
  : length (zipWith f (a :: as) as) = length as := by
  rw [length_zipWith]
  simp only [length_cons, ge_iff_le, min_eq_right_iff]
  show length as ≤ length as + 1
  simp only [le_add_iff_nonneg_right]

/--
The result of a `zipWith` is nonempty if and only if both arguments are
nonempty.
-/
theorem zip_with_nonempty_iff_args_nonempty
  : zipWith f as bs ≠ [] ↔ as ≠ [] ∧ bs ≠ [] := by
  apply Iff.intro
  · intro h
    rw [self_nonempty_imp_exists_mem] at h
    have ⟨z, ⟨zs, hzs⟩⟩ := h
    refine ⟨?_, ?_⟩ <;>
    · by_contra nh
      rw [nh] at hzs
      simp at hzs
  · intro ⟨ha, hb⟩
    have ⟨a', ⟨as', has⟩⟩ := self_nonempty_imp_exists_mem.mp ha
    have ⟨b', ⟨bs', hbs⟩⟩ := self_nonempty_imp_exists_mem.mp hb
    rw [has, hbs]
    simp

private lemma fin_zip_with_imp_val_lt_length_left {i : Fin (zipWith f xs ys).length}
  : i.1 < length xs := by
  have hi := i.2
  simp only [length_zipWith, ge_iff_le, lt_min_iff] at hi
  exact hi.left

private lemma fin_zip_with_imp_val_lt_length_right {i : Fin (zipWith f xs ys).length}
  : i.1 < length ys := by
  have hi := i.2
  simp only [length_zipWith, ge_iff_le, lt_min_iff] at hi
  exact hi.right

/--
Calling `get _ i` on a zip of `xs` and `ys` is the same as applying the function
argument to each of `get xs i` and `get ys i` directly.
-/
theorem get_zip_with_apply_get_get {i : Fin (zipWith f xs ys).length}
  : get (zipWith f xs ys) i = f
      (get xs ⟨i.1, fin_zip_with_imp_val_lt_length_left⟩)
      (get ys ⟨i.1, fin_zip_with_imp_val_lt_length_right⟩) := by
  sorry

-- ========================================
-- Pairwise
-- ========================================

/--
Given a list `xs` of length `k`, produces a list of length `k - 1` where the
`i`th member of the resulting list is `f xs[i] xs[i + 1]`.
-/
def pairwise (xs : List α) (f : α → α → β) : List β :=
  match xs.tail? with
  | none => []
  | some ys => zipWith f xs ys

/--
If list `xs` is empty, then any `pairwise` operation on `xs` yields an empty
list.
-/
theorem len_pairwise_len_nil_eq_zero {xs : List α} (h : xs = [])
  : (xs.pairwise f).length = 0 := by
  rw [h]
  unfold pairwise tail? length
  simp

/--
If `List` `xs` is nonempty, then any `pairwise` operation on `xs` has length
`xs.length - 1`.
-/
theorem len_pairwise_len_cons_sub_one {xs : List α} (h : xs.length > 0)
  : xs.length = (xs.pairwise f).length + 1 := by
  unfold pairwise tail?
  cases xs with
  | nil =>
    have h' := length_gt_zero_imp_not_nil h
    simp at h'
  | cons a bs =>
    suffices length (zipWith f (a :: bs) bs) = length bs by
      rw [this]
      simp
    rw [length_zip_with_self_tail_eq_length_sub_one]

/--
If the `pairwise` list isn't empty, then the original list must have at least
two elements.
-/
theorem mem_pairwise_imp_length_self_ge_2 {xs : List α} (h : xs.pairwise f ≠ [])
  : xs.length ≥ 2 := by
  unfold pairwise tail? at h
  cases hx : xs with
  | nil => rw [hx] at h; simp at h
  | cons a bs =>
    rw [hx] at h
    cases hx' : bs with
    | nil => rw [hx'] at h; simp at h
    | cons a' bs' => unfold length length; rw [add_assoc]; norm_num

/--
If `x` is a member of the pairwise'd list, there must exist two (adjacent)
elements of the list, say `x₁` and `x₂`, such that `x = f x₁ x₂`.
-/
theorem mem_pairwise_imp_exists {xs : List α} (h : x ∈ xs.pairwise f)
  : ∃ x₁ x₂, x₁ ∈ xs ∧ x₂ ∈ xs ∧ x = f x₁ x₂ := by
  unfold pairwise at h
  cases hys : tail? xs with
  | none => rw [hys] at h; cases h
  | some ys =>
    rw [hys] at h
    simp only at h

    -- Since our `tail?` result isn't `none`, we should be able to decompose
    -- `xs` into concatenation operands.
    have ⟨r, hrs⟩ : ∃ r, xs = r :: ys := by
      unfold tail? at hys
      cases xs with
      | nil => simp at hys
      | cons r rs => exact ⟨r, by simp at hys; rw [hys]⟩

    -- Maintain a collection of relations related to `i` and the length of `xs`.
    -- Because of the proof-carrying `Fin` index, we find ourselves needing to
    -- cast these values around periodically.
    have ⟨i, hx⟩ := mem_iff_exists_get.mp h
    have succ_i_lt_length_xs : ↑i + 1 < length xs := by
      have hi := add_lt_add_right i.2 1
      conv at hi => rhs; rw [hrs, length_zip_with_self_tail_eq_length_sub_one]
      conv => rhs; rw [congrArg length hrs]; unfold length
      exact hi
    have succ_i_lt_length_cons_r_ys : ↑i + 1 < length (r :: ys) := by
      have hi := i.2
      conv at hi => rhs; rw [hrs, length_zip_with_self_tail_eq_length_sub_one]
      exact add_lt_add_right hi 1
    have i_lt_length_ys : ↑i < length ys := by
      unfold length at succ_i_lt_length_cons_r_ys
      exact Nat.lt_of_succ_lt_succ succ_i_lt_length_cons_r_ys

    -- Choose the indices `x₁` and `x₂` that correspond to our `x` member. We
    -- massage these values into the correct shape and then prove `x = f x₁ x₂`.
    let x₁ := xs.get ⟨i, fin_zip_with_imp_val_lt_length_left⟩
    let x₂ := xs.get ⟨i + 1, succ_i_lt_length_xs⟩

    have hx₁ : x₁ = xs.get ⟨i, fin_zip_with_imp_val_lt_length_left⟩ := rfl
    have hx₂ : x₂ = get (r :: ys) { val := ↑i + 1, isLt := succ_i_lt_length_cons_r_ys } := by
      rw [show x₂ = xs.get _ by rfl]
      congr
      exact Eq.recOn
        (motive := fun x h => HEq
          succ_i_lt_length_xs
          (cast (show (↑i + 1 < length xs) = (↑i + 1 < length x) by rw [← h])
            succ_i_lt_length_xs))
        (show xs = r :: ys from hrs)
        HEq.rfl

    refine ⟨x₁, ⟨x₂, ⟨get_mem_self, ⟨get_mem_self, ?_⟩⟩⟩⟩
    have hx₂_offset_idx
      : get (r :: ys) { val := ↑i + 1, isLt := succ_i_lt_length_cons_r_ys}
      = get ys { val := ↑i, isLt := i_lt_length_ys } := by
      conv => lhs; unfold get; simp
    rw [hx₂_offset_idx] at hx₂
    rw [get_zip_with_apply_get_get, ← hx₁, ← hx₂] at hx
    exact Eq.symm hx

end List
