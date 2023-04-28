import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.NormNum

namespace List

-- ========================================
-- Indexing
-- ========================================

/--
Getting an element `i` from a list is equivalent to `get`ting an element `i + 1`
from that list as a tail.
-/
theorem get_cons_succ_self_eq_get_tail_self
  : get (x :: xs) (Fin.succ i) = get xs i := by
  conv => lhs; unfold get; simp only

-- ========================================
-- Length
-- ========================================

/--
A list is nonempty if and only if it can be written as a head concatenated with
a tail.
-/
theorem self_neq_nil_imp_exists_mem : xs ≠ [] ↔ (∃ a as, xs = a :: as) := by
  apply Iff.intro
  · intro h
    cases hx : xs with
    | nil => rw [hx] at h; simp at h
    | cons a as => exact ⟨a, ⟨as, rfl⟩⟩
  · intro ⟨a, ⟨as, hx⟩⟩
    rw [hx]
    simp

/--
Only the empty list has length zero.
-/
theorem eq_nil_iff_length_zero : xs = [] ↔ length xs = 0 := by
  apply Iff.intro
  · intro h
    rw [h]
    simp
  · intro h
    cases xs with
    | nil => rfl
    | cons a as => simp at h

/--
If the length of a list is greater than zero, it cannot be `List.nil`.
-/
theorem neq_nil_iff_length_gt_zero : xs ≠ [] ↔ xs.length > 0 := by
  have : ¬xs = [] ↔ ¬length xs = 0 := Iff.not eq_nil_iff_length_zero
  rwa [
    show ¬xs = [] ↔ xs ≠ [] from Iff.rfl,
    show ¬length xs = 0 ↔ length xs ≠ 0 from Iff.rfl,
    ← zero_lt_iff
  ] at this

-- ========================================
-- Membership
-- ========================================

/--
If there exists a member of a list, the list must be nonempty.
-/
theorem exists_mem_iff_neq_nil : (∃ x, x ∈ xs) ↔ xs ≠ [] := by
  apply Iff.intro
  · intro ⟨x, hx⟩
    induction hx <;> simp
  · intro hx
    cases xs with
    | nil => simp at hx
    | cons a as => exact ⟨a, by simp⟩

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
-- Sublists
-- ========================================

/--
Given nonempty list `xs`, `head` is equivalent to `get`ting the `0`th index.
-/
theorem head_eq_get_zero {xs : List α} (h : xs ≠ [])
  : head xs h = get xs ⟨0, neq_nil_iff_length_gt_zero.mp h⟩ := by
  have ⟨a, ⟨as, hs⟩⟩ := self_neq_nil_imp_exists_mem.mp h
  subst hs
  simp

/--
Given nonempty list `xs`, `getLast xs` is equivalent to `get`ting the
`length - 1`th index.
-/
theorem getLast_eq_get_length_sub_one {xs : List α} (h : xs ≠ [])
  : getLast xs h = get xs ⟨xs.length - 1, by
      have ⟨_, ⟨_, hs⟩⟩ := self_neq_nil_imp_exists_mem.mp h
      rw [hs]
      simp⟩ := by
  induction xs with
  | nil => simp at h
  | cons _ as ih =>
    match as with
    | nil => simp
    | cons b bs => unfold getLast; rw [ih]; simp

/--
If a `List` has a `tail?` defined, it must be nonempty.
-/
theorem some_tail?_imp_cons (h : tail? xs = some ys) : ∃ x, xs = x :: ys := by
  unfold tail? at h
  cases xs with
  | nil => simp at h
  | cons r rs => exact ⟨r, by simp at h; rw [h]⟩

-- ========================================
-- Zips
-- ========================================

/--
The length of a list zipped with its tail is the length of the tail.
-/
theorem length_zipWith_self_tail_eq_length_sub_one
  : length (zipWith f (a :: as) as) = length as := by
  rw [length_zipWith]
  simp only [length_cons, ge_iff_le, min_eq_right_iff]
  show length as ≤ length as + 1
  simp only [le_add_iff_nonneg_right]

/--
The result of a `zipWith` is nonempty if and only if both arguments are
nonempty.
-/
theorem zipWith_nonempty_iff_args_nonempty
  : zipWith f as bs ≠ [] ↔ as ≠ [] ∧ bs ≠ [] := by
  apply Iff.intro
  · intro h
    rw [self_neq_nil_imp_exists_mem] at h
    have ⟨z, ⟨zs, hzs⟩⟩ := h
    refine ⟨?_, ?_⟩ <;>
    · by_contra nh
      rw [nh] at hzs
      simp at hzs
  · intro ⟨ha, hb⟩
    have ⟨a', ⟨as', has⟩⟩ := self_neq_nil_imp_exists_mem.mp ha
    have ⟨b', ⟨bs', hbs⟩⟩ := self_neq_nil_imp_exists_mem.mp hb
    rw [has, hbs]
    simp

/--
An index less than the length of a `zip` is less than the length of the left
operand.
-/
theorem fin_zipWith_imp_val_lt_length_left {i : Fin (zipWith f xs ys).length}
  : ↑i < length xs := by
  have hi := i.2
  simp only [length_zipWith, ge_iff_le, lt_min_iff] at hi
  exact hi.left

/--
An index less than the length of a `zip` is less than the length of the left
operand.
-/
theorem fin_zipWith_imp_val_lt_length_right {i : Fin (zipWith f xs ys).length}
  : ↑i < length ys := by
  have hi := i.2
  simp only [length_zipWith, ge_iff_le, lt_min_iff] at hi
  exact hi.right

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
    have := neq_nil_iff_length_gt_zero.mpr h
    simp at this
  | cons a bs =>
    rw [length_zipWith_self_tail_eq_length_sub_one]
    conv => lhs; unfold length

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
theorem mem_pairwise_imp_exists_adjacent {xs : List α} (h : x ∈ xs.pairwise f)
  : ∃ i : Fin (xs.length - 1), ∃ x₁ x₂,
      x₁ = get xs ⟨i.1, Nat.lt_of_lt_pred i.2⟩ ∧
      x₂ = get xs ⟨i.1 + 1, lt_tsub_iff_right.mp i.2⟩ ∧
      x = f x₁ x₂ := by
  unfold pairwise at h
  cases hs : tail? xs with
  | none => rw [hs] at h; cases h
  | some ys =>
    rw [hs] at h
    simp only at h
    -- Find index `i` that corresponds to the index `x₁`. We decompose this
    -- `Fin` type into `j` and `hj` to make rewriting easier.
    have ⟨_, hy⟩ := some_tail?_imp_cons hs    
    have ⟨i, hx⟩ := mem_iff_exists_get.mp h
    have ⟨j, hj⟩ := i
    rw [
      hy,
      length_zipWith_self_tail_eq_length_sub_one,
      show length ys = length xs - 1 by rw [hy]; simp
    ] at hj
    refine
      ⟨⟨j, hj⟩,
        ⟨get xs ⟨j, Nat.lt_of_lt_pred hj⟩,
          ⟨get xs ⟨j + 1, lt_tsub_iff_right.mp hj⟩,
            ⟨rfl, ⟨rfl, ?_⟩⟩⟩⟩⟩
    rw [← hx, get_zipWith]
    subst hy
    simp only [length_cons, get, Nat.add_eq, add_zero]

end List
