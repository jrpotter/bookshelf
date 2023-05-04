import Mathlib.Tactic.Ring

/-! # Bookshelf.LTuple.Basic

The following is a representation of a (possibly empty) left-biased tuple. A
left-biased `n`-tuple is defined recursively as follows:

```
⟨x₁, ..., xₙ⟩ = ⟨⟨x₁, ..., xₙ₋₁⟩, xₙ⟩
```

Note a `Tuple` exists in Lean already. This implementation differs in two
notable ways:

1. It is left-associative. The built-in `Tuple` instance evaluates e.g.
  `(x₁, x₂, x₃)` as `(x₁, (x₂, x₃))` instead of `((x₁, x₂), x₃)`.
2. Internally, the built-in `Tuple` instance is syntactic sugar for nested
   `Prod` instances. Unlike this implementation, an `LTuple` is a homogeneous
   collection.

In general, prefer using `Prod` over `LTuple`. This exists primarily to solve
certain theorems outlined in [^1].

[^1]: Enderton, Herbert B. A Mathematical Introduction to Logic. 2nd ed. San
      Diego: Harcourt/Academic Press, 2001.
-/

/--
#### LTuple

A left-biased, possibly empty, homogeneous `Tuple`-like structure..
-/
inductive LTuple : (α : Type u) → (size : Nat) → Type u where
  | nil : LTuple α 0
  | snoc : LTuple α n → α → LTuple α (n + 1)

namespace LTuple

/-! ## Coercions -/

scoped instance : CoeOut (LTuple α (min (m + n) m)) (LTuple α m) where
  coe := cast (by simp)

scoped instance : Coe (LTuple α 0) (LTuple α (min n 0)) where
  coe := cast (by rw [Nat.min_zero])

scoped instance : Coe (LTuple α 0) (LTuple α (min 0 n)) where
  coe := cast (by rw [Nat.zero_min])

scoped instance : Coe (LTuple α n) (LTuple α (min n n)) where
  coe := cast (by simp)

scoped instance : Coe (LTuple α n) (LTuple α (0 + n)) where
  coe := cast (by simp)

scoped instance : Coe (LTuple α (min m n + 1)) (LTuple α (min (m + 1) (n + 1))) where
  coe := cast (by rw [Nat.min_succ_succ])

scoped instance : Coe (LTuple α m) (LTuple α (min (m + n) m)) where
  coe := cast (by simp)

/-! ### Equality -/

/--
Two values `a` and `b` are equal **iff** `[a] = [b]`.
-/
theorem eq_iff_singleton : (a = b) ↔ (snoc a nil = snoc b nil) := by
  apply Iff.intro
  · intro h; rw [h]
  · intro h; injection h

/--
Two lists are equal **iff** their heads and tails are equal.
-/
theorem eq_iff_snoc {t₁ t₂ : LTuple α n}
  : (a = b ∧ t₁ = t₂) ↔ (snoc t₁ a = snoc t₂ b) := by
  apply Iff.intro
  · intro ⟨h₁, h₂ ⟩; rw [h₁, h₂]
  · intro h
    injection h with _ h₁ h₂
    exact And.intro h₂ h₁

/--
Implements decidable equality for `Tuple α m`, provided `a` has decidable
equality. 
-/
protected def hasDecEq [DecidableEq α] (t₁ t₂ : LTuple α n)
  : Decidable (Eq t₁ t₂) :=
  match t₁, t₂ with
  | nil, nil => isTrue rfl
  | snoc as a, snoc bs b =>
    match LTuple.hasDecEq as bs with
    | isFalse np => isFalse (fun h => absurd (eq_iff_snoc.mpr h).right np)
    | isTrue hp =>
      if hq : a = b then
        isTrue (eq_iff_snoc.mp $ And.intro hq hp)
      else
        isFalse (fun h => absurd (eq_iff_snoc.mpr h).left hq)

instance [DecidableEq α] : DecidableEq (LTuple α n) := LTuple.hasDecEq

/-! ## Basic API -/

/--
Returns the number of entries in an `LTuple`.
-/
def size (_ : LTuple α n) : Nat := n

/--
Returns all but the last entry of an `LTuple`.
-/
def init : (t : LTuple α (n + 1)) → LTuple α n
  | snoc vs _ => vs

/--
Returns the last entry of an `LTuple`.
-/
def last : LTuple α (n + 1) → α
  | snoc _ v => v

/--
Prepends an entry to an `LTuple`.
-/
def cons : LTuple α n → α → LTuple α (n + 1)
  | nil, a => snoc nil a
  | snoc ts t, a => snoc (cons ts a) t

/-! ## Concatenation -/

/--
Joins two `LTuple`s together end to end.
-/
def concat : LTuple α m → LTuple α n → LTuple α (m + n)
  | is, nil => is
  | is, snoc ts t => snoc (concat is ts) t

/--
Concatenating an `LTuple` with `nil` yields the original `LTuple`.
-/
theorem self_concat_nil_eq_self (t : LTuple α m) : concat t nil = t :=
  match t with
  | nil => rfl
  | snoc _ _ => rfl

/--
Concatenating `nil` with an `LTuple` yields the original `LTuple`.
-/
theorem nil_concat_self_eq_self (t : LTuple α m) : concat nil t = t := by
  induction t with
  | nil => unfold concat; simp
  | @snoc n as a ih =>
    unfold concat
    rw [ih]
    suffices HEq (snoc (cast (_ : LTuple α n = LTuple α (0 + n)) as) a) ↑(snoc as a)
      from eq_of_heq this
    have h₁ := Eq.recOn
      (motive := fun x h => HEq
        (snoc (cast (show LTuple α n = LTuple α x by rw [h]) as) a)
        (snoc as a))
      (show n = 0 + n by simp)
      HEq.rfl
    exact Eq.recOn
      (motive := fun x h => HEq
        (snoc (cast (_ : LTuple α n = LTuple α (0 + n)) as) a)
        (cast h (snoc as a)))
      (show LTuple α (n + 1) = LTuple α (0 + (n + 1)) by simp)
      h₁

/--
Concatenating an `LTuple` to a nonempty `LTuple` moves `concat` calls closer to
the expression leaves.
-/
theorem concat_snoc_snoc_concat {bs : LTuple α n}
  : concat as (snoc bs b) = snoc (concat as bs) b :=
  rfl

/--
`snoc` is equivalent to concatenating the `init` and `last` elements of an
`LTuple` together.
-/
theorem snoc_eq_init_concat_last (as : LTuple α m)
  : snoc as a = concat as (snoc nil a) := by
  cases as with
  | nil => rfl
  | snoc _ _ => simp; unfold concat concat; rfl

/-! ## Initial Sequences -/

/--
Takes the first `k` entries from an `LTuple` to form a new `LTuple`, or the
entire `LTuple` if `k` exceeds the size.
-/
def take (t : LTuple α n) (k : Nat) : LTuple α (min n k) :=
  if h : n ≤ k then
    cast (by rw [min_eq_left h]) t
  else
    match t with
    | nil => nil
    | @snoc _ n' as a => cast (by rw [min_lt_succ_eq h]) (take as k)
 where
  min_lt_succ_eq {m : Nat} (h : ¬m + 1 ≤ k) : min m k = min (m + 1) k := by
    have h' : k + 1 ≤ m + 1 := Nat.lt_of_not_le h
    simp at h'
    rw [min_eq_right h', min_eq_right (Nat.le_trans h' (Nat.le_succ m))]

/--
Taking no entries from any `LTuple` should yield an empty `LTuple`.
-/
theorem self_take_zero_eq_nil (t : LTuple α n) : take t 0 = @nil α := by
  induction t with
  | nil => simp; rfl
  | snoc as a ih => unfold take; simp; rw [ih]; simp

/--
Taking any number of entries from an empty `LTuple` should yield an empty
`LTuple`.
-/
theorem nil_take_zero_eq_nil (k : Nat) : (take (@nil α) k) = @nil α := by
  cases k <;> (unfold take; simp)

/--
Taking `n` entries from an `LTuple` of size `n` should yield the same `LTuple`.
-/
theorem self_take_size_eq_self (t : LTuple α n) : take t n = t := by
  cases t with
  | nil => simp; rfl
  | snoc as a => unfold take; simp

/--
Taking `n - 1` elements from an `LTuple` of size `n` yields the same result,
regardless of the last entry's value.
-/
theorem take_subst_last {as : LTuple α n} (a₁ a₂ : α)
  : take (snoc as a₁) n = take (snoc as a₂) n := by
  unfold take
  simp

/--
Taking `n` elements from an `LTuple` of size `n + 1` is the same as invoking
`init`.
-/
theorem init_eq_take_pred (t : LTuple α (n + 1)) : take t n = init t := by
  cases t with
  | snoc as a =>
    unfold init take
    simp
    rw [self_take_size_eq_self]
    simp

/--
If two `LTuple`s are equal, then any initial sequences of these two `LTuple`s
are also equal.
-/
theorem eq_tuple_eq_take {t₁ t₂ : LTuple α n}
  : (t₁ = t₂) → (t₁.take k = t₂.take k) := by
  intro h
  rw [h]

/--
Given an `LTuple` of size `k`, concatenating an arbitrary `LTuple` and taking
`k` elements yields the original `LTuple`.
-/
theorem eq_take_concat {t₁ : LTuple α m} {t₂ : LTuple α n}
  : take (concat t₁ t₂) m = t₁ := by
  induction t₂ with
  | nil =>
    simp
    rw [self_concat_nil_eq_self, self_take_size_eq_self]
  | @snoc n' as a ih =>
    simp
    rw [concat_snoc_snoc_concat]
    unfold take
    simp
    rw [ih]
    simp

end LTuple