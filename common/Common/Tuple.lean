import Mathlib.Tactic.Ring

/--
`n`-tuples are defined recursively as such:

  `⟨x₁, ..., xₙ⟩ = ⟨⟨x₁, ..., xₙ₋₁⟩, xₙ⟩`

We allow empty tuples. For a `Tuple`-like type with opposite "endian", refer to
`Mathlib.Data.Vector`.
-/
inductive Tuple : (α : Type u) → (size : Nat) → Type u where
  | nil : Tuple α 0
  | snoc : Tuple α n → α → Tuple α (n + 1)

syntax (priority := high) "t[" term,* "]" : term

macro_rules
  | `(t[]) => `(Tuple.nil)
  | `(t[$x]) => `(Tuple.snoc t[] $x)
  | `(t[$xs:term,*, $x]) => `(Tuple.snoc t[$xs,*] $x)

namespace Tuple

-- ========================================
-- Coercions
-- ========================================

scoped instance : CoeOut (Tuple α (min (m + n) m)) (Tuple α m) where
  coe := cast (by simp)

scoped instance : Coe (Tuple α 0) (Tuple α (min n 0)) where
  coe := cast (by rw [Nat.min_zero])

scoped instance : Coe (Tuple α 0) (Tuple α (min 0 n)) where
  coe := cast (by rw [Nat.zero_min])

scoped instance : Coe (Tuple α n) (Tuple α (min n n)) where
  coe := cast (by simp)

scoped instance : Coe (Tuple α n) (Tuple α (0 + n)) where
  coe := cast (by simp)

scoped instance : Coe (Tuple α (min m n + 1)) (Tuple α (min (m + 1) (n + 1))) where
  coe := cast (by rw [Nat.min_succ_succ])

scoped instance : Coe (Tuple α m) (Tuple α (min (m + n) m)) where
  coe := cast (by simp)

-- ========================================
-- Equality
-- ========================================

theorem eq_nil : @Tuple.nil α = t[] := rfl

theorem eq_iff_singleton : (a = b) ↔ (t[a] = t[b]) := by
  apply Iff.intro
  · intro h; rw [h]
  · intro h; injection h

theorem eq_iff_snoc {t₁ t₂ : Tuple α n}
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
protected def hasDecEq [DecidableEq α] (t₁ t₂ : Tuple α n)
  : Decidable (Eq t₁ t₂) :=
  match t₁, t₂ with
  | t[], t[] => isTrue eq_nil
  | snoc as a, snoc bs b =>
    match Tuple.hasDecEq as bs with
    | isFalse np => isFalse (fun h => absurd (eq_iff_snoc.mpr h).right np)
    | isTrue hp =>
      if hq : a = b then
        isTrue (eq_iff_snoc.mp $ And.intro hq hp)
      else
        isFalse (fun h => absurd (eq_iff_snoc.mpr h).left hq)

instance [DecidableEq α] : DecidableEq (Tuple α n) := Tuple.hasDecEq

-- ========================================
-- Basic API
-- ========================================

/--
Returns the number of entries of the `Tuple`.
-/
def size (_ : Tuple α n) : Nat := n

/--
Returns all but the last entry of the `Tuple`.
-/
def init : (t : Tuple α (n + 1)) → Tuple α n
  | snoc vs _ => vs

/--
Returns the last entry of the `Tuple`.
-/
def last : Tuple α (n + 1) → α
  | snoc _ v => v

/--
Prepends an entry to the start of the `Tuple`.
-/
def cons : Tuple α n → α → Tuple α (n + 1)
  | t[], a => t[a]
  | snoc ts t, a => snoc (cons ts a) t

-- ========================================
-- Concatenation
-- ========================================

/--
Join two `Tuple`s together end to end.
-/
def concat : Tuple α m → Tuple α n → Tuple α (m + n)
  | is, t[] => is
  | is, snoc ts t => snoc (concat is ts) t

/--
Concatenating a `Tuple` with `nil` yields the original `Tuple`.
-/
theorem self_concat_nil_eq_self (t : Tuple α m) : concat t t[] = t :=
  match t with
  | t[] => rfl
  | snoc _ _ => rfl

/--
Concatenating `nil` with a `Tuple` yields the `Tuple`.
-/
theorem nil_concat_self_eq_self (t : Tuple α m) : concat t[] t = t := by
  induction t with
  | nil => unfold concat; simp
  | @snoc n as a ih =>
    unfold concat
    rw [ih]
    suffices HEq (snoc (cast (_ : Tuple α n = Tuple α (0 + n)) as) a) ↑(snoc as a)
      from eq_of_heq this
    have h₁ := Eq.recOn
      (motive := fun x h => HEq
        (snoc (cast (show Tuple α n = Tuple α x by rw [h]) as) a)
        (snoc as a))
      (show n = 0 + n by simp)
      HEq.rfl
    exact Eq.recOn
      (motive := fun x h => HEq
        (snoc (cast (_ : Tuple α n = Tuple α (0 + n)) as) a)
        (cast h (snoc as a)))
      (show Tuple α (n + 1) = Tuple α (0 + (n + 1)) by simp)
      h₁

/--
Concatenating a `Tuple` to a nonempty `Tuple` moves `concat` calls closer to
expression leaves.
-/
theorem concat_snoc_snoc_concat {bs : Tuple α n}
  : concat as (snoc bs b) = snoc (concat as bs) b :=
  rfl

/--
`snoc` is equivalent to concatenating the `init` and `last` element together.
-/
theorem snoc_eq_init_concat_last (as : Tuple α m)
  : snoc as a = concat as t[a] := by
  cases as with
  | nil => rfl
  | snoc _ _ => simp; unfold concat concat; rfl

-- ========================================
-- Initial sequences
-- ========================================

/--
Take the first `k` entries from the `Tuple` to form a new `Tuple`, or the entire
`Tuple` if `k` exceeds the number of entries.
-/
def take (t : Tuple α n) (k : Nat) : Tuple α (min n k) :=
  if h : n ≤ k then
    cast (by rw [min_eq_left h]) t
  else
    match t with
    | t[] => t[]
    | @snoc _ n' as a => cast (by rw [min_lt_succ_eq h]) (take as k)
 where
  min_lt_succ_eq {m : Nat} (h : ¬m + 1 ≤ k) : min m k = min (m + 1) k := by
    have h' : k + 1 ≤ m + 1 := Nat.lt_of_not_le h
    simp at h'
    rw [min_eq_right h', min_eq_right (Nat.le_trans h' (Nat.le_succ m))]

/--
Taking no entries from any `Tuple` should yield an empty one.
-/
theorem self_take_zero_eq_nil (t : Tuple α n) : take t 0 = @nil α := by
  induction t with
  | nil => simp; rfl
  | snoc as a ih => unfold take; simp; rw [ih]; simp

/--
Taking any number of entries from an empty `Tuple` should yield an empty one.
-/
theorem nil_take_zero_eq_nil (k : Nat) : (take (@nil α) k) = @nil α := by
  cases k <;> (unfold take; simp)

/--
Taking `n` entries from a `Tuple` of size `n` should yield the same `Tuple`.
-/
theorem self_take_size_eq_self (t : Tuple α n) : take t n = t := by
  cases t with
  | nil => simp; rfl
  | snoc as a => unfold take; simp

/--
Taking all but the last entry of a `Tuple` is the same result, regardless of the
value of the last entry.
-/
theorem take_subst_last {as : Tuple α n} (a₁ a₂ : α)
  : take (snoc as a₁) n = take (snoc as a₂) n := by
  unfold take
  simp

/--
Taking `n` elements from a tuple of size `n + 1` is the same as invoking `init`.
-/
theorem init_eq_take_pred (t : Tuple α (n + 1)) : take t n = init t := by
  cases t with
  | snoc as a =>
    unfold init take
    simp
    rw [self_take_size_eq_self]
    simp

/--
If two `Tuple`s are equal, then any initial sequences of those two `Tuple`s are
also equal.
-/
theorem eq_tuple_eq_take {t₁ t₂ : Tuple α n}
  : (t₁ = t₂) → (t₁.take k = t₂.take k) := by
  intro h
  rw [h]

/--
Given a `Tuple` of size `k`, concatenating an arbitrary `Tuple` and taking `k`
elements yields the original `Tuple`.
-/
theorem eq_take_concat {t₁ : Tuple α m} {t₂ : Tuple α n}
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

end Tuple
