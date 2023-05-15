import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

/-! # Common.List.NonEmpty

A `List` with at least one member.
-/

namespace List

structure NonEmpty (α : Type _) : Type _ where
  head : α
  tail : List α

instance : Coe (NonEmpty α) (List α) where
  coe (xs : NonEmpty α) := xs.head :: xs.tail

instance : CoeDep (List α) (cons x xs : List α) (NonEmpty α) where
  coe := { head := x, tail := xs }

namespace NonEmpty

/--
The length of a `List.NonEmpty`.
-/
def length (xs : NonEmpty α) : Nat := 1 + xs.tail.length

/--
The length of a `List.NonEmpty` is always one plus the length of its tail.
-/
theorem length_self_eq_one_add_length_tail (xs : NonEmpty α)
  : xs.length = 1 + xs.tail.length := rfl

/--
A proof that an index is within the bounds of the `List.NonEmpty`.
-/
abbrev inBounds (xs : NonEmpty α) (i : Nat) : Prop :=
  i < xs.length

/--
Retrieves the member of the `List.NonEmpty` at the specified index.
-/
def get (xs : NonEmpty α) : (i : Nat) → (h : xs.inBounds i) → α
  | 0, _ => xs.head
  | n + 1, h =>
    have : n < xs.tail.length := by
      unfold inBounds at h
      rw [length_self_eq_one_add_length_tail, add_comm] at h
      norm_num at h
      exact h
    xs.tail[n]

/--
Variant of `get` that returns an `Option α` in the case of an invalid index.
-/
def get? : NonEmpty α → Nat → Option α
  | xs, 0 => some xs.head
  | xs, n + 1 => xs.tail.get? n

/--
Type class instance for allowing direct indexing notation.
-/
instance : GetElem (NonEmpty α) Nat α inBounds where
  getElem := get

/--
Convert a `List.NonEmpty` into a plain `List`.
-/
def toList (xs : NonEmpty α) : List α := xs

/--
Retrieve the last member of the `List.NonEmpty`.
-/
def last : NonEmpty α → α
  | ⟨head, []⟩ => head
  | ⟨_, cons x xs⟩ => last (cons x xs)

end NonEmpty

end List