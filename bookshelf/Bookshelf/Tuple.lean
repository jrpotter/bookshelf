/-
# References

1. Enderton, Herbert B. A Mathematical Introduction to Logic. 2nd ed. San Diego:
   Harcourt/Academic Press, 2001.
2. Axler, Sheldon. Linear Algebra Done Right. Undergraduate Texts in
   Mathematics. Cham: Springer International Publishing, 2015.
   https://doi.org/10.1007/978-3-319-11080-6.
-/

import Mathlib.Tactic.Ring

universe u

/--
As described in [1], `n`-tuples are defined recursively as such:

  `⟨x₁, ..., xₙ⟩ = ⟨⟨x₁, ..., xₙ₋₁⟩, xₙ⟩`

We allow for empty tuples; [2] expects this functionality.

For a `Tuple`-like type with opposite "endian", refer to `Vector`.

TODO: It would be nice to define `⟨x⟩ = x`. It's not clear to me yet how to do
so or whether I could leverage a simple isomorphism everywhere I would like
this.
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
Implements decidable equality for `Tuple α m`, provided `a` has decidable equality. 
-/
protected def hasDecEq [DecidableEq α] (t₁ t₂ : Tuple α n) : Decidable (Eq t₁ t₂) :=
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

/--
Returns the number of entries of the `Tuple`.
-/
def size (_ : Tuple α n) : Nat := n

/--
Returns all but the last entry of the `Tuple`.
-/
def init : Tuple α n → 1 ≤ n → Tuple α (n - 1)
  | snoc vs _, _ => vs

/--
Returns the last entry of the `Tuple`.
-/
def last : Tuple α n → 1 ≤ n → α
  | snoc _ v, _ => v  

/--
Prepends an entry to the start of the `Tuple`.
-/
def cons : Tuple α n → α → Tuple α (n + 1)
  | t[], a => t[a]
  | snoc ts t, a => snoc (cons ts a) t

/--
Join two `Tuple`s together end to end.
-/
def concat : Tuple α m → Tuple α n → Tuple α (m + n)
  | t[], ts => cast (by simp) ts
  | is, t[] => is
  | is, snoc ts t => snoc (concat is ts) t

/--
Take the first `k` entries from the `Tuple` to form a new `Tuple`.
-/
def take (t : Tuple α n) (k : Nat) (p : 1 ≤ k ∧ k ≤ n) : Tuple α k :=
  have _ : 1 ≤ n := Nat.le_trans p.left p.right
  match t with
  | @snoc _ n' init last => by
      by_cases h : k = n' + 1
      · rw [h]; exact snoc init last
      · exact take init k (And.intro p.left $
          have h' : k + 1 ≤ n' + 1 := Nat.lt_of_le_of_ne p.right h
          by simp at h'; exact h')

end Tuple
