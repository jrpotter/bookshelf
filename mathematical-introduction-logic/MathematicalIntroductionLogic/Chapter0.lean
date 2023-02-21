/-
# References

1. Enderton, Herbert B. A Mathematical Introduction to Logic. 2nd ed. San Diego:
   Harcourt/Academic Press, 2001.
-/

import Bookshelf.Tuple

/--
The following describes a so-called "generic" tuple. Like in `Bookshelf.Tuple`,
an `n`-tuple is defined recursively like so:

  `⟨x₁, ..., xₙ⟩ = ⟨⟨x₁, ..., xₙ₋₁⟩, xₙ⟩`

Unlike `Bookshelf.Tuple`, a "generic" tuple bends the syntax above further. For
example, both tuples above are equivalent to:

  `⟨⟨x₁, ..., xₘ⟩, xₘ₊₁, ..., xₙ⟩`

for some `1 ≤ m ≤ n`. This distinction is purely syntactic, but necessary to
prove certain theorems found in [1] (e.g. `lemma_0a`).

In general, prefer `Bookshelf.Tuple`.
-/
inductive XTuple : (α : Type u) → (size : Nat × Nat) → Type u where
  | nil : XTuple α (0, 0)
  | snoc : XTuple α (p, q) → Tuple α r → XTuple α (p + q, r)

syntax (priority := high) "x[" term,* "]" : term

macro_rules
  | `(x[]) => `(XTuple.nil)
  | `(x[$x]) => `(XTuple.snoc x[] t[$x])
  | `(x[x[$xs:term,*], $ys:term,*]) => `(XTuple.snoc x[$xs,*] t[$ys,*])
  | `(x[$x, $xs:term,*]) => `(XTuple.snoc x[] t[$x, $xs,*])

namespace XTuple

/--
Converts an `XTuple` into "normal form".
-/
def norm : XTuple α (m, n) → Tuple α (m + n)
  |         x[] => t[]
  | snoc x[] ts => cast (by simp) ts
  | snoc  is ts => is.norm.concat ts

/--
Casts a tuple indexed by `m` to one indexed by `n`.
-/
theorem cast_eq_size : (m = n) → (Tuple α m = Tuple α n) :=
  fun h => by rw [h]

/--
Implements Boolean equality for `XTuple α n` provided `α` has decidable
equality.
-/
instance BEq [DecidableEq α] : BEq (XTuple α n) where
  beq t₁ t₂ := t₁.norm == t₂.norm

/--
Returns the number of entries in the `XTuple`.
-/
def size (_ : XTuple α n) := n

/--
Returns the number of entries in the "shallowest" portion of the `XTuple`. For
example, the length of `x[x[1, 2], 3, 4]` is `3`, despite its size being `4`.
-/
def length : XTuple α n → Nat
  |         x[] => 0
  | snoc x[] ts => ts.size
  | snoc   _ ts => 1 + ts.size

/--
Returns the first component of our `XTuple`. For example, the first component of
tuple `x[x[1, 2], 3, 4]` is `t[1, 2]`.
-/
def first : XTuple α (m, n) → 1 ≤ m → Tuple α m
  | snoc ts _, _ => ts.norm

section

variable {k m n : Nat}
variable (p : n + (m - 1) = m + k)
variable (qₙ : 1 ≤ n)
variable (qₘ : 1 ≤ m)

namespace Lemma_0a

lemma aux1 : n = k + 1 := sorry

lemma aux2 : 1 ≤ m → 1 ≤ k + 1 ∧ k + 1 ≤ m + k := sorry

end Lemma_0a

open Lemma_0a

/--[1]
Assume that ⟨x₁, ..., xₘ⟩ = ⟨y₁, ..., yₘ, ..., yₘ₊ₖ⟩. Then x₁ = ⟨y₁, ..., yₖ₊₁⟩.
-/
theorem lemma_0a (xs : XTuple α (n, m - 1)) (ys : Tuple α (m + k))
  : (cast (cast_eq_size p) xs.norm = ys)
  → (cast (cast_eq_size aux1) (xs.first qₙ) = ys.take (k + 1) (aux2 qₘ))
  := sorry

end

end XTuple
