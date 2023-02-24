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
  | snoc  is ts => Tuple.concat is.norm ts

/--
Casts a tuple indexed by `m` to one indexed by `n`.
-/
theorem lift_eq_size : (m = n) → (Tuple α m = Tuple α n) :=
  fun h => by rw [h]

/--
Normalization distributes when the `snd` component is `nil`.
-/
theorem distrib_norm_snoc_nil {t : XTuple α (p, q)}
  : norm (snoc t t[]) = norm t :=
  sorry

/--
Normalizing an `XTuple` is equivalent to concatenating the `fst` component (in
normal form) with the second.
-/
theorem norm_snoc_eq_concat {t₁ : XTuple α (p, q)} {t₂ : Tuple α n}
  : norm (snoc t₁ t₂) = t₁.norm.concat t₂ :=
  Tuple.recOn
    (motive := fun k t => norm (snoc t₁ t) = t₁.norm.concat t)
    t₂
    (calc
      norm (snoc t₁ t[])
          = t₁.norm := distrib_norm_snoc_nil
        _ = t₁.norm.concat t[] := by rw [Tuple.self_concat_nil_eq_self])
    (sorry)

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
def fst : XTuple α (m, n) → Tuple α m
  | x[] => t[]
  | snoc ts _ => ts.norm

/--
Given `XTuple α (m, n)`, the `fst` component is equal to an initial segment of
size `k` of the tuple in normal form.
-/
theorem self_fst_eq_norm_take (t : XTuple α (m, n))
  : cast (by simp) (t.norm.take m) = t.fst :=
  XTuple.casesOn
    (motive := fun (m, n) t => cast (by simp) (t.norm.take m) = t.fst)
    t
    rfl
    (@fun p q r t₁ t₂ => sorry)

/--
If the normal form of our `XTuple` is the same as another `Tuple`, the `fst`
component must be a prefix of the second.
-/
theorem norm_eq_fst_eq_take {t₁ : XTuple α (m, n)} {t₂ : Tuple α (m + n)}
  : (t₁.norm = t₂) → cast (by simp) (t₂.take m) = t₁.fst := by
  intro h
  sorry

/--
Returns the first component of our `XTuple`. For example, the first component of
tuple `x[x[1, 2], 3, 4]` is `t[3, 4]`.
-/
def snd : XTuple α (m, n) → Tuple α n
  | x[] => t[]
  | snoc _ ts => ts

section

variable {k m n : Nat}
variable (p : 1 ≤ m)
variable (q : n + (m - 1) = m + k)

namespace Lemma_0a

lemma n_eq_succ_k : n = k + 1 :=
  let ⟨m', h⟩ := Nat.exists_eq_succ_of_ne_zero $ show m ≠ 0 by
    intro h
    have ff : 1 ≤ 0 := h ▸ p
    ring_nf at ff
    exact ff.elim
  calc
    n = n + (m - 1) - (m - 1) := by rw [Nat.add_sub_cancel]
    _ = m' + 1 + k - (m' + 1 - 1) := by rw [q, h]
    _ = m' + 1 + k - m' := by simp
    _ = 1 + k + m' - m' := by rw [Nat.add_assoc, Nat.add_comm]
    _ = 1 + k := by simp
    _ = k + 1 := by rw [Nat.add_comm]

lemma min_comm_succ_eq : min (m + k) (k + 1) = k + 1 :=
  Nat.recOn k
    (by simp; exact p)
    (fun k' ih => calc
      min (m + (k' + 1)) (k' + 1 + 1)
          = min (m + k' + 1) (k' + 1 + 1) := by conv => rw [Nat.add_assoc]
        _ = min (m + k') (k' + 1) + 1 := Nat.min_succ_succ (m + k') (k' + 1)
        _ = k' + 1 + 1 := by rw [ih])

-- TODO: Consider using coercions and heterogeneous equality isntead of these.

def cast_norm : XTuple α (n, m - 1) → Tuple α (m + k)
  | xs => cast (lift_eq_size q) xs.norm 

def cast_fst : XTuple α (n, m - 1) → Tuple α (k + 1)
  | xs => cast (lift_eq_size (n_eq_succ_k p q)) xs.fst
  
def cast_init_seq (ys : Tuple α (m + k)) :=
  cast (lift_eq_size (min_comm_succ_eq p)) (ys.take (k + 1))

end Lemma_0a

open Lemma_0a

/--[1]
Assume that ⟨x₁, ..., xₘ⟩ = ⟨y₁, ..., yₘ, ..., yₘ₊ₖ⟩. Then x₁ = ⟨y₁, ..., yₖ₊₁⟩.
-/
theorem lemma_0a (xs : XTuple α (n, m - 1)) (ys : Tuple α (m + k))
  : (cast_norm q xs = ys) → (cast_fst p q xs = cast_init_seq p ys) :=
  fun h => sorry

end

end XTuple
