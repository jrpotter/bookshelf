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

open scoped Tuple

/- -------------------------------------
 - Normalization
 - -------------------------------------/

/--
Converts an `XTuple` into "normal form".
-/
def norm : XTuple α (m, n) → Tuple α (m + n)
  |         x[] => t[]
  | snoc  is ts => Tuple.concat is.norm ts

/--
Normalization of an empty `XTuple` yields an empty `Tuple`.
-/
theorem norm_nil_eq_nil : @norm α 0 0 nil = Tuple.nil :=
  rfl

/--
Normalization of a pseudo-empty `XTuple` yields an empty `Tuple`.
-/
theorem norm_snoc_nil_nil_eq_nil : @norm α 0 0 (snoc x[] t[]) = t[] := by
  unfold norm norm
  rfl

/--
Normalization elimates `snoc` when the `snd` component is `nil`.
-/
theorem norm_snoc_nil_elim {t : XTuple α (p, q)}
  : norm (snoc t t[]) = norm t :=
  XTuple.casesOn t
    (motive := fun _ t => norm (snoc t t[]) = norm t)
    (by simp; unfold norm norm; rfl)
    (fun tf tl => by
      simp
      conv => lhs; unfold norm)

/--
Normalization eliminates `snoc` when the `fst` component is `nil`.
-/
theorem norm_nil_snoc_elim {ts : Tuple α n} : norm (snoc x[] ts) = cast (by simp) ts := by
  unfold norm norm
  rw [Tuple.nil_concat_self_eq_self]

/--
Normalization distributes across `Tuple.snoc` calls.
-/
theorem norm_snoc_snoc_norm
  : norm (snoc as (Tuple.snoc bs b)) = Tuple.snoc (norm (snoc as bs)) b := by
  unfold norm
  rw [←Tuple.concat_snoc_snoc_concat]

/--
Normalizing an `XTuple` is equivalent to concatenating the normalized `fst`
component with the `snd`.
-/
theorem norm_snoc_eq_concat {t₁ : XTuple α (p, q)} {t₂ : Tuple α n}
  : norm (snoc t₁ t₂) = Tuple.concat t₁.norm t₂ := by
  conv => lhs; unfold norm

/- -------------------------------------
 - Equality
 - -------------------------------------/

/--
Implements Boolean equality for `XTuple α n` provided `α` has decidable
equality.
-/
instance BEq [DecidableEq α] : BEq (XTuple α n) where
  beq t₁ t₂ := t₁.norm == t₂.norm

/- -------------------------------------
 - Basic API
 - -------------------------------------/

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
theorem self_fst_eq_norm_take (t : XTuple α (m, n)) : t.fst = t.norm.take m :=
  match t with
  | x[] => by unfold fst; rw [Tuple.self_take_zero_eq_nil]; simp
  | snoc tf tl => by
    unfold fst
    conv => rhs; unfold norm
    rw [Tuple.eq_take_concat]
    simp

/--
If the normal form of an `XTuple` is equal to a `Tuple`, the `fst` component
must be a prefix of the `Tuple`.
-/
theorem norm_eq_fst_eq_take {t₁ : XTuple α (m, n)} {t₂ : Tuple α (m + n)}
  : (t₁.norm = t₂) → (t₁.fst = t₂.take m) :=
  fun h => by rw [self_fst_eq_norm_take, h]

/--
Returns the first component of our `XTuple`. For example, the first component of
tuple `x[x[1, 2], 3, 4]` is `t[3, 4]`.
-/
def snd : XTuple α (m, n) → Tuple α n
  | x[] => t[]
  | snoc _ ts => ts

/- -------------------------------------
 - Lemma 0A
 - -------------------------------------/

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
  
lemma n_pred_eq_k : n - 1 = k := by
  have h : k + 1 - 1 = k + 1 - 1 := rfl
  conv at h => lhs; rw [←n_eq_succ_k p q]
  simp at h
  exact h
  
lemma n_geq_one : 1 ≤ n := by
  rw [n_eq_succ_k p q]
  simp

lemma min_comm_succ_eq : min (m + k) (k + 1) = k + 1 :=
  Nat.recOn k
    (by simp; exact p)
    (fun k' ih => calc
      min (m + (k' + 1)) (k' + 1 + 1)
          = min (m + k' + 1) (k' + 1 + 1) := by conv => rw [Nat.add_assoc]
        _ = min (m + k') (k' + 1) + 1 := Nat.min_succ_succ (m + k') (k' + 1)
        _ = k' + 1 + 1 := by rw [ih])

lemma n_eq_min_comm_succ : n = min (m + k) (k + 1) := by
  rw [min_comm_succ_eq p]
  exact n_eq_succ_k p q

lemma n_pred_m_eq_m_k : n + (m - 1) = m + k := by
  rw [←Nat.add_sub_assoc p, Nat.add_comm, Nat.add_sub_assoc (n_geq_one p q)]
  conv => lhs; rw [n_pred_eq_k p q]

def cast_norm : XTuple α (n, m - 1) → Tuple α (m + k)
  | xs => cast (by rw [q]) xs.norm

def cast_fst : XTuple α (n, m - 1) → Tuple α (k + 1)
  | xs => cast (by rw [n_eq_succ_k p q]) xs.fst
  
def cast_take (ys : Tuple α (m + k)) :=
  cast (by rw [min_comm_succ_eq p]) (ys.take (k + 1))

end Lemma_0a

open Lemma_0a

/--[1]
Assume that ⟨x₁, ..., xₘ⟩ = ⟨y₁, ..., yₘ, ..., yₘ₊ₖ⟩. Then x₁ = ⟨y₁, ..., yₖ₊₁⟩.
-/
theorem lemma_0a (xs : XTuple α (n, m - 1)) (ys : Tuple α (m + k))
  : (cast_norm q xs = ys) → (cast_fst p q xs = cast_take p ys) := by
  intro h
  suffices HEq
    (cast (_ : Tuple α n = Tuple α (k + 1)) (fst xs))
    (cast (_ : Tuple α (min (m + k) (k + 1)) = Tuple α (k + 1)) (Tuple.take ys (k + 1)))
    from eq_of_heq this
  congr
  · exact n_eq_min_comm_succ p q
  · rfl
  · exact n_eq_min_comm_succ p q
  · exact HEq.rfl
  · exact Eq.recOn
      (motive := fun _ h => HEq
        (_ : n + (n - 1) = n + k)
        (cast h (show n + (n - 1) = n + k by rw [n_pred_eq_k p q])))
      (show (n + (n - 1) = n + k) = (min (m + k) (k + 1) + (n - 1) = n + k) by
        rw [n_eq_min_comm_succ p q])
      HEq.rfl
  · exact n_geq_one p q
  · exact n_pred_eq_k p q
  · exact Eq.symm (n_eq_min_comm_succ p q)
  · exact n_pred_eq_k p q
  · rw [self_fst_eq_norm_take]
    unfold cast_norm at h
    simp at h
    rw [←h, ←n_eq_succ_k p q]
    have h₂ := Eq.recOn
      (motive := fun x h => HEq
        (Tuple.take xs.norm n)
        (Tuple.take (cast (show Tuple α (n + (m - 1)) = Tuple α x by rw [h]) xs.norm) n))
      (show n + (m - 1) = m + k by rw [n_pred_m_eq_m_k p q])
      HEq.rfl
    exact Eq.recOn
      (motive := fun x h => HEq
        (cast h (Tuple.take xs.norm n))
        (Tuple.take (cast (_ : Tuple α (n + (m - 1)) = Tuple α (m + k)) xs.norm) n))
      (show Tuple α (min (n + (m - 1)) n) = Tuple α n by simp)
      h₂

end

end XTuple
