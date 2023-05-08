import Common.LTuple.Basic

/-! # Enderton.Chapter0

Useful Facts About Sets
-/

namespace Enderton.Chapter0

/--
The following describes a so-called "generic" tuple. Like an `LTuple`, a generic
`n`-tuple is defined recursively like so:

  `⟨x₁, ..., xₙ⟩ = ⟨⟨x₁, ..., xₙ₋₁⟩, xₙ⟩`

Unlike `LTuple`, this tuple bends the syntax above further. For example,
both tuples above are equivalent to:

  `⟨⟨x₁, ..., xₘ⟩, xₘ₊₁, ..., xₙ⟩`

for some `1 ≤ m ≤ n`. This distinction is purely syntactic, and introduced
solely to prove `lemma_0a`. In other words, `LTuple` is an always-normalized
variant of an `GTuple`. In general, prefer it over this when working within
Enderton's book.
-/
inductive GTuple : (α : Type u) → (size : Nat × Nat) → Type u where
  | nil : GTuple α (0, 0)
  | snoc : GTuple α (p, q) → LTuple α r → GTuple α (p + q, r)

syntax (priority := high) "t[" term,* "]" : term

macro_rules
  | `(t[]) => `(LTuple.nil)
  | `(t[$x]) => `(LTuple.snoc t[] $x)
  | `(t[$xs:term,*, $x]) => `(LTuple.snoc t[$xs,*] $x)

syntax (priority := high) "g[" term,* "]" : term

macro_rules
  | `(g[]) => `(GTuple.nil)
  | `(g[$x]) => `(GTuple.snoc g[] t[$x])
  | `(g[g[$xs:term,*], $ys:term,*]) => `(GTuple.snoc g[$xs,*] t[$ys,*])
  | `(g[$x, $xs:term,*]) => `(GTuple.snoc g[] t[$x, $xs,*])

namespace GTuple

open scoped LTuple

/-! ## Normalization -/

/--
Converts an `GTuple` into "normal form".
-/
def norm : GTuple α (m, n) → LTuple α (m + n)
  |         g[] => t[]
  | snoc  is ts => LTuple.concat is.norm ts

/--
Normalization of an empty `GTuple` yields an empty `Tuple`.
-/
theorem norm_nil_eq_nil : @norm α 0 0 nil = LTuple.nil :=
  rfl

/--
Normalization of a pseudo-empty `GTuple` yields an empty `Tuple`.
-/
theorem norm_snoc_nil_nil_eq_nil : @norm α 0 0 (snoc g[] t[]) = t[] := by
  unfold norm norm
  rfl

/--
Normalization elimates `snoc` when the `snd` component is `nil`.
-/
theorem norm_snoc_nil_elim {t : GTuple α (p, q)}
  : norm (snoc t t[]) = norm t := by
  cases t with
  | nil => simp; unfold norm norm; rfl
  | snoc tf tl =>
      simp
      conv => lhs; unfold norm

/--
Normalization eliminates `snoc` when the `fst` component is `nil`.
-/
theorem norm_nil_snoc_elim {ts : LTuple α n}
  : norm (snoc g[] ts) = cast (by simp) ts := by
  unfold norm norm
  rw [LTuple.nil_concat_self_eq_self]

/--
Normalization distributes across `Tuple.snoc` calls.
-/
theorem norm_snoc_snoc_norm
  : norm (snoc as (LTuple.snoc bs b)) = LTuple.snoc (norm (snoc as bs)) b := by
  unfold norm
  rw [← LTuple.concat_snoc_snoc_concat]

/--
Normalizing an `GTuple` is equivalent to concatenating the normalized `fst`
component with the `snd`.
-/
theorem norm_snoc_eq_concat {t₁ : GTuple α (p, q)} {t₂ : LTuple α n}
  : norm (snoc t₁ t₂) = LTuple.concat t₁.norm t₂ := by
  conv => lhs; unfold norm

/-! ## Equality -/

/--
Implements Boolean equality for `GTuple α n` provided `α` has decidable
equality.
-/
instance BEq [DecidableEq α] : BEq (GTuple α n) where
  beq t₁ t₂ := t₁.norm == t₂.norm

/-! ## Basic API -/

/--
Returns the number of entries in the `GTuple`.
-/
def size (_ : GTuple α n) := n

/--
Returns the number of entries in the "shallowest" portion of the `GTuple`. For
example, the length of `x[x[1, 2], 3, 4]` is `3`, despite its size being `4`.
-/
def length : GTuple α n → Nat
  |         g[] => 0
  | snoc g[] ts => ts.size
  | snoc   _ ts => 1 + ts.size

/--
Returns the first component of our `GTuple`. For example, the first component of
tuple `x[x[1, 2], 3, 4]` is `t[1, 2]`.
-/
def fst : GTuple α (m, n) → LTuple α m
  | g[] => t[]
  | snoc ts _ => ts.norm

/--
Given `GTuple α (m, n)`, the `fst` component is equal to an initial segment of
size `k` of the tuple in normal form.
-/
theorem self_fst_eq_norm_take (t : GTuple α (m, n)) : t.fst = t.norm.take m :=
  match t with
  | g[] => by
    unfold fst
    rw [LTuple.self_take_zero_eq_nil]
    simp
  | snoc tf tl => by
    unfold fst
    conv => rhs; unfold norm
    rw [LTuple.eq_take_concat]
    simp

/--
If the normal form of an `GTuple` is equal to a `Tuple`, the `fst` component
must be a prefix of the `Tuple`.
-/
theorem norm_eq_fst_eq_take {t₁ : GTuple α (m, n)} {t₂ : LTuple α (m + n)}
  : (t₁.norm = t₂) → (t₁.fst = t₂.take m) := by
  intro h
  rw [self_fst_eq_norm_take, h]

/--
Returns the first component of our `GTuple`. For example, the first component of
tuple `x[x[1, 2], 3, 4]` is `t[3, 4]`.
-/
def snd : GTuple α (m, n) → LTuple α n
  | g[] => t[]
  | snoc _ ts => ts

end GTuple

/-! ## Lemma 0A -/

section

variable {k m n : Nat}
variable (p : 1 ≤ m)
variable (q : n + (m - 1) = m + k)

private lemma n_eq_succ_k : n = k + 1 := by
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

private lemma n_pred_eq_k : n - 1 = k := by
  have h : k + 1 - 1 = k + 1 - 1 := rfl
  conv at h => lhs; rw [←n_eq_succ_k p q]
  simp at h
  exact h

private lemma n_geq_one : 1 ≤ n := by
  rw [n_eq_succ_k p q]
  simp

private lemma min_comm_succ_eq : min (m + k) (k + 1) = k + 1 :=
  Nat.recOn k
    (by simp; exact p)
    (fun k' ih => calc min (m + (k' + 1)) (k' + 1 + 1)
      _ = min (m + k' + 1) (k' + 1 + 1) := by conv => rw [Nat.add_assoc]
      _ = min (m + k') (k' + 1) + 1 := Nat.min_succ_succ (m + k') (k' + 1)
      _ = k' + 1 + 1 := by rw [ih])

private lemma n_eq_min_comm_succ : n = min (m + k) (k + 1) := by
  rw [min_comm_succ_eq p]
  exact n_eq_succ_k p q

private lemma n_pred_m_eq_m_k : n + (m - 1) = m + k := by
  rw [←Nat.add_sub_assoc p, Nat.add_comm, Nat.add_sub_assoc (n_geq_one p q)]
  conv => lhs; rw [n_pred_eq_k p q]

private def cast_norm : GTuple α (n, m - 1) → LTuple α (m + k)
  | xs => cast (by rw [q]) xs.norm

private def cast_fst : GTuple α (n, m - 1) → LTuple α (k + 1)
  | xs => cast (by rw [n_eq_succ_k p q]) xs.fst

private def cast_take (ys : LTuple α (m + k)) :=
  cast (by rw [min_comm_succ_eq p]) (ys.take (k + 1))

/-- #### Lemma 0A

Assume that `⟨x₁, ..., xₘ⟩ = ⟨y₁, ..., yₘ, ..., yₘ₊ₖ⟩`. Then
`x₁ = ⟨y₁, ..., yₖ₊₁⟩`.
-/
theorem lemma_0a (xs : GTuple α (n, m - 1)) (ys : LTuple α (m + k))
  : (cast_norm q xs = ys) → (cast_fst p q xs = cast_take p ys) := by
  intro h
  suffices HEq
    (cast (_ : LTuple α n = LTuple α (k + 1)) xs.fst)
    (cast (_ : LTuple α (min (m + k) (k + 1)) = LTuple α (k + 1)) (LTuple.take ys (k + 1)))
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
  · rw [GTuple.self_fst_eq_norm_take]
    unfold cast_norm at h
    simp at h
    rw [←h, ←n_eq_succ_k p q]
    have h₂ := Eq.recOn
      (motive := fun x h => HEq
        (LTuple.take xs.norm n)
        (LTuple.take (cast (show LTuple α (n + (m - 1)) = LTuple α x by rw [h]) xs.norm) n))
      (show n + (m - 1) = m + k by rw [n_pred_m_eq_m_k p q])
      HEq.rfl
    exact Eq.recOn
      (motive := fun x h => HEq
        (cast h (LTuple.take xs.norm n))
        (LTuple.take (cast (_ : LTuple α (n + (m - 1)) = LTuple α (m + k)) xs.norm) n))
      (show LTuple α (min (n + (m - 1)) n) = LTuple α n by simp)
      h₂

end

end Enderton.Chapter0