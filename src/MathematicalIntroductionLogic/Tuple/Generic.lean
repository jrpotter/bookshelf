import MathematicalIntroductionLogic.Tuple.Basic

/--
The following describes a so-called "generic" tuple. Like a `Tuple`, an
`n`-tuple is defined recursively like so:

  `⟨x₁, ..., xₙ⟩ = ⟨⟨x₁, ..., xₙ₋₁⟩, xₙ⟩`

Unlike `Tuple`, a "generic" tuple bends the syntax above further. For example,
both tuples above are equivalent to:

  `⟨⟨x₁, ..., xₘ⟩, xₘ₊₁, ..., xₙ⟩`

for some `1 ≤ m ≤ n`. This distinction is purely syntactic, but necessary to
prove certain theorems (e.g. `Chapter0.lemma_0a`). In other words, `Tuple` is an
always-normalized variant of an `GTuple`. In general, prefer it over this when
working within Enderton's book.
-/
inductive GTuple : (α : Type u) → (size : Nat × Nat) → Type u where
  | nil : GTuple α (0, 0)
  | snoc : GTuple α (p, q) → Tuple α r → GTuple α (p + q, r)

syntax (priority := high) "g[" term,* "]" : term

macro_rules
  | `(g[]) => `(GTuple.nil)
  | `(g[$x]) => `(GTuple.snoc g[] t[$x])
  | `(g[g[$xs:term,*], $ys:term,*]) => `(GTuple.snoc g[$xs,*] t[$ys,*])
  | `(g[$x, $xs:term,*]) => `(GTuple.snoc g[] t[$x, $xs,*])

namespace GTuple

open scoped Tuple

-- ========================================
-- Normalization
-- ========================================

/--
Converts an `GTuple` into "normal form".
-/
def norm : GTuple α (m, n) → Tuple α (m + n)
  |         g[] => t[]
  | snoc  is ts => Tuple.concat is.norm ts

/--
Normalization of an empty `GTuple` yields an empty `Tuple`.
-/
theorem norm_nil_eq_nil : @norm α 0 0 nil = Tuple.nil :=
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
theorem norm_nil_snoc_elim {ts : Tuple α n}
  : norm (snoc g[] ts) = cast (by simp) ts := by
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
Normalizing an `GTuple` is equivalent to concatenating the normalized `fst`
component with the `snd`.
-/
theorem norm_snoc_eq_concat {t₁ : GTuple α (p, q)} {t₂ : Tuple α n}
  : norm (snoc t₁ t₂) = Tuple.concat t₁.norm t₂ := by
  conv => lhs; unfold norm

-- ========================================
-- Equality
-- ========================================

/--
Implements Boolean equality for `GTuple α n` provided `α` has decidable
equality.
-/
instance BEq [DecidableEq α] : BEq (GTuple α n) where
  beq t₁ t₂ := t₁.norm == t₂.norm

-- ========================================
-- Basic API
-- ========================================

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
def fst : GTuple α (m, n) → Tuple α m
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
    rw [Tuple.self_take_zero_eq_nil]
    simp
  | snoc tf tl => by
    unfold fst
    conv => rhs; unfold norm
    rw [Tuple.eq_take_concat]
    simp

/--
If the normal form of an `GTuple` is equal to a `Tuple`, the `fst` component
must be a prefix of the `Tuple`.
-/
theorem norm_eq_fst_eq_take {t₁ : GTuple α (m, n)} {t₂ : Tuple α (m + n)}
  : (t₁.norm = t₂) → (t₁.fst = t₂.take m) := by
  intro h
  rw [self_fst_eq_norm_take, h]

/--
Returns the first component of our `GTuple`. For example, the first component of
tuple `x[x[1, 2], 3, 4]` is `t[3, 4]`.
-/
def snd : GTuple α (m, n) → Tuple α n
  | g[] => t[]
  | snoc _ ts => ts

end GTuple
