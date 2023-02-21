import Mathlib.Tactic.Ring

/--
A list-like structure with its size encoded in the type.

For a `Vector`-like type with opposite "endian", refer to `Tuple`.
-/
inductive Vector (α : Type u) : (size : Nat) → Type u where
  | nil : Vector α 0
  | cons : α → Vector α n → Vector α (n + 1)

syntax (priority := high) "v[" term,* "]" : term

macro_rules
  | `(v[]) => `(Vector.nil)
  | `(v[$x]) => `(Vector.cons $x v[])
  | `(v[$x, $xs:term,*]) => `(Vector.cons $x v[$xs,*])

namespace Vector

/--
Returns the number of entries in the `Vector`.
-/
def size (_ : Vector α n) : Nat := n

/--
Returns the first entry of the `Vector`.
-/
def head : Vector α n → 1 ≤ n → α
  | cons v _, _ => v

/--
Returns the last entry of the `Vector`.
-/
def last (v : Vector α n) : 1 ≤ n → α :=
  fun h =>
    match v with
    | nil => by ring_nf at h; exact h.elim
    | @cons _ n' v vs => if h' : n' > 0 then vs.last h' else v

/--
Returns all but the `head` of the `Vector`.
-/
def tail : Vector α n → 1 ≤ n → Vector α (n - 1)
  | cons _ vs, _ => vs

/--
Appends an entry to the end of the `Vector`.
-/
def snoc : Vector α n → α → Vector α (n + 1)
  | nil, a => v[a]
  | cons v vs, a => cons v (snoc vs a)

end Vector
