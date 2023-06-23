import Common.Set.OrderedPair
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Prod

/-! # Relations

A representation of a relation, i.e. a set of ordered pairs. Like `Set`, it is
assumed a relation is homogeneous.
-/

namespace Set

/--
A relation type as defined by Enderton.

We choose to use tuples to represent our ordered pairs, as opposed to
Kuratowski's definition of a set.

Not to be confused with the Lean-provided `Rel`.
-/
abbrev Relation (α : Type _) := Set (α × α)

namespace Relation

/--
The domain of a `Relation`.
-/
def dom (R : Relation α) : Set α := Prod.fst '' R

/--
The range of a `Relation`.
-/
def ran (R : Relation α) : Set α := Prod.snd '' R

/--
The field of a `Relation`.
-/
def fld (R : Relation α) : Set α := dom R ∪ ran R

/--
The inverse of a `Relation`.
-/
def inv (R : Relation α) : Relation α := { (p.2, p.1) | p ∈ R }

/--
The composition of two `Relation`s.
-/
def comp (F G : Relation α) : Relation α :=
  { p | ∃ t, (p.1, t) ∈ G ∧ (t, p.2) ∈ F}

/--
The restriction of a `Relation` to a `Set`.
-/
def restriction (R : Relation α) (A : Set α) : Relation α :=
  { p ∈ R | p.1 ∈ A } 

/--
The image of a `Relation` under a `Set`.
-/
def image (R : Relation α) (A : Set α) : Set α :=
  { y | ∃ u ∈ A, (u, y) ∈ R }

/--
A `Relation` `R` is said to be single-rooted **iff** for all `y ∈ ran R`, there
exists exactly one `x` such that `⟨x, y⟩ ∈ R`.
-/
def isSingleRooted (R : Relation α) : Prop :=
  ∀ y ∈ R.ran, ∃! x, x ∈ R.dom ∧ (x, y) ∈ R

/--
A `Relation` `R` is said to be single-valued **iff** for all `x ∈ dom R`, there
exists exactly one `y` such that `⟨x, y⟩ ∈ R`.

Notice, a `Relation` that is single-valued is a function.
-/
def isSingleValued (R : Relation α) : Prop :=
  ∀ x ∈ R.dom, ∃! y, y ∈ R.ran ∧ (x, y) ∈ R

/--
Convert a `Relation` into an equivalent representation using `OrderedPair`s.
-/
def toOrderedPairs (R : Relation α) : Set (Set (Set α)) :=
  -- Notice here we are using `Set.image` and *not* `Set.Relation.image`.
  Set.image (fun (x, y) => OrderedPair x y) R

end Relation

end Set