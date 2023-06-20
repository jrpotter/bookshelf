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
Convert a `Relation` into an equivalent representation using `OrderedPair`s.
-/
def toOrderedPairs (R : Relation α) : Set (Set (Set α)) :=
  R.image (fun (x, y) => OrderedPair x y)

end Relation

end Set