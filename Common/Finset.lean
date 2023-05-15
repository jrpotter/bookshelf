import Mathlib.Data.Finset.Basic

/-! # Common.Finset

Additional theorems and definitions useful in the context of `Finset`s.
-/

namespace Finset

/--
An alternative `Finset.range` function that returns `Fin` indices instead of `ℕ`
indices.
-/
def finRange (n : ℕ) : Finset (Fin n) :=
  ⟨sorry, sorry⟩

end Finset