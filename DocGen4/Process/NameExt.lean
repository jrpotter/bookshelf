/-
A generalization of `Lean.Name` that includes a file extension.
-/
import Lean

open Lean Name

inductive Extension where
| html
| pdf
deriving Repr

namespace Extension

def cmp : Extension → Extension → Ordering
  | html, html => Ordering.eq
  | html, _ => Ordering.lt
  | pdf, pdf => Ordering.eq
  | pdf, _ => Ordering.gt

def toString : Extension → String
  | html => "html"
  | pdf => "pdf"

end Extension

structure NameExt where
  name : Name
  ext : Extension

namespace NameExt

def cmp (n₁ n₂ : NameExt) : Ordering :=
  match Name.cmp n₁.name n₂.name with
  | Ordering.eq => Extension.cmp n₁.ext n₂.ext
  | ord => ord

def getString! : NameExt → String
  | ⟨str _ s, .html⟩ => s
  | ⟨str _ s, .pdf⟩ => s ++ "_pdf"
  | _       => unreachable!

end NameExt
