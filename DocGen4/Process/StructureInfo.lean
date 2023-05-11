/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Lean

import DocGen4.Process.Base
import DocGen4.Process.NameInfo

namespace DocGen4.Process

open Lean Meta 

-- TODO: replace with Leos variant from Zulip
def dropArgs (type : Expr) (n : Nat) : (Expr × List (Name × Expr)) :=
  match type, n with
  | e, 0 => (e, [])
  | Expr.forallE name type body _, x + 1 =>
    let body := body.instantiate1 <| mkFVar ⟨name⟩
    let next := dropArgs body x
    { next with snd := (name, type) :: next.snd}
  | _, _ + 1 => panic! s!"No forallE left"

def getFieldTypes (struct : Name) (ctor : ConstructorVal) (parents : Nat) : MetaM (Array NameInfo) := do
  let type := ctor.type
  let (fieldFunction, _) := dropArgs type (ctor.numParams + parents)
  let (_, fields) := dropArgs fieldFunction (ctor.numFields - parents)
  let mut fieldInfos := #[]
  for (name, type) in fields do
    fieldInfos := fieldInfos.push <| ← NameInfo.ofTypedName (struct.append name) type
  return fieldInfos

def StructureInfo.ofInductiveVal (v : InductiveVal) : MetaM StructureInfo := do
  let info ← Info.ofConstantVal v.toConstantVal
  let env ← getEnv
  let parents := getParentStructures env v.name
  let ctorVal := getStructureCtor env v.name
  let ctor ← NameInfo.ofTypedName ctorVal.name ctorVal.type
  match getStructureInfo? env v.name with
  | some i =>
    if i.fieldNames.size - parents.size > 0 then
      return {
        toInfo := info,
        fieldInfo := ← getFieldTypes v.name ctorVal parents.size,
        parents,
        ctor
      }
    else
      return {
        toInfo := info,
        fieldInfo := #[],
        parents,
        ctor
      }
  | none => panic! s!"{v.name} is not a structure"

end DocGen4.Process
