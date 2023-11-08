/-
Copyright (c) 2021 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Lean
import Lean.Data.HashMap

import DocGen4.Process.NameExt

def Lean.HashSet.fromArray [BEq α] [Hashable α] (xs : Array α) : Lean.HashSet α :=
  xs.foldr (flip .insert) .empty

namespace DocGen4

open Lean Name

def getNLevels (name : Name) (levels: Nat) : Name :=
  let components := name.componentsRev
  (components.drop (components.length - levels)).reverse.foldl (· ++ ·) Name.anonymous

inductive Hierarchy where
| node (name : NameExt) (isFile : Bool) (children : RBNode NameExt (fun _ => Hierarchy)) : Hierarchy

instance : Inhabited Hierarchy := ⟨Hierarchy.node ⟨.anonymous, .html⟩ false RBNode.leaf⟩

abbrev HierarchyMap := RBNode NameExt (fun _ => Hierarchy)

-- Everything in this namespace is adapted from stdlib's RBNode
namespace HierarchyMap

def toList : HierarchyMap → List (NameExt × Hierarchy)
| t => t.revFold (fun ps k v => (k, v)::ps) []

def toArray : HierarchyMap → Array (NameExt × Hierarchy)
| t => t.fold (fun ps k v => ps ++ #[(k, v)] ) #[]

def hForIn [Monad m] (t : HierarchyMap) (init : σ) (f : (NameExt × Hierarchy) → σ → m (ForInStep σ)) : m σ :=
  t.forIn init (fun a b acc => f (a, b) acc)

instance : ForIn m HierarchyMap (NameExt × Hierarchy) where
  forIn := HierarchyMap.hForIn

end HierarchyMap

namespace Hierarchy

def empty (n : NameExt) (isFile : Bool) : Hierarchy :=
  node n isFile RBNode.leaf

def getName : Hierarchy → Name
| node n _ _ => n.name

def getNameExt : Hierarchy → NameExt
| node n _ _ => n

def getChildren : Hierarchy → HierarchyMap
| node _ _ c => c

def isFile : Hierarchy → Bool
| node _ f _ => f

partial def insert! (h : Hierarchy) (n : NameExt) : Hierarchy := Id.run do
  let hn := h.getNameExt
  let mut cs := h.getChildren

  if getNumParts hn.name + 1 == getNumParts n.name then
    match cs.find NameExt.cmp n with
    | none =>
      node hn h.isFile (cs.insert NameExt.cmp n <| empty n true)
    | some (node _ true _) => h
    | some (node _ false ccs) =>
        cs := cs.erase NameExt.cmp n
        node hn h.isFile (cs.insert NameExt.cmp n <| node n true ccs)
  else
    let leveled := ⟨getNLevels n.name (getNumParts hn.name + 1), .html⟩
    match cs.find NameExt.cmp leveled with
    | some nextLevel =>
      cs := cs.erase NameExt.cmp leveled
      -- BUG?
      node hn h.isFile <| cs.insert NameExt.cmp leveled (nextLevel.insert! n)
    | none =>
      let child := (insert! (empty leveled false) n)
      node hn h.isFile <| cs.insert NameExt.cmp leveled child

partial def fromArray (names : Array Name) : Hierarchy :=
   (names.map (fun n => NameExt.mk n .html)).foldl insert! (empty ⟨anonymous, .html⟩ false)

partial def fromArrayExt (names : Array NameExt) : Hierarchy :=
  names.foldl insert! (empty ⟨anonymous, .html⟩ false)

def baseDirBlackList : HashSet String :=
  HashSet.fromArray #[
    "404.html",
    "color-scheme.js",
    "declaration-data.js",
    "declarations",
    "expand-nav.js",
    "find",
    "foundational_types.html",
    "how-about.js",
    "index.html",
    "jump-src.js",
    "mathjax-config.js",
    "navbar.html",
    "nav.js",
    "search.html",
    "search.js",
    "src",
    "style.css"
  ]

partial def fromDirectoryAux (dir : System.FilePath) (previous : Name) : IO (Array NameExt) := do
  let mut children := #[]
  for entry in ← System.FilePath.readDir dir do
    if ← entry.path.isDir then
      children := children ++ (← fromDirectoryAux entry.path (.str previous entry.fileName))
    else if entry.path.extension = some "html" then
      children := children.push <| ⟨.str previous (entry.fileName.dropRight ".html".length), .html⟩
    else if entry.path.extension = some "pdf" then
      children := children.push <| ⟨.str previous (entry.fileName.dropRight ".pdf".length), .pdf⟩
  return children

def fromDirectory (dir : System.FilePath) : IO Hierarchy := do
    let mut children := #[]
    for entry in ← System.FilePath.readDir dir do
      if baseDirBlackList.contains entry.fileName then
        continue
      else if ← entry.path.isDir then
        children := children ++ (← fromDirectoryAux entry.path (.mkSimple entry.fileName))
      else if entry.path.extension = some "html" then
        children := children.push <| ⟨.mkSimple (entry.fileName.dropRight ".html".length), .html⟩
      else if entry.path.extension = some "pdf" then
        children := children.push <| ⟨.mkSimple (entry.fileName.dropRight ".pdf".length), .pdf⟩
    return Hierarchy.fromArrayExt children

end Hierarchy
end DocGen4
