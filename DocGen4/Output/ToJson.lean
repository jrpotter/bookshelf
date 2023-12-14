import Lean
import DocGen4.Process
import DocGen4.Output.Base
import DocGen4.Output.Module
import Lean.Data.RBMap

namespace DocGen4.Output

open Lean

structure JsonDeclarationInfo where
  name : String
  kind : String
  doc : String
  docLink : String
  sourceLink : String
  line : Nat
  deriving FromJson, ToJson

structure JsonDeclaration where
  info : JsonDeclarationInfo
  header : String
deriving FromJson, ToJson

structure JsonInstance where
  name : String
  className : String
  typeNames : Array String
  deriving FromJson, ToJson

structure JsonModule where
  name : String
  declarations : List JsonDeclaration
  instances : Array JsonInstance
  imports : Array String
  deriving FromJson, ToJson

structure JsonHeaderIndex where
  declarations : List (String × JsonDeclaration) := []

structure JsonIndexedDeclarationInfo where
  kind : String
  docLink : String
  deriving FromJson, ToJson

structure JsonIndexedModule where
  importedBy : Array String
  url : String
  deriving FromJson, ToJson

structure JsonIndex where
  declarations : List (String × JsonIndexedDeclarationInfo) := []
  instances : HashMap String (RBTree String Ord.compare) := .empty
  modules : HashMap String JsonIndexedModule := {}
  instancesFor : HashMap String (RBTree String Ord.compare) := .empty

instance : ToJson JsonHeaderIndex where
  toJson idx := Json.mkObj <| idx.declarations.map (fun (k, v) => (k, toJson v))

instance : ToJson JsonIndex where
  toJson idx := Id.run do
    let jsonDecls := Json.mkObj <| idx.declarations.map (fun (k, v) => (k, toJson v))
    let jsonInstances := Json.mkObj <| idx.instances.toList.map (fun (k, v) => (k, toJson v.toArray))
    let jsonModules := Json.mkObj <| idx.modules.toList.map (fun (k, v) => (k, toJson v))
    let jsonInstancesFor := Json.mkObj <| idx.instancesFor.toList.map (fun (k, v) => (k, toJson v.toArray))
    let finalJson := Json.mkObj [
      ("declarations", jsonDecls),
      ("instances", jsonInstances),
      ("modules", jsonModules),
      ("instancesFor", jsonInstancesFor)
    ]
    return finalJson

def JsonHeaderIndex.addModule (index : JsonHeaderIndex) (module : JsonModule) : JsonHeaderIndex :=
  let merge idx decl := { idx with declarations := (decl.info.name, decl) :: idx.declarations }
  module.declarations.foldl merge index

def JsonIndex.addModule (index : JsonIndex) (module : JsonModule) : BaseHtmlM JsonIndex := do
  let mut index := index
  let newDecls := module.declarations.map (fun d => (d.info.name, {
    kind := d.info.kind,
    docLink := d.info.docLink,
  }))
  index := { index with
    declarations := newDecls ++ index.declarations
  }

  -- TODO: In theory one could sort instances and imports by name and batch the writes
  for inst in module.instances do
    let mut insts := index.instances.findD inst.className {}
    insts := insts.insert inst.name
    index := { index with instances := index.instances.insert inst.className insts }
    for typeName in inst.typeNames do
      let mut instsFor := index.instancesFor.findD typeName {}
      instsFor := instsFor.insert inst.name
      index := { index with instancesFor := index.instancesFor.insert typeName instsFor }

  -- TODO: dedup
  if index.modules.find? module.name |>.isNone then
    let moduleLink <- moduleNameToLink (String.toName module.name)
    let indexedModule := { url := moduleLink, importedBy := #[] }
    index := { index with modules := index.modules.insert module.name indexedModule }

  for imp in module.imports do
    let indexedImp ←
      match index.modules.find? imp with
      | some i => pure i
      | none =>
        let impLink ←  moduleNameToLink (String.toName imp)
        let indexedModule := { url := impLink, importedBy := #[] }
        pure indexedModule
    index := { index with
      modules :=
        index.modules.insert
        imp
        { indexedImp with importedBy := indexedImp.importedBy.push module.name }
    }
  return index

def DocInfo.toJson (module : Name) (info : Process.DocInfo) : HtmlM JsonDeclaration := do
  let name := info.getName.toString
  let kind := info.getKind
  let doc := info.getDocString.getD ""
  let docLink ← declNameToLink info.getName
  let sourceLink ← getSourceUrl module info.getDeclarationRange
  let line := info.getDeclarationRange.pos.line
  let header := (← docInfoHeader info).toString
  let info := { name, kind, doc, docLink, sourceLink, line }
  return { info, header }

def Process.Module.toJson (module : Process.Module) : HtmlM Json := do
    let mut jsonDecls := []
    let mut instances := #[]
    let declInfo := Process.filterDocInfo module.members
    for decl in declInfo do
      jsonDecls := (← DocInfo.toJson module.name decl) :: jsonDecls
      if let .instanceInfo i := decl then
        instances := instances.push {
          name := i.name.toString,
          className := i.className.toString
          typeNames := i.typeNames.map Name.toString
        }
    let jsonMod : JsonModule :=  {
      name := module.name.toString,
      declarations := jsonDecls,
      instances,
      imports := module.imports.map Name.toString
    }
    return ToJson.toJson jsonMod

end DocGen4.Output
