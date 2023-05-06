import Lake

open Lake DSL

package «bookshelf»

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "d65ed3b2920dbfb0b2bf1aca2189ec177eb68980"
require std4 from git
  "https://github.com/leanprover/std4.git" @
    "6006307d2ceb8743fea7e00ba0036af8654d0347"
require «doc-gen4» from git
  "https://github.com/jrpotter/bookshelf-docgen.git" @
    "b083d636c2581e72da9d18023240319dd5eca43a"

@[default_target]
lean_lib «Bookshelf» {
  roots := #[`Bookshelf, `Exercises]
}

/--
The contents of our `.env` file.
-/
structure Config where
  port : Nat := 5555

/--
Read in the `.env` file into an in-memory structure.
-/
private def readConfig : StateT Config ScriptM Unit := do
  let env <- IO.FS.readFile ".env"
  for line in env.trim.split (fun c => c == '\n') do
    match line.split (fun c => c == '=') with
    | ["PORT", port] => modify (fun c => { c with port := String.toNat! port })
    | _ => error "Malformed `.env` file."
  return ()

/--
Start an HTTP server for locally serving documentation. It is expected the
documentation has already been generated prior via

```bash
> lake build Bookshelf:docs
```

USAGE:
  lake run server
-/
script server (_args) do
  let ((), config) <- StateT.run readConfig {}
  IO.println s!"Running Lean on `http://localhost:{config.port}`"
  _ <- IO.Process.run {
    cmd := "python3",
    args := #["-m", "http.server", toString config.port, "-d", "build/doc"],
  }
  return 0
