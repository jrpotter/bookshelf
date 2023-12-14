import Lake

open System Lake DSL

package «bookshelf»

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "v4.3.0"
require std from git
  "https://github.com/leanprover/std4.git" @
    "v4.3.0"
meta if get_config? env = some "dev" then
  require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @
    "main"

@[default_target]
lean_lib «Bookshelf» {
  roots := #[`Bookshelf, `Common]
}
