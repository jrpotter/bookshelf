import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

package «Common»

@[default_target]
lean_lib «Common» {
  roots := #["Bookshelf"]
}
