import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

package «bookshelf» {
  -- add package configuration options here
}

@[default_target]
lean_lib «Bookshelf» {
  -- add library configuration options here
}
