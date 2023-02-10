import Lake
open Lake DSL

package «bookshelf» {
  -- add package configuration options here
}

lean_lib «Bookshelf» {
  -- add library configuration options here
}

@[default_target]
lean_exe «bookshelf» {
  root := `Main
}
