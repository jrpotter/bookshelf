import Lake
open Lake DSL

package «first-course-abstract-algebra»

require Bookshelf from "../bookshelf"
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "0107c50abf149a48b5b9ad08a0b2a2093bcb567a"

@[default_target]
lean_lib «FirstCourseAbstractAlgebra» {
  -- add library configuration options here
}
