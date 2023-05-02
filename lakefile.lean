import Lake
open Lake DSL

package «bookshelf»

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "0107c50abf149a48b5b9ad08a0b2a2093bcb567a"
require std4 from git
  "https://github.com/leanprover/std4.git" @
    "6006307d2ceb8743fea7e00ba0036af8654d0347"

@[default_target]
lean_lib «Bookshelf» {
  roots := #[
    `Bookshelf,
    `FirstCourseAbstractAlgebra,
    `MathematicalIntroductionLogic,
    `MockMockingbird,
    `OneVariableCalculus,
    `TheoremProvingInLean
  ]
}
