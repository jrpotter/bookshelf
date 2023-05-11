import DocGen4.Output.Template
import DocGen4.Output.DocString
import DocGen4.Process

namespace DocGen4
namespace Output

open scoped DocGen4.Jsx
open Lean Widget

/-- This is basically an arbitrary number that seems to work okay. -/
def equationLimit : Nat := 200

def equationToHtml (c : CodeWithInfos) : HtmlM Html := do
  return <li class="equation">[← infoFormatToHtml c]</li>

/--
Attempt to render all `simp` equations for this definition. At a size
defined in `equationLimit` we stop trying since they:
- are too ugly to read most of the time
- take too long
-/
def equationsToHtml (i : Process.DefinitionInfo) : HtmlM (Array Html) := do
  if let some eqs := i.equations then
    let equationsHtml ← eqs.mapM equationToHtml
    let filteredEquationsHtml := equationsHtml.filter (·.textLength < equationLimit)
    if equationsHtml.size ≠ filteredEquationsHtml.size then
      return #[
        <details>
          <summary>Equations</summary>
          <ul class="equations">
            <li class="equation">One or more equations did not get rendered due to their size.</li>
            [filteredEquationsHtml]
          </ul>
        </details>
      ]
    else
      return #[
        <details>
          <summary>Equations</summary>
          <ul class="equations">
            [filteredEquationsHtml]
          </ul>
        </details>
      ]
  else
    return #[]

end Output
end DocGen4

