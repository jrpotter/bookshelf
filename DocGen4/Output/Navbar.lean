/-
Copyright (c) 2021 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Lean
import DocGen4.Output.ToHtmlFormat
import DocGen4.Output.Base

namespace DocGen4
namespace Output

open Lean
open scoped DocGen4.Jsx

def moduleListFile (file : NameExt) : BaseHtmlM Html := do
  let contents :=
    if file.ext == .pdf then
      <span>{s!"🗎 {file.getString!} (<a class=\"pdf\" target=\"_blank\" href={← moduleNameExtToLink file}>pdf</a>)"}</span>
    else
      <a href={← moduleNameExtToLink file}>{file.getString!}</a>
  return <div class={if (← getCurrentName) == file.name then "nav_link visible" else "nav_link"}>
    {contents}
  </div>

/--
Build the HTML tree representing the module hierarchy.
-/
partial def moduleListDir (h : Hierarchy) : BaseHtmlM Html := do
  let children := Array.mk (h.getChildren.toList.map Prod.snd)
  let nodes ← children.mapM (fun c =>
    if c.getChildren.toList.length != 0 then
      moduleListDir c
    else if Hierarchy.isFile c && c.getChildren.toList.length = 0 then
      moduleListFile (Hierarchy.getNameExt c)
    else
      pure ""
  )
  let moduleLink ← moduleNameToHtmlLink h.getName
  let summary :=
    if h.isFile then
      <summary>{s!"{h.getName.getString!} ({<a href={← moduleNameToHtmlLink h.getName}>file</a>})"} </summary>
    else
      <summary>{h.getName.getString!}</summary>

  pure
    <details class="nav_sect" "data-path"={moduleLink} [if (← getCurrentName).any (h.getName.isPrefixOf ·) then #[("open", "")] else #[]]>
      {summary}
      [nodes]
    </details>

/--
Return a list of top level modules, linkified and rendered as HTML
-/
def moduleList : BaseHtmlM Html := do
  let hierarchy ← getHierarchy
  let mut list := Array.empty
  for (_, cs) in hierarchy.getChildren do
    list := list.push <| ← moduleListDir cs
  return <div class="module_list">[list]</div>

/--
The main entry point to rendering the navbar on the left hand side.
-/
def navbar : BaseHtmlM Html := do
  pure
    <html lang="en">
      <head>
        [← baseHtmlHeadDeclarations]

        <script type="module" src={s!"{← getRoot}nav.js"}></script>
        <script type="module" src={s!"{← getRoot}color-scheme.js"}></script>
        <base target="_parent" />
      </head>

      <body>
        <div class="navframe">
        <nav class="nav">
          <h3>General documentation</h3>
          <div class="nav_link"><a href={s!"{← getRoot}"}>index</a></div>
          <div class="nav_link"><a href={s!"{← getRoot}foundational_types.html"}>foundational types</a></div>
          /-
          TODO: Add these in later
          <div class="nav_link"><a href={s!"{← getRoot}tactics.html"}>tactics</a></div>
          <div class="nav_link"><a href={s!"{← getRoot}commands.html"}>commands</a></div>
          <div class="nav_link"><a href={s!"{← getRoot}hole_commands.html"}>hole commands</a></div>
          <div class="nav_link"><a href={s!"{← getRoot}attributes.html"}>attributes</a></div>
          <div class="nav_link"><a href={s!"{← getRoot}notes.html"}>notes</a></div>
          <div class="nav_link"><a href={s!"{← getRoot}references.html"}>references</a></div>
          -/
          <h3>Library</h3>
          {← moduleList}
          <div id="settings" hidden="hidden">
            -- `input` is a void tag, but can be self-closed to make parsing easier.
            <h3>Color scheme</h3>
            <form id="color-theme-switcher">
                <label for="color-theme-dark">
                    <input type="radio" name="color_theme" id="color-theme-dark" value="dark" autocomplete="off"/>dark</label>
                <label for="color-theme-system" title="Match system theme settings">
                    <input type="radio" name="color_theme" id="color-theme-system" value="system" autocomplete="off"/>system</label>
                <label for="color-theme-light">
                    <input type="radio" name="color_theme" id="color-theme-light" value="light" autocomplete="off"/>light</label>
            </form>
          </div>
        </nav>
        </div>
      </body>
    </html>

end Output
end DocGen4
