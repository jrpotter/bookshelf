/-
Copyright (c) 2021 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import DocGen4.Output.ToHtmlFormat
import DocGen4.Output.Template

namespace DocGen4
namespace Output

open scoped DocGen4.Jsx

def index : BaseHtmlM Html := do templateExtends (baseHtml "Index") <|
  pure <|
    <main>
      <a id="top"></a>
      <h1>Bookshelf</h1>
      <p>
        A study of the books listed below. Most proofs are conducted in LaTeX.
        Where feasible, theorems are also formally proven in
        <a target="_blank" href="https://leanprover.github.io/">Lean</a>.
      </p>
      <ul>
        <li>Apostol, Tom M. Calculus, Vol. 1: One-Variable Calculus, with an Introduction to Linear Algebra. 2nd ed. Vol. 1. 2 vols. Wiley, 1991.</li>
        <li>Avigad, Jeremy. ‘Theorem Proving in Lean’, n.d.</li>
        <li>Axler, Sheldon. Linear Algebra Done Right. Undergraduate Texts in Mathematics. Cham: Springer International Publishing, 2015.</li>
        <li>Cormen, Thomas H., Charles E. Leiserson, Ronald L. Rivest, and Clifford Stein. Introduction to Algorithms. 3rd ed. Cambridge, Mass: MIT Press, 2009.</li>
        <li>Enderton, Herbert B. A Mathematical Introduction to Logic. 2nd ed. San Diego: Harcourt/Academic Press, 2001.</li>
        <li>Enderton, Herbert B. Elements of Set Theory. New York: Academic Press, 1977.</li>
        <li>Gries, David. The Science of Programming. Texts and Monographs in Computer Science. New York: Springer-Verlag, 1981.</li>
        <li>Gustedt, Jens. Modern C. Shelter Island, NY: Manning Publications Co, 2020.</li>
        <li>Ross, Sheldon. A First Course in Probability Theory. 8th ed. Pearson Prentice Hall, n.d.</li>
        <li>Smullyan, Raymond M. To Mock a Mockingbird: And Other Logic Puzzles Including an Amazing Adventure in Combinatory Logic. Oxford: Oxford university press, 2000.</li>
      </ul>
      <p>
        A color/symbol code is used on generated PDF headers to indicate their
        status:
        <ul>
          <li>
            <span style="color:darkgray">Dark gray statements </span> are
            reserved for definitions and axioms that have been encoded in LaTeX.
            A corresponding reference to a definition/axiom in Lean may also be
            provided.
          </li>
          <li>
            <span style="color:teal">Teal statements </span> are reserved for
            statements, theorems, lemmas, etc. that have been proven in both
            LaTeX and Lean.
          </li>
          <li>
            <span style="color:olive">Olive statements </span> are reserved for
            statements, theorems, lemmas, etc. that have been proven in LaTeX
            and will <i>not </i> be proven in Lean.
          </li>
          <li>
            <span style="color:fuchsia">Fuchsia statements </span> are reserved
            for definitions, axioms, statements, theorems, lemmas, etc. that
            have been proven or encoded in LaTeX and <i>will </i> be encoded in
            Lean.
          </li>
          <li>
            <span style="color:maroon">Maroon </span> serves as a catch-all for
            all statements that don't fit the above categorizations. Incomplete
            definitions, statements without proof, etc. belong here.
          </li>
        </ul>
      </p>
      <p>This was built using Lean 4 at commit <a href={s!"https://github.com/leanprover/lean4/tree/{Lean.githash}"}>{Lean.githash}</a></p>
    </main>

end Output
end DocGen4
