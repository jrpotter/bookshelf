# bookshelf

A study of the books listed below.

## Overview

Most proofs are conducted in LaTeX. Where feasible, theorems are also formally
proven in [Lean](https://leanprover.github.io/).

- [ ] Apostol, Tom M. Calculus, Vol. 1: One-Variable Calculus, with an Introduction to Linear Algebra. 2nd ed. Vol. 1. 2 vols. Wiley, 1991.
- [x] Avigad, Jeremy. ‘Theorem Proving in Lean’, n.d.
- [ ] Axler, Sheldon. Linear Algebra Done Right. Undergraduate Texts in Mathematics. Cham: Springer International Publishing, 2015.
- [ ] Cormen, Thomas H., Charles E. Leiserson, Ronald L. Rivest, and Clifford Stein. Introduction to Algorithms. 3rd ed. Cambridge, Mass: MIT Press, 2009.
- [ ] Enderton, Herbert B. A Mathematical Introduction to Logic. 2nd ed. San Diego: Harcourt/Academic Press, 2001.
- [ ] Enderton, Herbert B. Elements of Set Theory. New York: Academic Press, 1977.
- [ ] Gries, David. The Science of Programming. Texts and Monographs in Computer Science. New York: Springer-Verlag, 1981.
- [ ] Gustedt, Jens. Modern C. Shelter Island, NY: Manning Publications Co, 2020.
- [ ] Ross, Sheldon. A First Course in Probability Theory. 8th ed. Pearson Prentice Hall, n.d.
- [ ] Smullyan, Raymond M. To Mock a Mockingbird: And Other Logic Puzzles Including an Amazing Adventure in Combinatory Logic. Oxford: Oxford university press, 2000.

## Building

[direnv](https://direnv.net/) can be used to launch a dev shell upon entering
this directory (refer to `.envrc`). Otherwise run via:
```bash
$ nix develop
```
If you prefer not to use `nix`, you can also use the [elan](https://github.com/leanprover/elan)
package manager like normal. Afterward, build the project by running
```bash
$ lake build
```
Optionally build documentation by running:
```bash
$ lake build Bookshelf:docs
```
Afterward, you can view the generated files by running `python3 -m http.server`
from within the `.lake/build/doc` directory.
