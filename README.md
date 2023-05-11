# bookshelf

A study of the books listed below. Most proofs are conducted in LaTeX. Where
feasible, theorems are also formally proven in [Lean](https://leanprover.github.io/).

- [ ] Apostol, Tom M. Calculus, Vol. 1: One-Variable Calculus, with an Introduction to Linear Algebra. 2nd ed. Vol. 1. 2 vols. Wiley, 1991.
- [x] Avigad, Jeremy. ‘Theorem Proving in Lean’, n.d.
- [ ] Axler, Sheldon. Linear Algebra Done Right. Undergraduate Texts in Mathematics. Cham: Springer International Publishing, 2015.
- [ ] Cormen, Thomas H., Charles E. Leiserson, Ronald L. Rivest, and Clifford Stein. Introduction to Algorithms. 3rd ed. Cambridge, Mass: MIT Press, 2009.
- [ ] Enderton, Herbert B. A Mathematical Introduction to Logic. 2nd ed. San Diego: Harcourt/Academic Press, 2001.
- [ ] Gries, David. The Science of Programming. Texts and Monographs in Computer Science. New York: Springer-Verlag, 1981.
- [ ] Gustedt, Jens. Modern C. Shelter Island, NY: Manning Publications Co, 2020.
- [ ] Ross, Sheldon. A First Course in Probability Theory. 8th ed. Pearson Prentice Hall, n.d.
- [ ] Smullyan, Raymond M. To Mock a Mockingbird: And Other Logic Puzzles Including an Amazing Adventure in Combinatory Logic. Oxford: Oxford university press, 2000.

## Documentation

To generate documentation, we use [bookshelf-docgen](https://github.com/jrpotter/bookshelf-docgen).
Refer to this project on prerequisites and then run the following to build and
serve files locally:

```bash
> lake build Bookshelf:docs
> lake run server
```

This assumes you have `python3` available in your `$PATH`. To change how the
server behaves, refer to the `.env` file located in the root directory of this
project.

A color/symbol code is used on generated PDF headers to indicate their status:

* Teal coloring indicates the corresponding proof is complete. That is, the
  proof has been written in TeX and also formally verified in Lean.
* Magenta coloring indicates the corresponding proof is in progress. That is, a
  proof in both TeX and Lean have not yet been finished, but is actively being
  worked on.
* Red coloring indicates the formal Lean proof has not yet been started. It may
  or may not also indicate the TeX proof has been written.
