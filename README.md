# bookshelf

A collection on the study of the books listed below. I aim to use [Lean](https://leanprover.github.io/)
when possible and fallback to LaTeX when not.

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

To generate Lean documentation, we use [bookshelf-docgen](https://github.com/jrpotter/bookshelf-docgen).
Refer to this project on prerequisites and then run the following to build and
serve files locally:

```bash
> lake build Bookshelf:docs
> lake run server
```

This assumes you have `python3` available in your `$PATH`. To change how the
server behaves, refer to the `.env` file located in the root directory of this
project.
