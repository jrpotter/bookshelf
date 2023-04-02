# bookshelf-lean

A collection of proofs and answers to exercises to books I'm studying.

## Updates

Lean's tooling is a fickle beast. If looking to update e.g. `Mathlib`, pin a new
version to the `lake-manifest.json` file and start a new build from scratch:

```bash
> lake update
> lake clean
> lake build
```
