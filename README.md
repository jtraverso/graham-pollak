# The Graham–Pollak theorem in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

A *biclique decomposition* of the complete graph on a finite type `V` by `m` bicliques is a family
of pairs `(A i, B i)`, `i : Fin m`, of disjoint vertex sets such that every pair of distinct
vertices `u ≠ v` lies in exactly one complete bipartite graph `A i × B i`
(`GrahamPollakTheorem.IsBicliqueDecomposition`). All statements are in the namespace
`GrahamPollakTheorem`:

1. `graham_pollak`, **the Graham–Pollak theorem (1971).** Every biclique decomposition of `K_n`
   uses at least `n − 1` bicliques.
2. `exists_bicliqueDecomposition`: the bound is attained; for `n ≥ 1`, `K_n` is the union of
   `n − 1` stars.

The definition is stated in `Challenge.lean`; `comparator.json` selects only the theorems, and the
definition enters the check only as part of the theorem statements that use it. Mathlib does not
contain this theorem.

## Files

- [`Challenge.lean`](Challenge.lean): the definition and the audited statements. It imports only
  Mathlib.
- [`Solution.lean`](Solution.lean) and [`GrahamPollakLib/`](GrahamPollakLib): the proofs.
- [`comparator.json`](comparator.json): the theorems that are compared.
- [`MATHLIB_DEFINITIONS.md`](MATHLIB_DEFINITIONS.md): verbatim copies of the Mathlib definitions
  used.
- [`formalization.yaml`](formalization.yaml): provenance, sources and process.

## How the proofs go

* **Lower bound** (Tverberg's proof). If `m + 1 < n`, the `m + 1` linear forms `x ↦ ∑ v, x v` and
  `x ↦ x(A i) = ∑ v ∈ A i, x v` on `V → ℝ` have a common nonzero zero `x`. Since every pair
  `u ≠ v` is covered exactly once, `(∑ v, x v)² = ∑ v, x v² + 2 ∑ i, x(A i) x(B i)`, so
  `∑ v, x v² = 0` and `x = 0`, a contradiction.
* **Sharpness.** For `i < n − 1` take `A i = {i}` and `B i = {v | i < v}`; the pair `u ≠ v` is
  covered only by the index `min u v`.

## Sources

* R. L. Graham, H. O. Pollak, *On the addressing problem for loop switching*, Bell System Tech. J.
  50 (1971) 2495–2519, doi:10.1002/j.1538-7305.1971.tb02618.x.
* H. Tverberg, *On the decomposition of K_n into complete bipartite graphs*, J. Graph Theory 6
  (1982) 493–494, doi:10.1002/jgt.3190060414.

## Authorship and use of AI

The author chose the result. The statements and proof plan were written with Claude in Claude Code
and checked on the smallest cases. The proofs were produced by Harmonic's Aristotle in one run, then
audited and rebuilt locally. Lean checks everything mechanically. See `formalization.yaml`.

## Building

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```bash
lake exe cache get
lake build
```
