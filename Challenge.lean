/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# The Graham–Pollak theorem

A *biclique decomposition* of the complete graph on a finite type `V` by `m` bicliques is given by
pairs `(A i, B i)` of disjoint vertex sets, `i : Fin m`, such that every pair of distinct vertices
`u ≠ v` is joined by exactly one of the complete bipartite graphs `A i × B i`
(`GrahamPollakTheorem.IsBicliqueDecomposition`).

* `GrahamPollakTheorem.graham_pollak`: **Graham–Pollak (1971).** Every biclique decomposition of
  `K_n`
  uses at least `n − 1` bicliques.
* `GrahamPollakTheorem.exists_bicliqueDecomposition`: the bound is attained: for `n ≥ 1`, `K_n` has
  a
  decomposition into `n − 1` stars.

The Mathlib definitions used in these statements are reproduced verbatim, with file and line at the
pinned Mathlib revision, in `MATHLIB_DEFINITIONS.md` at the root of this repository.
-/

@[expose] public section

namespace GrahamPollakTheorem

variable {V : Type*}

/-- The pairs `(A i, B i)`, `i : Fin m`, of disjoint vertex sets decompose the edges of the complete
graph on `V`: each pair `u ≠ v` lies in exactly one complete bipartite graph `A i × B i`. -/
def IsBicliqueDecomposition [DecidableEq V] {m : ℕ} (A B : Fin m → Finset V) : Prop :=
  (∀ i, Disjoint (A i) (B i)) ∧
    ∀ u v : V, u ≠ v →
      (Finset.univ.filter (fun i => (u ∈ A i ∧ v ∈ B i) ∨ (v ∈ A i ∧ u ∈ B i))).card = 1

/-- **Graham–Pollak (1971).** The complete graph on `n` vertices cannot be decomposed into fewer
than `n − 1` complete bipartite graphs. -/
theorem graham_pollak [Fintype V] [DecidableEq V] {m : ℕ} (A B : Fin m → Finset V)
    (h : IsBicliqueDecomposition A B) : Fintype.card V - 1 ≤ m := by
  sorry

/-- The Graham–Pollak bound is attained: `K_n` (`n ≥ 1`) is the union of `n − 1` stars. -/
theorem exists_bicliqueDecomposition (n : ℕ) (hn : 1 ≤ n) :
    ∃ A B : Fin (n - 1) → Finset (Fin n), IsBicliqueDecomposition A B := by
  sorry

end GrahamPollakTheorem
