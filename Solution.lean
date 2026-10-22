/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import GrahamPollakLib.GrahamPollak

/-!
# Proofs of the statements in `Challenge.lean`

The theorems are proved in `GrahamPollakLib/` (namespace `GrahamPollak`), with the definition
stated identically there. `graham_pollak` follows Tverberg: if `m + 1 < n`, the `m + 1` linear
forms `x ↦ ∑ v, x v` and `x ↦ ∑ v ∈ A i, x v` have a common nonzero zero `x`; the identity
`(∑ x)² = ∑ x² + 2 ∑ᵢ x(Aᵢ) x(Bᵢ)` then forces `x = 0`. `exists_bicliqueDecomposition` uses the
`n − 1` stars `({i}, {v | i < v})`.
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
    (h : IsBicliqueDecomposition A B) : Fintype.card V - 1 ≤ m :=
  GrahamPollak.graham_pollak A B h

/-- The Graham–Pollak bound is attained: `K_n` (`n ≥ 1`) is the union of `n − 1` stars. -/
theorem exists_bicliqueDecomposition (n : ℕ) (hn : 1 ≤ n) :
    ∃ A B : Fin (n - 1) → Finset (Fin n), IsBicliqueDecomposition A B :=
  GrahamPollak.exists_bicliqueDecomposition n hn

end GrahamPollakTheorem
