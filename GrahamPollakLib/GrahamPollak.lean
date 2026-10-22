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
(`GrahamPollak.IsBicliqueDecomposition`).

* `GrahamPollak.graham_pollak`: **Graham–Pollak (1971).** Every biclique decomposition of `K_n`
  uses at least `n − 1` bicliques.
* `GrahamPollak.exists_bicliqueDecomposition`: the bound is attained: for `n ≥ 1`, `K_n` has a
  decomposition into `n − 1` stars.
-/

@[expose] public section

namespace GrahamPollak

variable {V : Type*}

/-- The pairs `(A i, B i)`, `i : Fin m`, of disjoint vertex sets decompose the edges of the complete
graph on `V`: each pair `u ≠ v` lies in exactly one complete bipartite graph `A i × B i`. -/
def IsBicliqueDecomposition [DecidableEq V] {m : ℕ} (A B : Fin m → Finset V) : Prop :=
  (∀ i, Disjoint (A i) (B i)) ∧
    ∀ u v : V, u ≠ v →
      (Finset.univ.filter (fun i => (u ∈ A i ∧ v ∈ B i) ∨ (v ∈ A i ∧ u ∈ B i))).card = 1

section Aux

variable [DecidableEq V]

theorem pair_count_add {m : ℕ} {A B : Fin m → Finset V}
    (h : IsBicliqueDecomposition A B) (u v : V) :
    (∑ i, ((if u ∈ A i ∧ v ∈ B i then 1 else 0 : ℝ))) +
      (∑ i, ((if v ∈ A i ∧ u ∈ B i then 1 else 0 : ℝ))) = if u = v then 0 else 1 := by
  rw [← Finset.sum_add_distrib]
  split_ifs with huv
  · subst huv
    refine Finset.sum_eq_zero fun i _ => ?_
    have hd := Finset.disjoint_left.mp (h.1 i)
    by_cases hu : u ∈ A i
    · simp [hu, hd hu]
    · simp [hu]
  · have h1 := h.2 u v huv
    rw [Finset.card_eq_sum_ones, Finset.sum_filter] at h1
    have h2 : ((∑ i, ((if (u ∈ A i ∧ v ∈ B i) ∨ (v ∈ A i ∧ u ∈ B i) then 1 else 0 : ℕ)) : ℕ)
        : ℝ) = 1 := by
      rw [h1]; simp
    rw [Nat.cast_sum] at h2
    refine (Finset.sum_congr rfl fun i _ => ?_).trans h2
    have hd := Finset.disjoint_left.mp (h.1 i)
    by_cases h3 : u ∈ A i ∧ v ∈ B i
    · have h4 : ¬ (v ∈ A i ∧ u ∈ B i) := fun h4 => hd h4.1 h3.2
      simp [h3, h4]
    · by_cases h4 : v ∈ A i ∧ u ∈ B i
      · simp [h3, h4]
      · simp [h3, h4]

theorem sum_prod_eq [Fintype V] {m : ℕ} (A B : Fin m → Finset V) (x : V → ℝ) :
    ∑ i, (∑ u ∈ A i, x u) * (∑ v ∈ B i, x v) =
      ∑ u, ∑ v, x u * x v * ∑ i, ((if u ∈ A i ∧ v ∈ B i then 1 else 0 : ℝ)) := by
  have hA : ∀ (S : Finset V), ∑ u ∈ S, x u = ∑ u, if u ∈ S then x u else 0 := fun S => by
    rw [← Finset.sum_filter]; congr 1; ext; simp
  simp only [hA]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp_all

theorem sq_sum_eq [Fintype V] {m : ℕ} {A B : Fin m → Finset V}
    (h : IsBicliqueDecomposition A B) (x : V → ℝ) :
    (∑ v, x v) ^ 2 = ∑ v, x v ^ 2 + 2 * ∑ i, (∑ u ∈ A i, x u) * (∑ v ∈ B i, x v) := by
  set e : V → V → ℝ := fun u v => ∑ i, ((if u ∈ A i ∧ v ∈ B i then 1 else 0 : ℝ)) with he
  have hS := sum_prod_eq A B x
  have hS' : ∑ i, (∑ u ∈ A i, x u) * (∑ v ∈ B i, x v) = ∑ u, ∑ v, x u * x v * e v u := by
    rw [hS, Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    simp only [he]; ring
  have h2 : 2 * ∑ i, (∑ u ∈ A i, x u) * (∑ v ∈ B i, x v) =
      ∑ u, ∑ v, x u * x v * (if u = v then 0 else 1) := by
    rw [two_mul]
    nth_rewrite 1 [hS]
    rw [hS', ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← pair_count_add h u v]; ring
  have h3 : ∑ v, x v ^ 2 = ∑ u, ∑ v, x u * x v * (if u = v then 1 else 0) := by
    refine Finset.sum_congr rfl fun u _ => ?_
    simp [sq]
  rw [h2, h3, ← Finset.sum_add_distrib, sq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  split_ifs <;> ring

end Aux

/-- **Graham–Pollak (1971).** The complete graph on `n` vertices cannot be decomposed into fewer
than `n − 1` complete bipartite graphs. -/
theorem graham_pollak [Fintype V] [DecidableEq V] {m : ℕ} (A B : Fin m → Finset V)
    (h : IsBicliqueDecomposition A B) : Fintype.card V - 1 ≤ m := by
  by_contra hlt
  rw [not_le] at hlt
  let S : Fin (m + 1) → Finset V := Fin.cons Finset.univ A
  let L : (V → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ) :=
    LinearMap.pi fun j => ∑ v ∈ S j, LinearMap.proj v
  have hL : ∀ x j, L x j = ∑ v ∈ S j, x v := by
    intro x j; simp [L]
  have hker : LinearMap.ker L ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  rw [LinearMap.mem_ker] at hx
  have hsum : ∑ v, x v = 0 := by
    have := congrFun hx 0
    rw [hL] at this
    simpa [S] using this
  have hA : ∀ i, ∑ v ∈ A i, x v = 0 := by
    intro i
    have := congrFun hx i.succ
    rw [hL] at this
    simpa [S] using this
  have hsq := sq_sum_eq h x
  simp only [hA, zero_mul, Finset.sum_const_zero, mul_zero, add_zero, hsum] at hsq
  have h0 : ∑ v, x v ^ 2 = 0 := by simpa using hsq.symm
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => sq_nonneg (x v))).mp h0
  apply hx0
  funext v
  simpa using hall v (Finset.mem_univ v)

/-- The Graham–Pollak bound is attained: `K_n` (`n ≥ 1`) is the union of `n − 1` stars. -/
theorem exists_bicliqueDecomposition (n : ℕ) (hn : 1 ≤ n) :
    ∃ A B : Fin (n - 1) → Finset (Fin n), IsBicliqueDecomposition A B := by
  refine ⟨fun i => {⟨i.val, by omega⟩},
    fun i => Finset.univ.filter (fun v : Fin n => i.val < v.val), ?_, ?_⟩
  · intro i
    simp
  · intro u v huv
    have huv' : u.val ≠ v.val := fun h => huv (Fin.ext h)
    rw [Finset.card_eq_one]
    refine ⟨⟨min u.val v.val, by omega⟩, ?_⟩
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      Fin.ext_iff]
    omega

end GrahamPollak
