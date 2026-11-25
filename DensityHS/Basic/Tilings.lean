module

public import DensityHS.Basic.WeightedGraph

/-!
# Finite fractional clique tilings and weak duality

Author and maintainer: Xizhi Liu.
Tiling size counts copies, not covered vertex mass. The factor `r` in the total
load identity records this normalization explicitly.
-/

@[expose] public section

namespace DensityHS

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The finite family of unordered `r`-cliques. -/
noncomputable def cliqueFamily (r : ℕ) (G : SimpleGraph V) : Finset (Finset V) := by
  classical
  exact G.cliqueFinset r

@[simp] theorem mem_cliqueFamily {r : ℕ} {G : SimpleGraph V} {K : Finset V} :
    K ∈ cliqueFamily r G ↔ G.IsNClique r K := by
  classical
  exact G.mem_cliqueFinset_iff

/-- The total number (mass) of fractional clique copies. -/
noncomputable def tilingSize (r : ℕ) (G : SimpleGraph V) (t : Finset V → ℝ) : ℝ :=
  ∑ K ∈ cliqueFamily r G, t K

/-- The load of fractional clique copies on one vertex. -/
noncomputable def tilingLoad (r : ℕ) (G : SimpleGraph V)
    (t : Finset V → ℝ) (v : V) : ℝ :=
  ∑ K ∈ cliqueFamily r G, if v ∈ K then t K else 0

/-- Nonnegative clique amounts with prescribed vertex capacities. -/
def IsFractionalTiling (r : ℕ) (G : SimpleGraph V)
    (p : V → ℝ) (t : Finset V → ℝ) : Prop :=
  (∀ K ∈ cliqueFamily r G, 0 ≤ t K) ∧ ∀ v, tilingLoad r G t v ≤ p v

theorem tilingSize_nonneg {r : ℕ} {G : SimpleGraph V}
    {p : V → ℝ} {t : Finset V → ℝ} (ht : IsFractionalTiling r G p t) :
    0 ≤ tilingSize r G t :=
  Finset.sum_nonneg ht.1

/-- Reindexing the incidence matrix: weighted vertex loads equal weighted clique loads. -/
theorem coverCost_tilingLoad (r : ℕ) (G : SimpleGraph V)
    (c : V → ℝ) (t : Finset V → ℝ) :
    (∑ v, c v * tilingLoad r G t v) =
      ∑ K ∈ cliqueFamily r G, t K * (∑ v ∈ K, c v) := by
  classical
  simp only [tilingLoad, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro K _
  calc
    (∑ v, c v * (if v ∈ K then t K else 0)) =
        ∑ v, if v ∈ K then c v * t K else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      split_ifs <;> simp
    _ = ∑ v ∈ K, c v * t K := by simp
    _ = ∑ v ∈ K, t K * c v := by
      apply Finset.sum_congr rfl
      intro v _
      ring

/-- Every feasible tiling has size at most the cost of every feasible cover. -/
theorem fractional_weak_duality {r : ℕ} {G : SimpleGraph V}
    {p c : V → ℝ} {t : Finset V → ℝ}
    (ht : IsFractionalTiling r G p t) (hc : IsCliqueCover r G c) :
    tilingSize r G t ≤ coverCost p c := by
  calc
    tilingSize r G t ≤ ∑ K ∈ cliqueFamily r G, t K * (∑ v ∈ K, c v) := by
      apply Finset.sum_le_sum
      intro K hK
      exact le_mul_of_one_le_right (ht.1 K hK) (hc.2 K (mem_cliqueFamily.mp hK))
    _ = ∑ v, c v * tilingLoad r G t v := (coverCost_tilingLoad r G c t).symm
    _ ≤ ∑ v, c v * p v := by
      apply Finset.sum_le_sum
      intro v _
      exact mul_le_mul_of_nonneg_left (ht.2 v) (hc.1 v)
    _ = coverCost p c := by simp [coverCost, mul_comm]

/-- The sum of all vertex loads is `r` times the number of clique copies. -/
theorem sum_tilingLoad (r : ℕ) (G : SimpleGraph V) (t : Finset V → ℝ) :
    (∑ v, tilingLoad r G t v) = (r : ℝ) * tilingSize r G t := by
  have h := coverCost_tilingLoad r G (fun _ => 1) t
  simp only [one_mul, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  rw [h]
  unfold tilingSize
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro K hK
  rw [(mem_cliqueFamily.mp hK).card_eq]
  ring

theorem tilingSize_le_inv {r : ℕ} {G : SimpleGraph V}
    {p : V → ℝ} {t : Finset V → ℝ} (hr : 0 < r)
    (hp : IsProbabilityWeight p) (ht : IsFractionalTiling r G p t) :
    tilingSize r G t ≤ 1 / (r : ℝ) := by
  have h := fractional_weak_duality ht (constant_clique_cover r G hr)
  simpa [coverCost_const, hp.2] using h

/-- An integral clique packing is a finite family of pairwise vertex-disjoint cliques. -/
def IsCliquePacking (r : ℕ) (G : SimpleGraph V) (P : Finset (Finset V)) : Prop :=
  (∀ K ∈ P, G.IsNClique r K) ∧ (P : Set (Finset V)).PairwiseDisjoint id

/-- The ordinary, integral packing restriction in Theorem 1.1. -/
def HasPackingNumberAtMost (r : ℕ) (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ P : Finset (Finset V), IsCliquePacking r G P → P.card ≤ k

end DensityHS
