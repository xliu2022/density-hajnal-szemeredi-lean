module

public import DensityHS.Basic.WeightedGraph
public import Mathlib.Analysis.Convex.KreinMilman

/-!
# Extreme optimal fractional clique covers

Author and maintainer: Xizhi Liu.
This establishes actual optimal-cover existence and an extreme optimal point of the
unbounded covering polyhedron, not an assumed linear-programming interface.
-/

@[expose] public section

namespace DensityHS

open Finset Set

variable {V : Type*} [Fintype V]

/-- Cover cost as a continuous linear functional. -/
noncomputable def coverCostCLM (p : V → ℝ) : (V → ℝ) →L[ℝ] ℝ :=
  ∑ v, (p v) • ContinuousLinearMap.proj v

@[simp] theorem coverCostCLM_apply (p c : V → ℝ) :
    coverCostCLM p c = coverCost p c := by
  simp [coverCostCLM, coverCost]

theorem IsOptimalCover.le_one {r : ℕ} {G : SimpleGraph V} {p c : V → ℝ}
    (hp : ∀ v, 0 < p v) (hc : IsOptimalCover r G p c) : ∀ v, c v ≤ 1 := by
  intro v
  by_contra h
  have hv : 1 < c v := lt_of_not_ge h
  have hlt : coverCost p (fun w => min (c w) 1) < coverCost p c := by
    apply Finset.sum_lt_sum
    · intro w _
      exact mul_le_mul_of_nonneg_left (min_le_left _ _) (le_of_lt (hp w))
    · refine ⟨v, mem_univ _, ?_⟩
      change p v * min (c v) 1 < p v * c v
      rw [min_eq_right (le_of_lt hv)]
      exact mul_lt_mul_of_pos_left hv (hp v)
  exact (not_lt_of_ge (hc.2 _ hc.1.truncate)) hlt

theorem isExposed_optimalCovers (r : ℕ) (G : SimpleGraph V) (p : V → ℝ) :
    IsExposed ℝ {c | IsCliqueCover r G c} {c | IsOptimalCover r G p c} := by
  intro _
  refine ⟨-coverCostCLM p, ?_⟩
  ext c
  simp [IsOptimalCover]

theorem isCompact_optimalCovers (r : ℕ) (G : SimpleGraph V) (hr : 0 < r)
    (p : V → ℝ) (hp : ∀ v, 0 < p v) :
    IsCompact {c | IsOptimalCover r G p c} := by
  obtain ⟨c₀, hc₀, _⟩ := exists_optimal_cover r G hr p (fun v => le_of_lt (hp v))
  have heq : {c | IsOptimalCover r G p c} =
      coverCube r G ∩ {c | coverCost p c = coverCost p c₀} := by
    ext c
    constructor
    · intro hc
      exact ⟨⟨hc.1, hc.le_one hp⟩, le_antisymm (hc.2 _ hc₀.1) (hc₀.2 _ hc.1)⟩
    · rintro ⟨hc, he⟩
      exact ⟨hc.1, fun d hd => he ▸ hc₀.2 d hd⟩
  rw [heq]
  exact (isCompact_coverCube r G).inter_right
    (isClosed_eq (continuous_coverCost p) continuous_const)

theorem exists_extreme_optimal_cover (r : ℕ) (G : SimpleGraph V) (hr : 0 < r)
    (p : V → ℝ) (hp : ∀ v, 0 < p v) :
    ∃ c, IsOptimalCover r G p c ∧
      c ∈ ({d | IsCliqueCover r G d} : Set (V → ℝ)).extremePoints ℝ := by
  have hn : ({c | IsOptimalCover r G p c} : Set (V → ℝ)).Nonempty := by
    obtain ⟨c, hc, _⟩ := exists_optimal_cover r G hr p (fun v => le_of_lt (hp v))
    exact ⟨c, hc⟩
  obtain ⟨c, hc⟩ := (isCompact_optimalCovers r G hr p hp).extremePoints_nonempty hn
  exact ⟨c, hc.1,
    (isExposed_optimalCovers r G p).isExtreme.extremePoints_subset_extremePoints hc⟩

end DensityHS
