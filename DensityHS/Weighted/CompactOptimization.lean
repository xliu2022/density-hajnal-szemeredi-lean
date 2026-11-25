module

public import DensityHS.Weighted.Optimization

/-!+# Compact selection at a fixed cover-cost budget

Author and maintainer: Xizhi Liu.

All finite support graphs are considered, together with closed probability
weights and bounded covers. The range of edge densities is a finite union of
compact images, so a global maximum exists.
-/

@[expose] public section

namespace DensityHS

open Set Finset

variable {V : Type*} [Fintype V]

def feasiblePairs (r : ℕ) (G : SimpleGraph V) (x : ℝ) :
    Set ((V → ℝ) × (V → ℝ)) :=
  {w | IsProbabilityWeight w.1 ∧ w.2 ∈ coverCube r G ∧ coverCost w.1 w.2 ≤ x}

theorem continuous_coverCost_pair :
    Continuous (fun w : (V → ℝ) × (V → ℝ) => coverCost w.1 w.2) := by
  unfold coverCost
  fun_prop

theorem continuous_edgeMass (G : SimpleGraph V) : Continuous (edgeMass G) := by
  classical
  unfold edgeMass
  apply Continuous.div_const
  apply continuous_finset_sum
  intro u _
  apply continuous_finset_sum
  intro v _
  split_ifs <;> fun_prop

theorem isCompact_feasiblePairs (r : ℕ) (G : SimpleGraph V) (x : ℝ) :
    IsCompact (feasiblePairs r G x) := by
  have heq : feasiblePairs r G x =
      (stdSimplex ℝ V ×ˢ coverCube r G) ∩
        {w : (V → ℝ) × (V → ℝ) | coverCost w.1 w.2 ≤ x} := by
    ext w
    simp only [feasiblePairs, IsProbabilityWeight, stdSimplex, Set.mem_ofPred_eq,
      Set.mem_inter_iff, Set.mem_prod]
    tauto
  rw [heq]
  exact ((isCompact_stdSimplex ℝ V).prod (isCompact_coverCube r G)).inter_right
    (isClosed_le continuous_coverCost_pair continuous_const)

/-- Every feasible edge density on this fixed vertex type. -/
noncomputable def feasibleDensities (r : ℕ) (x : ℝ) : Set ℝ :=
  ⋃ G : SimpleGraph V, (fun w : (V → ℝ) × (V → ℝ) => edgeMass G w.1) ''
    feasiblePairs r G x

theorem isCompact_feasibleDensities (r : ℕ) (x : ℝ) :
    IsCompact (feasibleDensities (V := V) r x) := by
  classical
  apply isCompact_iUnion
  intro G
  exact (isCompact_feasiblePairs r G x).image ((continuous_edgeMass G).comp continuous_fst)

theorem mem_feasibleDensities {r : ℕ} {x : ℝ} {G : SimpleGraph V}
    {p c : V → ℝ} (hp : IsProbabilityWeight p) (hc : IsCliqueCover r G c)
    (hcost : coverCost p c ≤ x) : edgeMass G p ∈ feasibleDensities (V := V) r x := by
  apply Set.mem_iUnion.mpr
  refine ⟨G, (p, fun v => min (c v) 1), ?_, rfl⟩
  exact ⟨hp, truncated_cover_mem_cube hc, (coverCost_truncate_le hp.1).trans hcost⟩

/-- The optimization is over both graph and weights; the cover is a witness
that the fixed budget is feasible. -/
def IsGlobalWeightMaximum (r : ℕ) (x : ℝ) (G : SimpleGraph V) (p : V → ℝ) : Prop :=
  ∀ (H : SimpleGraph V) (q d : V → ℝ), IsProbabilityWeight q →
    IsCliqueCover r H d → coverCost q d ≤ x → edgeMass H q ≤ edgeMass G p

/-- Existence of the finite global maximum used before selecting positive
support. No positivity or nonzero-support assumption is hidden in compactness. -/
theorem exists_global_weightMaximum {r : ℕ} {x : ℝ} {G : SimpleGraph V}
    {p c : V → ℝ} (hp : IsProbabilityWeight p) (hc : IsCliqueCover r G c)
    (hcost : coverCost p c ≤ x) :
    ∃ (H : SimpleGraph V) (q d : V → ℝ), IsProbabilityWeight q ∧
      d ∈ coverCube r H ∧ coverCost q d ≤ x ∧
      IsGlobalWeightMaximum r x H q := by
  have hnonempty : (feasibleDensities (V := V) r x).Nonempty :=
    ⟨edgeMass G p, mem_feasibleDensities hp hc hcost⟩
  obtain ⟨e, he, hmax⟩ := (isCompact_feasibleDensities (V := V) r x).exists_isGreatest hnonempty
  obtain ⟨H, w, hw, hwe⟩ := Set.mem_iUnion.mp he
  refine ⟨H, w.1, w.2, hw.1, hw.2.1, hw.2.2, ?_⟩
  intro J q d hq hd hqd
  change edgeMass H w.1 = e at hwe
  rw [hwe]
  exact hmax (mem_feasibleDensities hq hd hqd)

theorem IsGlobalWeightMaximum.to_weightMaximum {r : ℕ} {x : ℝ}
    {G : SimpleGraph V} {p c : V → ℝ}
    (hmax : IsGlobalWeightMaximum r x G p) (hc : IsCliqueCover r G c) :
    IsWeightMaximum G c x p := fun q hq hqc => hmax G q c hq hc hqc

/-- A boundary estimate from the induction on the number of atoms gives
minimal positive support for a strict counterexample. -/
theorem minimalPositiveSupport_of_boundary_bound {r : ℕ} {x bound : ℝ}
    {G : SimpleGraph V} {p c : V → ℝ} (hc : IsCliqueCover r G c)
    (hstrict : bound < edgeMass G p)
    (hboundary : ∀ (H : SimpleGraph V) (q d : V → ℝ),
      IsProbabilityWeight q → IsCliqueCover r H d → coverCost q d ≤ x →
      (∃ v, q v = 0) → edgeMass H q ≤ bound) :
    HasMinimalPositiveSupport G c x p := by
  intro q hq hcost hedge v
  by_contra hn
  have hv : q v = 0 := le_antisymm (le_of_not_gt hn) (hq.1 v)
  have hbound := hboundary G q c hq hc hcost ⟨v, hv⟩
  linarith

end DensityHS
