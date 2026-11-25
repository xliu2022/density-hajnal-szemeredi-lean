module

public import DensityHS.Weighted.Saturation
public import DensityHS.Weighted.CoverVertices
public import DensityHS.Basic.Envelope

/-!
# Reduction of a strict counterexample to an extreme positive-support maximum

Author and maintainer: Xizhi Liu.

The boundary premise is the induction hypothesis on the number of positive
atoms. Compactness, extreme optimal covers, and every optimization property
are supplied by proved theorems, rather than postulated as axioms.
-/

@[expose] public section

namespace DensityHS

open Set

variable {V : Type*} [Fintype V]

/-- The concrete extremal data selected inside a fixed finite vertex type. -/
structure ExtremalTriple (r : ℕ) (x : ℝ) (G : SimpleGraph V)
    (p c : V → ℝ) : Prop where
  probability : IsProbabilityWeight p
  positive : ∀ v, 0 < p v
  optimal : IsOptimalCover r G p c
  extreme : c ∈ ({d | IsCliqueCover r G d} : Set (V → ℝ)).extremePoints ℝ
  budget : coverCost p c ≤ x
  maximum : IsGlobalWeightMaximum r x G p
  minimal : HasMinimalPositiveSupport G c x p

/-- A strict counterexample whose boundary is already bounded produces all
the extremal data used in the support reduction. -/
theorem exists_extremalTriple {r : ℕ} (hr : 0 < r) {x bound : ℝ}
    {G : SimpleGraph V} {p c : V → ℝ}
    (hp : IsProbabilityWeight p) (hc : IsCliqueCover r G c)
    (hbudget : coverCost p c ≤ x) (hstrict : bound < edgeMass G p)
    (hboundary : ∀ (H : SimpleGraph V) (q d : V → ℝ),
      IsProbabilityWeight q → IsCliqueCover r H d → coverCost q d ≤ x →
      (∃ v, q v = 0) → edgeMass H q ≤ bound) :
    ∃ (H : SimpleGraph V) (q d : V → ℝ), ExtremalTriple r x H q d ∧
      edgeMass G p ≤ edgeMass H q ∧ bound < edgeMass H q := by
  obtain ⟨H, q, c₀, hq, hc₀, hqcost, hmax⟩ :=
    exists_global_weightMaximum hp hc hbudget
  have hedge : edgeMass G p ≤ edgeMass H q := hmax G p c hp hc hbudget
  have hstrictq : bound < edgeMass H q := hstrict.trans_le hedge
  have hpos : ∀ v, 0 < q v := by
    intro v
    by_contra hn
    have hv : q v = 0 := le_antisymm (le_of_not_gt hn) (hq.1 v)
    exact not_lt_of_ge (hboundary H q c₀ hq hc₀.1 hqcost ⟨v, hv⟩) hstrictq
  obtain ⟨d, hd, hext⟩ := exists_extreme_optimal_cover r H hr q hpos
  have hcostd : coverCost q d ≤ x := (hd.2 c₀ hc₀.1).trans hqcost
  have hmin := minimalPositiveSupport_of_boundary_bound hd.1 hstrictq hboundary
  exact ⟨H, q, d, ⟨hq, hpos, hd, hext, hcostd, hmax, hmin⟩, hedge, hstrictq⟩

theorem ExtremalTriple.weightMaximum {r : ℕ} {x : ℝ}
    {G : SimpleGraph V} {p c : V → ℝ} (h : ExtremalTriple r x G p c) :
    IsWeightMaximum G c x p := h.maximum.to_weightMaximum h.optimal.1

theorem ExtremalTriple.saturated {r : ℕ} (hr : 2 ≤ r) {x : ℝ}
    {G : SimpleGraph V} {p c : V → ℝ} (h : ExtremalTriple r x G p c) :
    Weighted.Support.EdgeSaturatedCover r G c :=
  globalWeightMaximum_edgeSaturatedCover hr h.probability h.positive h.optimal.1
    h.budget h.maximum

theorem ExtremalTriple.negative {r : ℕ} {x : ℝ}
    {G : SimpleGraph V} [DecidableRel G.Adj] {p c : V → ℝ}
    (h : ExtremalTriple r x G p c) :
    Weighted.Support.NegativeOnTwoKernels
      (Weighted.Support.quadratic (G.adjMatrix ℝ))
      Weighted.Support.totalFunctional (Weighted.Support.costFunctional c) :=
  minimal_weightMaximum_negativeOnTwoKernels h.probability h.positive h.budget
    h.weightMaximum h.minimal

theorem ExtremalTriple.stationary {r : ℕ} {x : ℝ}
    {G : SimpleGraph V} {p c : V → ℝ} (h : ExtremalTriple r x G p c) :
    ∃ lam μ : ℝ, 0 ≤ μ ∧ ∀ v, weightedDegree G p v = lam + μ * c v :=
  weightMaximum_stationary h.probability h.positive h.budget h.weightMaximum

/-- The actual compactly selected maximum has the support shape required by
the remaining weighted cases. -/
theorem ExtremalTriple.support_classification {r : ℕ} (hr : 2 ≤ r) {x : ℝ}
    {G : SimpleGraph V} {p c : V → ℝ} (h : ExtremalTriple r x G p c) :
    G = ⊤ ∨ (Weighted.Support.IsCliquePathBlowup G ∧
      r - 2 ≤ (Weighted.Support.universalVertices G).card) := by
  classical
  exact Weighted.Support.complete_or_cliquePathBlowup hr G c h.optimal.1
    (h.saturated hr) h.negative

end DensityHS
