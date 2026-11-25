module

public import DensityHS.Graphon.FinalEquality
public import DensityHS.Graphon.FinalCrossingEquality
public import DensityHS.Constructions.EndpointAlignment

/-!
# Actual active-family membership on the final phase and its crossing

Author and maintainer: Xizhi Liu.

The measurable classification theorems are converted to the canonical
interval models using the proved measure-preserving alignment theorems.
-/

@[expose] public section

namespace DensityHS.Constructions

open MeasureTheory Set Graphon ProbabilityTheory

theorem ordinaryPartition_mem_active {r q : ℕ} (hr : 3 ≤ r)
    (hq : 1 ≤ q) (hqr : q < r) {x : ℝ} (hx : x ∈ Icc 0 (1 / (r : ℝ)))
    (hactive : Phi r x = B r q x) {W : Kernel ℝ}
    (P : OrdinaryPartition r q x W unitMeasure) :
    Vendor.GraphonSpace.mk (W.toVendorGraphon unitMeasure) ∈ activeFamily r x := by
  let z : Fin (r - 1) → ℝ := fun _ => 1 / ((r - 1 : ℕ) : ℝ)
  have hs : (r - 1 : ℕ) ≠ 0 := by omega
  have hz : IsProbabilityWeight z := by
    refine ⟨fun _ => by dsimp [z]; positivity, ?_⟩
    simp [z, hs]
  apply (mem_activeFamily_iff hr).mpr
  refine ⟨.ordinary ⟨q - 1, by omega⟩, z, hx, hz, trivial, ?_, ?_⟩
  · simpa only [constructionDensity, Nat.sub_add_cancel hq] using hactive
  · simpa only [constructionGraphon, Nat.sub_add_cancel hq] using P.graphon_eq hqr hx

theorem finalPartition_mem_active {r : ℕ} (hr : 3 ≤ r) {x : ℝ}
    (hx : x ∈ Icc 0 (1 / (r : ℝ))) (hxR : RDomain r x)
    (hactive : Phi r x = R r x) {W : Kernel ℝ}
    (P : FinalPartition r x W unitMeasure) :
    Vendor.GraphonSpace.mk (W.toVendorGraphon unitMeasure) ∈ activeFamily r x := by
  obtain ⟨z, hz, hmodel⟩ := P.exists_graphon_eq (by omega : 2 ≤ r) hxR
  exact (mem_activeFamily_iff hr).mpr ⟨.final, z, hx, hz, hxR, hactive, hmodel⟩

theorem kernel_final_interior_mem_active {r : ℕ} (hr : 3 ≤ r) (W : Kernel ℝ)
    {x : ℝ} (hxl : RCrossing r < x) (hxu : x < 1 / (r : ℝ))
    (htiling : tilingNumber r W unitMeasure ≤ x)
    (he : density unitMeasure W = Phi r x) :
    Vendor.GraphonSpace.mk (W.toVendorGraphon unitMeasure) ∈ activeFamily r x := by
  have hcond : cond (volume : Measure ℝ) (Ioc 0 1) = unitMeasure := by
    simp [ProbabilityTheory.cond, unitMeasure]
  obtain ⟨P⟩ := R_classification_interior (volume : Measure ℝ) hr W
    (D := Ioc 0 1) measurableSet_Ioc (by simp) (by simp) hxl hxu
    (by simpa only [hcond] using htiling) (by simpa only [hcond] using he)
  have P' : FinalPartition r x W unitMeasure := by simpa only [hcond] using P
  have hxR := RDomain_of_after_crossing hr hxl.le hxu.le
  have hx0 : 0 ≤ x := by
    have hh := RCrossing_gt_reciprocal_succ hr
    have hp : (0 : ℝ) < 1 / ((r : ℝ) + 1) := by positivity
    linarith
  exact finalPartition_mem_active hr ⟨hx0, hxu.le⟩ hxR
    (Phi_eq_R_after_crossing hr hxl.le hxu.le) P'

theorem kernel_final_crossing_mem_active {r : ℕ} (hr : 3 ≤ r) (W : Kernel ℝ)
    (htiling : tilingNumber r W unitMeasure ≤ RCrossing r)
    (he : density unitMeasure W = Phi r (RCrossing r)) :
    Vendor.GraphonSpace.mk (W.toVendorGraphon unitMeasure) ∈
      activeFamily r (RCrossing r) := by
  have hcond : cond (volume : Measure ℝ) (Ioc 0 1) = unitMeasure := by
    simp [ProbabilityTheory.cond, unitMeasure]
  have hx0 : 0 ≤ RCrossing r := by
    have hh := RCrossing_gt_reciprocal_succ hr
    have hp : (0 : ℝ) < 1 / ((r : ℝ) + 1) := by positivity
    linarith
  have hxu := (RCrossing_lt_right_endpoint hr).le
  have hx : RCrossing r ∈ Icc 0 (1 / (r : ℝ)) := ⟨hx0, hxu⟩
  have hclasses := final_crossing_classification (volume : Measure ℝ) hr W
    (D := Ioc 0 1) measurableSet_Ioc (by simp) (by simp)
    (by simpa only [hcond] using htiling) (by simpa only [hcond] using he)
  rcases hclasses with hOrd | hFinal
  · obtain ⟨q, hq, hqr, hactive, ⟨P⟩⟩ := hOrd
    have P' : OrdinaryPartition r q (RCrossing r) W unitMeasure := by
      simpa only [hcond] using P
    exact ordinaryPartition_mem_active hr hq hqr hx hactive P'
  · obtain ⟨P⟩ := hFinal
    have P' : FinalPartition r (RCrossing r) W unitMeasure := by
      simpa only [hcond] using P
    exact finalPartition_mem_active hr hx (RDomain_of_after_crossing hr le_rfl hxu)
      (Phi_eq_R_after_crossing hr le_rfl hxu) P'

end DensityHS.Constructions
