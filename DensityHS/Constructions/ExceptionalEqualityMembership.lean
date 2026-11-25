module

public import DensityHS.Constructions.FinalEqualityMembership
public import DensityHS.Constructions.ExceptionalAlignment
public import DensityHS.Graphon.OrdinaryEquality
public import DensityHS.Graphon.ExceptionalEquality

/-!
# Active-family membership on ordinary and exceptional open phases

Author and maintainer: Xizhi Liu.

The generic exceptional-partition wrapper also applies to the first
crossing once its actual endpoint variation has selected the A model.
-/

@[expose] public section

namespace DensityHS.Constructions

open MeasureTheory Set Graphon ProbabilityTheory

theorem exceptionalPartition_mem_active {r : ℕ} (hr : 3 ≤ r) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ AEnd r) (hPhi : Phi r x = A r x)
    {W : Kernel ℝ} (P : ExceptionalPartition r x W unitMeasure) :
    Vendor.GraphonSpace.mk (W.toVendorGraphon unitMeasure) ∈ activeFamily r x := by
  have hxA : ADomain r x := ⟨hx0, hx1⟩
  have hx : x ∈ Icc 0 (1 / (r : ℝ)) := ⟨hx0, hx1.trans (A_endpoint_le (by omega))⟩
  let z : Fin (r - 1) → ℝ := fun _ => 1 / ((r - 1 : ℕ) : ℝ)
  have hs : (r - 1 : ℕ) ≠ 0 := by omega
  have hz : IsProbabilityWeight z := by
    refine ⟨fun _ => by dsimp [z]; positivity, ?_⟩
    simp [z, hs]
  exact (mem_activeFamily_iff hr).mpr
    ⟨.exceptional, z, hx, hz, hxA, hPhi, P.graphon_eq (by omega) hxA⟩

theorem kernel_ordinary_unique_mem_active {r i : ℕ} (hr : 3 ≤ r) (W : Kernel ℝ)
    {x : ℝ} (hx : x ∈ Icc 0 (1 / (r : ℝ))) (hunique : UniqueBActive r i x)
    (htiling : tilingNumber r W unitMeasure ≤ x) (he : density unitMeasure W = Phi r x) :
    Vendor.GraphonSpace.mk (W.toVendorGraphon unitMeasure) ∈ activeFamily r x := by
  have hcond : cond (volume : Measure ℝ) (Ioc 0 1) = unitMeasure := by
    simp [ProbabilityTheory.cond, unitMeasure]
  obtain ⟨P⟩ := B_classification_unique_cond hr (volume : Measure ℝ)
    (D := Ioc 0 1) measurableSet_Ioc (by simp) (by simp) W hx hunique
    (by simpa only [hcond] using htiling) (by simpa only [hcond] using he)
  have P' : OrdinaryPartition r i x W unitMeasure := by simpa only [hcond] using P
  exact ordinaryPartition_mem_active hr hunique.index_pos hunique.index_lt hx hunique.active P'

theorem kernel_exceptional_interior_mem_active {r : ℕ} (hr : 3 ≤ r) (W : Kernel ℝ)
    {x : ℝ} (hxl : AStart r < x) (hxu : x < AEnd r)
    (htiling : tilingNumber r W unitMeasure ≤ x) (he : density unitMeasure W = Phi r x) :
    Vendor.GraphonSpace.mk (W.toVendorGraphon unitMeasure) ∈ activeFamily r x := by
  have hcond : cond (volume : Measure ℝ) (Ioc 0 1) = unitMeasure := by
    simp [ProbabilityTheory.cond, unitMeasure]
  obtain ⟨P⟩ := A_classification_interior (volume : Measure ℝ) hr W
    (D := Ioc 0 1) measurableSet_Ioc (by simp) (by simp) hxl hxu
    (by simpa only [hcond] using htiling) (by simpa only [hcond] using he)
  have P' : ExceptionalPartition r x W unitMeasure := by simpa only [hcond] using P
  exact exceptionalPartition_mem_active hr ((AStart_pos hr).trans hxl).le hxu.le
    (Phi_eq_A_on_middle_interval hr hxl.le hxu.le) P'

end DensityHS.Constructions
