module

public import DensityHS.Constructions.FinalEqualityMembership
public import DensityHS.Graphon.ClassificationBridge

/-!
# Equality throughout the closed final phase

Author and maintainer: Xizhi Liu.

The final crossing, the open final phase, and the complete endpoint are
combined, both for actual kernels and for their compact graphon quotient.
-/

@[expose] public section

namespace DensityHS.Constructions

open MeasureTheory Set Graphon

theorem kernel_final_region_mem_active {r : ℕ} (hr : 3 ≤ r) (W : Kernel ℝ)
    {x : ℝ} (hxl : RCrossing r ≤ x) (hxu : x ≤ 1 / (r : ℝ))
    (htiling : tilingNumber r W unitMeasure ≤ x)
    (he : density unitMeasure W = Phi r x) :
    Vendor.GraphonSpace.mk (W.toVendorGraphon unitMeasure) ∈ activeFamily r x := by
  rcases hxu.eq_or_lt with rfl | hxu
  · exact kernel_full_endpoint_mem_active hr W he
  rcases hxl.eq_or_lt with rfl | hxl
  · exact kernel_final_crossing_mem_active hr W htiling he
  · exact kernel_final_interior_mem_active hr W hxl hxu htiling he

theorem graphonSpace_final_region_mem_active {r : ℕ} (hr : 3 ≤ r)
    (W : Vendor.GraphonSpace ℝ unitMeasure)
    {x : ℝ} (hxl : RCrossing r ≤ x) (hxu : x ≤ 1 / (r : ℝ))
    (htiling : graphonSpaceTilingNumber unitMeasure r (by omega) W ≤ x)
    (he : graphonSpaceDensity unitMeasure W = Phi r x) :
    W ∈ activeFamily r x := by
  exact graphonSpace_classification_of_kernel unitMeasure (by omega)
    (fun U => kernel_final_region_mem_active hr U hxl hxu) W htiling he

end DensityHS.Constructions
