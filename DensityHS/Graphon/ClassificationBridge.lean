module

public import DensityHS.Graphon.MetricTilings

/-!
# Passing a concrete equality classification to the compact graphon quotient

Author and maintainer: Xizhi Liu.

Every quotient class has a pointwise bounded symmetric measurable kernel
representative. Actual density and actual clique-tiling number are preserved.
This is a transfer theorem; the concrete classification is an explicit input.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] [NullSingletonClass μ]

theorem graphonSpace_classification_of_kernel {r : ℕ} (hr : 0 < r)
    {x d : ℝ} {F : Set (Vendor.GraphonSpace Ω μ)}
    (hclass : ∀ W : Kernel Ω, tilingNumber r W μ ≤ x → density μ W = d →
      Vendor.GraphonSpace.mk (W.toVendorGraphon μ) ∈ F)
    (W : Vendor.GraphonSpace Ω μ)
    (htiling : graphonSpaceTilingNumber μ r hr W ≤ x)
    (he : graphonSpaceDensity μ W = d) : W ∈ F := by
  obtain ⟨U, rfl⟩ := Vendor.GraphonSpace.surjective_mk W
  have ht : tilingNumber r (vendorRepresentative μ U) μ ≤ x := htiling
  have hd : density μ (vendorRepresentative μ U) = d := by
    rw [density_vendorRepresentative]
    exact he
  simpa only [toVendorGraphon_vendorRepresentative] using
    hclass (vendorRepresentative μ U) ht hd

end DensityHS.Graphon
