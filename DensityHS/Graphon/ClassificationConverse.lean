module

public import DensityHS.Constructions.TemplateCovers
public import DensityHS.Graphon.MetricTilings

/-!
# Every active construction is an actual extremal graphon

Author and maintainer: Xizhi Liu.

This is the reverse inclusion in the manuscript's equality classification.
It uses explicit feasible covers of the actual construction kernels, exact
density calculations, and invariance on the compact graphon quotient.
No necessity classification is imported or assumed.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set Constructions

theorem constructionGraphon_eq_mk (r : ℕ) (t : ConstructionKind r)
    (p : ℝ × (Fin (r - 1) → ℝ)) :
    constructionGraphon r t p =
      Vendor.GraphonSpace.mk ((constructionKernel r t p).toVendorGraphon unitMeasure) := by
  cases t <;> rfl

theorem activeFamily_tiling_eq_and_density {r : ℕ} (hr : 3 ≤ r) {x : ℝ}
    {W : Vendor.GraphonSpace ℝ unitMeasure} (hW : W ∈ activeFamily r x) :
    graphonSpaceTilingNumber unitMeasure r (by omega) W = x ∧
      graphonSpaceDensity unitMeasure W = Phi r x := by
  obtain ⟨t, z, hx, hz, hd, hactive, rfl⟩ := (mem_activeFamily_iff hr).mp hW
  rw [constructionGraphon_eq_mk, graphonSpaceTilingNumber_kernel,
    graphonSpaceDensity_kernel]
  exact ⟨active_construction_tiling_eq hr t hx hz hd hactive.symm,
    (density_constructionKernel hr t hx hz hd).trans hactive.symm⟩

theorem activeFamily_extremal {r : ℕ} (hr : 3 ≤ r) {x : ℝ}
    {W : Vendor.GraphonSpace ℝ unitMeasure} (hW : W ∈ activeFamily r x) :
    graphonSpaceTilingNumber unitMeasure r (by omega) W ≤ x ∧
      graphonSpaceDensity unitMeasure W = Phi r x := by
  obtain ⟨ht, hd⟩ := activeFamily_tiling_eq_and_density hr hW
  exact ⟨ht.le, hd⟩

theorem kernel_extremal_of_mem_activeFamily {r : ℕ} (hr : 3 ≤ r) {x : ℝ}
    (W : Kernel ℝ)
    (hW : Vendor.GraphonSpace.mk (W.toVendorGraphon unitMeasure) ∈ activeFamily r x) :
    tilingNumber r W unitMeasure = x ∧ density unitMeasure W = Phi r x := by
  simpa only [graphonSpaceTilingNumber_kernel, graphonSpaceDensity_kernel] using
    activeFamily_tiling_eq_and_density hr hW

end DensityHS.Graphon
