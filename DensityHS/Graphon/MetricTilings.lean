module

public import DensityHS.Graphon.CutSemicontinuity
public import DensityHS.Graphon.Pullback
public import DensityHS.Graphon.MetricDensity
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Fractional tilings on the compact metric graphon space

Author and maintainer: Xizhi Liu.

The cut-norm lower-semicontinuity proof is transported through actual
measure-preserving bijections supplied by the graphon overlay theorem.
It then descends to the compact metric quotient, retaining the independently
defined integral tiling number.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set
open scoped Topology

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [IsProbabilityMeasure μ] [StandardBorelSpace Ω] [NullSingletonClass μ]

noncomputable def vendorCoverNumber (r : ℕ) (W : Vendor.Graphon Ω μ) : ℝ :=
  coverNumber r (vendorRepresentative μ W) μ

noncomputable def vendorTilingNumber (r : ℕ) (W : Vendor.Graphon Ω μ) : ℝ :=
  tilingNumber r (vendorRepresentative μ W) μ

theorem vendorTilingNumber_eq_coverNumber {r : ℕ} (hr : 0<r) (W : Vendor.Graphon Ω μ) :
    vendorTilingNumber μ r W=vendorCoverNumber μ r W :=
  kernel_tiling_cover_duality r (vendorRepresentative μ W) μ hr

theorem exists_cutDistance_neighborhood_coverNumber_gt {r : ℕ} (hr : 0<r)
    (W : Vendor.Graphon Ω μ) {a : ℝ} (ha : a<vendorCoverNumber μ r W) :
    ∃ δ>0, ∀ U : Vendor.Graphon Ω μ,
      Vendor.Graphon.cutDistance W U<δ → a<vendorCoverNumber μ r U := by
  obtain ⟨δ,hδ,hnear⟩ := exists_cutNorm_neighborhood_coverNumber_gt hr
    (vendorRepresentative μ W) μ ha
  refine ⟨δ/2,half_pos hδ,?_⟩
  intro U hU
  obtain ⟨σ,hσ,hcut⟩ := Vendor.Graphon.exists_mpEquiv_cutNormDiff_lt_add U W (half_pos hδ)
  let K := (vendorRepresentative μ U).comap σ hσ.measurable
  have hk : kernelCutDistance μ (vendorRepresentative μ W) K<δ := by
    rw [kernelCutDistance_comm,← cutNormDiff_toVendorGraphon]
    dsimp [K]
    rw [toVendorGraphon_comap (ν := μ) (vendorRepresentative μ U) hσ,toVendorGraphon_vendorRepresentative,
      toVendorGraphon_vendorRepresentative] 
    rw [Vendor.Graphon.cutDistance_symm U W] at hcut
    linarith
  have h := hnear K hk
  change a<coverNumber r ((vendorRepresentative μ U).comap σ hσ.measurable) μ at h
  rw [coverNumber_comap_equiv hr (vendorRepresentative μ U) σ hσ] at h
  exact h

theorem lowerSemicontinuous_vendorCoverNumber {r : ℕ} (hr : 0<r) :
    LowerSemicontinuous (vendorCoverNumber μ r) := by
  intro W a ha
  obtain ⟨δ,hδ,hnear⟩ := exists_cutDistance_neighborhood_coverNumber_gt μ hr W ha
  apply Metric.eventually_nhds_iff.mpr
  refine ⟨δ,hδ,?_⟩
  intro U hU
  apply hnear U
  change Vendor.Graphon.cutDistance U W<δ at hU
  rwa [Vendor.Graphon.cutDistance_symm]

theorem vendorCoverNumber_eq_of_cutDistance_zero {r : ℕ} (hr : 0<r)
    {W U : Vendor.Graphon Ω μ} (h : Vendor.Graphon.cutDistance W U=0) :
    vendorCoverNumber μ r W=vendorCoverNumber μ r U := by
  have hle {A B : Vendor.Graphon Ω μ} (hab : Vendor.Graphon.cutDistance A B=0) :
      vendorCoverNumber μ r A≤vendorCoverNumber μ r B := by
    by_contra! hbad
    obtain ⟨δ,hδ,hnear⟩ := exists_cutDistance_neighborhood_coverNumber_gt μ hr A hbad
    have hh := hnear B (by rwa [hab])
    exact lt_irrefl _ hh
  exact le_antisymm (hle h) (hle (by rwa [Vendor.Graphon.cutDistance_symm]))

theorem vendorTilingNumber_eq_of_inseparable {r : ℕ} (hr : 0<r)
    {W U : Vendor.Graphon Ω μ} (h : Inseparable W U) :
    vendorTilingNumber μ r W=vendorTilingNumber μ r U := by
  simp only [vendorTilingNumber_eq_coverNumber μ hr]
  exact vendorCoverNumber_eq_of_cutDistance_zero μ hr (Metric.inseparable_iff.mp h)

/-- Actual integral clique-tiling number on the compact graphon quotient. -/
noncomputable def graphonSpaceTilingNumber (r : ℕ) (hr : 0<r) : Vendor.GraphonSpace Ω μ → ℝ :=
  SeparationQuotient.lift (vendorTilingNumber μ r)
    (fun _ _ h => vendorTilingNumber_eq_of_inseparable μ hr h)

@[simp] theorem graphonSpaceTilingNumber_mk {r : ℕ} (hr : 0<r)
    (W : Vendor.Graphon Ω μ) :
    graphonSpaceTilingNumber μ r hr (Vendor.GraphonSpace.mk W)=vendorTilingNumber μ r W := rfl

theorem lowerSemicontinuous_graphonSpaceTilingNumber {r : ℕ} (hr : 0<r) :
    LowerSemicontinuous (graphonSpaceTilingNumber μ r hr) := by
  apply lowerSemicontinuous_iff_isOpen_preimage.mpr
  intro a
  apply SeparationQuotient.isQuotientMap_mk.isOpen_preimage.mp
  have h := (lowerSemicontinuous_vendorCoverNumber μ hr).isOpen_preimage a
  change IsOpen {W : Vendor.Graphon Ω μ | a<vendorTilingNumber μ r W}
  change IsOpen {W : Vendor.Graphon Ω μ | a<vendorCoverNumber μ r W} at h
  simpa only [vendorTilingNumber_eq_coverNumber μ hr] using h

theorem graphonSpaceTilingNumber_kernel {r : ℕ} (hr : 0<r) (W : Kernel Ω) :
    graphonSpaceTilingNumber μ r hr (Vendor.GraphonSpace.mk (W.toVendorGraphon μ))=
      tilingNumber r W μ :=
  tilingNumber_congr_ae hr (vendorRepresentative_toVendorGraphon_ae μ W)

theorem graphonSpace_density_bound {r : ℕ} (hr : 2≤r) (W : Vendor.GraphonSpace Ω μ) :
    graphonSpaceDensity μ W ≤ Phi r (graphonSpaceTilingNumber μ r (by omega) W) := by
  obtain ⟨U,rfl⟩ := Vendor.GraphonSpace.surjective_mk W
  rw [graphonSpaceDensity_mk,graphonSpaceTilingNumber_mk,← density_vendorRepresentative]
  exact kernel_tilingNumber_density_bound hr μ (vendorRepresentative μ U)

end DensityHS.Graphon
