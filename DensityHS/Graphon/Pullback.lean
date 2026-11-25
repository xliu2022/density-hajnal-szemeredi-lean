module

public import DensityHS.Graphon.VendorBridge

/-!
# Relabelling concrete kernels and covers

Author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory

variable {Ω Λ : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]

/-- Pullback of an everywhere-defined kernel by a measurable map. -/
def Kernel.comap (W : Kernel Λ) (φ : Ω → Λ) (hφ : Measurable φ) : Kernel Ω where
  toFun x y := W (φ x) (φ y)
  measurable_uncurry := W.measurable_uncurry.comp (hφ.prodMap hφ)
  symmetric x y := W.symmetric _ _
  nonneg x y := W.nonneg _ _
  le_one x y := W.le_one _ _

theorem IsKernelCover.comap {r : ℕ} {W : Kernel Λ} {μ : Measure Ω} {ν : Measure Λ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {c : Λ → ℝ}
    (hc : IsKernelCover r W ν c) {φ : Ω → Λ} (hφ : MeasurePreserving φ μ ν) :
    IsKernelCover r (W.comap φ hφ.measurable) μ (c ∘ φ) := by
  refine ⟨hc.measurable.comp hφ.measurable,fun x => hc.2.1 (φ x),?_⟩
  have hm : MeasurePreserving (fun t : Fin r → Ω => fun i => φ (t i))
      (Measure.pi (fun _ => μ)) (Measure.pi (fun _ => ν)) :=
    measurePreserving_pi _ _ (fun _ => hφ)
  exact hm.quasiMeasurePreserving.ae hc.2.2

theorem integral_comap_measurable {μ : Measure Ω} {ν : Measure Λ}
    {φ : Ω → Λ} (hφ : MeasurePreserving φ μ ν) {c : Λ → ℝ} (hc : Measurable c) :
    (∫ x, c (φ x) ∂μ)=∫ y, c y ∂ν := by
  have h := integral_map_of_stronglyMeasurable (μ := μ) hφ.measurable hc.stronglyMeasurable
  rw [hφ.map_eq] at h
  exact h.symm

theorem coverNumber_comap_le {r : ℕ} (hr : 0<r) (W : Kernel Λ)
    {μ : Measure Ω} {ν : Measure Λ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {φ : Ω → Λ} (hφ : MeasurePreserving φ μ ν) :
    coverNumber r (W.comap φ hφ.measurable) μ ≤ coverNumber r W ν := by
  apply le_csInf (kernelCoverCosts_nonempty r W ν hr)
  rintro a ⟨c,hc,rfl⟩
  exact (coverNumber_le_cost (hc.comap hφ)).trans_eq (integral_comap_measurable hφ hc.measurable)

theorem coverNumber_comap_equiv {r : ℕ} (hr : 0<r) (W : Kernel Λ)
    {μ : Measure Ω} {ν : Measure Λ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (φ : Ω ≃ᵐ Λ) (hφ : MeasurePreserving φ μ ν) :
    coverNumber r (W.comap φ hφ.measurable) μ = coverNumber r W ν := by
  apply le_antisymm (coverNumber_comap_le hr W hφ)
  have h := coverNumber_comap_le hr (W.comap φ hφ.measurable) (hφ.symm φ)
  have he : Function.uncurry ((W.comap φ hφ.measurable).comap φ.symm (hφ.symm φ).measurable)
      =ᵐ[ν.prod ν] Function.uncurry W :=
    Filter.Eventually.of_forall fun z => by simp [Kernel.comap,Function.uncurry]
  rw [coverNumber_congr_ae r he] at h
  exact h

theorem tilingNumber_comap_equiv {r : ℕ} (hr : 0<r) (W : Kernel Λ)
    {μ : Measure Ω} {ν : Measure Λ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (φ : Ω ≃ᵐ Λ) (hφ : MeasurePreserving φ μ ν) :
    tilingNumber r (W.comap φ hφ.measurable) μ = tilingNumber r W ν := by
  simp only [kernel_tiling_cover_duality r _ _ hr]
  exact coverNumber_comap_equiv hr W φ hφ

theorem toVendorGraphon_comap (W : Kernel Λ) {μ : Measure Ω} {ν : Measure Λ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {φ : Ω → Λ}
    (hφ : MeasurePreserving φ μ ν) :
    (W.comap φ hφ.measurable).toVendorGraphon μ =
      Vendor.Graphon.pullback (W.toVendorGraphon ν) φ hφ := by
  apply Vendor.Graphon.ext
  apply Vendor.SymmKernel.ext
  apply AEEqFun.ext
  have hm := Vendor.SymmKernel.measurePreserving_prodMap_self hφ
  filter_upwards [(W.comap φ hφ.measurable).toVendorGraphon_ae μ,
    Vendor.Graphon.pullback_ae (W.toVendorGraphon ν) φ hφ,
    hm.quasiMeasurePreserving.ae (W.toVendorGraphon_ae ν)] with z hc hp hw
  change (W.toVendorGraphon ν).toAEEqFun (φ z.1,φ z.2)=W (φ z.1) (φ z.2) at hw
  rw [hc,hp,hw]
  rfl

theorem kernelCutDistance_comm (μ : Measure Ω) [IsProbabilityMeasure μ] (W U : Kernel Ω) :
    kernelCutDistance μ W U=kernelCutDistance μ U W := by
  rw [← cutNormDiff_toVendorGraphon,← cutNormDiff_toVendorGraphon]
  exact Vendor.Graphon.cutNormDiff_symm _ _

end DensityHS.Graphon
