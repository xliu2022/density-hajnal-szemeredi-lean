module

public import DensityHS.Graphon.Congruence
public import DensityHS.Graphon.CutL1
public import DensityHS.Vendor.Graphon.CutDistance

/-!
# Concrete kernels and the graphon compactness library

Author and maintainer: Xizhi Liu.

The density and duality proofs use everywhere-defined measurable kernels.
The imported compactness proof uses almost-everywhere equivalence classes.
This file supplies actual conversions in both directions and proves that
the cut norm and density agree. The conversion back clips and symmetrizes
a measurable representative; it does not assume a representative theorem.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [IsProbabilityMeasure μ]

/-- Regard a concrete kernel as an almost-everywhere graphon. -/
noncomputable def Kernel.toVendorGraphon (W : Kernel Ω) : Vendor.Graphon Ω μ where
  toAEEqFun := AEEqFun.mk (Function.uncurry W) W.measurable_uncurry.aestronglyMeasurable
  symm' := by
    have h := AEEqFun.coeFn_mk (μ := μ.prod μ) (Function.uncurry W) W.measurable_uncurry.aestronglyMeasurable
    have hs := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae h
    filter_upwards [h,hs] with z hz hzs
    rw [hz,hzs]
    exact W.symmetric z.2 z.1
  ae_mem_Icc := by
    filter_upwards [AEEqFun.coeFn_mk (Function.uncurry W)
      W.measurable_uncurry.aestronglyMeasurable] with z hz
    rw [hz]
    exact ⟨W.nonneg z.1 z.2,W.le_one z.1 z.2⟩

theorem Kernel.toVendorGraphon_ae (W : Kernel Ω) :
    (W.toVendorGraphon μ).toAEEqFun =ᵐ[μ.prod μ] Function.uncurry W :=
  AEEqFun.coeFn_mk (Function.uncurry W) W.measurable_uncurry.aestronglyMeasurable

/-- A pointwise symmetric bounded measurable representative of an a.e. graphon. -/
noncomputable def vendorRepresentative (W : Vendor.Graphon Ω μ) : Kernel Ω where
  toFun x y := max 0 (min 1 ((W.toAEEqFun (x,y)+W.toAEEqFun (y,x))/2))
  measurable_uncurry := by
    exact measurable_const.max (measurable_const.min
      ((W.toAEEqFun.measurable.add (W.toAEEqFun.measurable.comp measurable_swap)).div_const 2))
  symmetric x y := by simp only [add_comm]
  nonneg x y := le_max_left _ _
  le_one x y := max_le (by norm_num) (min_le_left _ _)

theorem vendorRepresentative_ae (W : Vendor.Graphon Ω μ) :
    Function.uncurry (vendorRepresentative μ W) =ᵐ[μ.prod μ] W.toAEEqFun := by
  filter_upwards [W.symm_ae,W.ae_mem_Icc] with z hs hb
  change max 0 (min 1 ((W.toAEEqFun z+W.toAEEqFun z.swap)/2)) = W.toAEEqFun z
  rw [hs]
  have h : (W.toAEEqFun z+W.toAEEqFun z)/2 = W.toAEEqFun z := by ring
  rw [h,min_eq_right hb.2,max_eq_right hb.1]

theorem toVendorGraphon_vendorRepresentative (W : Vendor.Graphon Ω μ) :
    (vendorRepresentative μ W).toVendorGraphon μ = W := by
  apply Vendor.Graphon.ext
  apply Vendor.SymmKernel.ext
  apply AEEqFun.ext
  exact ((vendorRepresentative μ W).toVendorGraphon_ae μ).trans
    (vendorRepresentative_ae μ W)

theorem vendorRepresentative_toVendorGraphon_ae (W : Kernel Ω) :
    Function.uncurry (vendorRepresentative μ (W.toVendorGraphon μ)) =ᵐ[μ.prod μ]
      Function.uncurry W :=
  (vendorRepresentative_ae μ (W.toVendorGraphon μ)).trans (W.toVendorGraphon_ae μ)

theorem Kernel.toVendorGraphon_surjective :
    Function.Surjective (Kernel.toVendorGraphon μ : Kernel Ω → Vendor.Graphon Ω μ) :=
  fun W => ⟨vendorRepresentative μ W,toVendorGraphon_vendorRepresentative μ W⟩

/-- The imported graphon convention counts ordered pairs; the paper counts
undirected edges, hence the factor one half. -/
noncomputable def vendorDensity (W : Vendor.Graphon Ω μ) : ℝ :=
  (∫ z, W.toAEEqFun z ∂μ.prod μ)/2

theorem vendorDensity_toVendorGraphon (W : Kernel Ω) :
    vendorDensity μ (W.toVendorGraphon μ) = density μ W := by
  rw [density_eq_prod_integral]
  exact congrArg (fun x : ℝ => x/2) (integral_congr_ae (W.toVendorGraphon_ae μ))

theorem density_vendorRepresentative (W : Vendor.Graphon Ω μ) :
    density μ (vendorRepresentative μ W) = vendorDensity μ W := by
  rw [density_eq_prod_integral]
  exact congrArg (fun x : ℝ => x/2) (integral_congr_ae (vendorRepresentative_ae μ W))

theorem rectIntegralDiff_toVendorGraphon (W U : Kernel Ω) (s t : Set Ω) :
    Vendor.Graphon.rectIntegralDiff (W.toVendorGraphon μ) (U.toVendorGraphon μ) s t =
      ∫ z in s ×ˢ t, W z.1 z.2-U z.1 z.2 ∂μ.prod μ := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (W.toVendorGraphon_ae μ),
    ae_restrict_of_ae (U.toVendorGraphon_ae μ)] with z hW hU
  rw [hW,hU]
  rfl

theorem cutNormDiff_toVendorGraphon (W U : Kernel Ω) :
    Vendor.Graphon.cutNormDiff (W.toVendorGraphon μ) (U.toVendorGraphon μ) =
      kernelCutDistance μ W U := by
  apply le_antisymm
  · unfold Vendor.Graphon.cutNormDiff
    apply Real.iSup_le _ (kernelCutDistance_nonneg μ W U)
    intro s
    apply Real.iSup_le _ (kernelCutDistance_nonneg μ W U)
    intro hs
    apply Real.iSup_le _ (kernelCutDistance_nonneg μ W U)
    intro t
    apply Real.iSup_le _ (kernelCutDistance_nonneg μ W U)
    intro ht
    rw [rectIntegralDiff_toVendorGraphon]
    exact rectangle_discrepancy_le_cut μ W U hs ht
  · apply csSup_le ⟨0,zero_mem_rectangleDiscrepancies μ W U⟩
    rintro a ⟨s,t,hs,ht,rfl⟩
    rw [← rectIntegralDiff_toVendorGraphon]
    exact Vendor.Graphon.abs_rectIntegralDiff_le _ _ hs ht

end DensityHS.Graphon
