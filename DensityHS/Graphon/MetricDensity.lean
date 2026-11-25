module

public import DensityHS.Graphon.VendorBridge
public import DensityHS.Vendor.Graphon.GraphonSpace

/-!
# Edge density on the compact graphon space

Author and maintainer: Xizhi Liu.

The concrete density descends to the actual compact metric quotient. Its
continuity follows from a quantitative bound by the cut distance, including
the relabellings in the definition of that distance.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [IsProbabilityMeasure μ]

theorem vendorDensity_pullback (W : Vendor.Graphon Ω μ) (φ : Ω → Ω)
    (hφ : MeasurePreserving φ μ μ) :
    vendorDensity μ (Vendor.Graphon.pullback W φ hφ) = vendorDensity μ W := by
  unfold vendorDensity
  apply congrArg (fun x : ℝ => x/2)
  calc
    (∫ z, (Vendor.Graphon.pullback W φ hφ).toAEEqFun z ∂μ.prod μ) =
        ∫ z, W.toAEEqFun (φ z.1,φ z.2) ∂μ.prod μ :=
      integral_congr_ae (Vendor.Graphon.pullback_ae W φ hφ)
    _ = ∫ z, W.toAEEqFun z ∂μ.prod μ := by
      have hm := Vendor.SymmKernel.measurePreserving_prodMap_self hφ
      have hi := integral_map_of_stronglyMeasurable (μ := μ.prod μ) hm.measurable
        W.toAEEqFun.measurable.stronglyMeasurable
      rw [hm.map_eq] at hi
      exact hi.symm

theorem abs_vendorDensity_sub_le_half_cutNormDiff (W U : Vendor.Graphon Ω μ) :
    |vendorDensity μ W-vendorDensity μ U| ≤ Vendor.Graphon.cutNormDiff W U/2 := by
  have h := Vendor.Graphon.abs_rectIntegralDiff_le W U MeasurableSet.univ MeasurableSet.univ
  rw [Vendor.Graphon.rectIntegralDiff, univ_prod_univ,setIntegral_univ,
    integral_sub (Vendor.SymmKernel.graphon_integrable W)
      (Vendor.SymmKernel.graphon_integrable U)] at h
  unfold vendorDensity
  rw [← sub_div,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  exact div_le_div_of_nonneg_right h (by norm_num)

theorem abs_vendorDensity_sub_le_half_cutDistance (W U : Vendor.Graphon Ω μ) :
    |vendorDensity μ W-vendorDensity μ U| ≤ Vendor.Graphon.cutDistance W U/2 := by
  apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
  apply le_csInf (Vendor.Graphon.cutDistance_set_nonempty W U)
  rintro a ⟨φ,ψ,hφ,hψ,rfl⟩
  have h := abs_vendorDensity_sub_le_half_cutNormDiff μ
    (Vendor.Graphon.pullback W φ hφ) (Vendor.Graphon.pullback U ψ hψ)
  rw [vendorDensity_pullback,vendorDensity_pullback] at h
  linarith

section Metric

variable [StandardBorelSpace Ω] [NullSingletonClass μ]

theorem lipschitz_vendorDensity : LipschitzWith 1 (vendorDensity μ) := by
  apply LipschitzWith.of_dist_le_mul
  intro W U
  change |vendorDensity μ W-vendorDensity μ U| ≤ (1:ℝ)*Vendor.Graphon.cutDistance W U
  have h := abs_vendorDensity_sub_le_half_cutDistance μ W U
  have hn := Vendor.Graphon.cutDistance_nonneg W U
  linarith

theorem vendorDensity_eq_of_inseparable {W U : Vendor.Graphon Ω μ}
    (h : Inseparable W U) : vendorDensity μ W = vendorDensity μ U :=
  by
    have hz : Vendor.Graphon.cutDistance W U = 0 := Metric.inseparable_iff.mp h
    have hb := abs_vendorDensity_sub_le_half_cutDistance μ W U
    rw [hz,zero_div] at hb
    exact sub_eq_zero.mp (abs_nonpos_iff.mp hb)

/-- The paper's undirected edge density on the compact quotient of graphons. -/
noncomputable def graphonSpaceDensity : Vendor.GraphonSpace Ω μ → ℝ :=
  SeparationQuotient.lift (vendorDensity μ) (fun _ _ h => vendorDensity_eq_of_inseparable μ h)

@[simp] theorem graphonSpaceDensity_mk (W : Vendor.Graphon Ω μ) :
    graphonSpaceDensity μ (Vendor.GraphonSpace.mk W) = vendorDensity μ W := rfl

theorem continuous_graphonSpaceDensity : Continuous (graphonSpaceDensity μ) :=
  SeparationQuotient.continuous_lift ((lipschitz_vendorDensity μ).continuous)

theorem graphonSpaceDensity_kernel (W : Kernel Ω) :
    graphonSpaceDensity μ (Vendor.GraphonSpace.mk (W.toVendorGraphon μ)) = density μ W :=
  vendorDensity_toVendorGraphon μ W

end Metric

end DensityHS.Graphon
