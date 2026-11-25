module

public import DensityHS.Graphon.Pullback
public import DensityHS.Vendor.Graphon.Overlay

/-!
# Cut distance controls edit distance from binary step graphons

Author and maintainer: Xizhi Liu.

The distance is an infimum over actual measure-preserving measurable
bijections. The already proved rectangle estimate is combined with the
proved overlay theorem; relabelling is not an abstract assumed operation.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

def relabelL1Values (W U : Kernel Ω) : Set ℝ :=
  {d | ∃ σ : Ω ≃ᵐ Ω, ∃ hσ : MeasurePreserving σ μ μ,
    d=kernelL1Distance μ (W.comap σ hσ.measurable) U}

noncomputable def relabelL1Distance (W U : Kernel Ω) : ℝ := sInf (relabelL1Values μ W U)

theorem relabelL1Values_nonempty (W U : Kernel Ω) : (relabelL1Values μ W U).Nonempty :=
  ⟨kernelL1Distance μ (W.comap (MeasurableEquiv.refl Ω) measurable_id) U,
    MeasurableEquiv.refl Ω,MeasurePreserving.id μ,rfl⟩

theorem relabelL1Values_bddBelow (W U : Kernel Ω) : BddBelow (relabelL1Values μ W U) := by
  refine ⟨0,?_⟩
  rintro d ⟨σ,hσ,rfl⟩
  exact kernelL1Distance_nonneg μ _ U

theorem relabelL1Distance_nonneg (W U : Kernel Ω) : 0≤relabelL1Distance μ W U := by
  apply le_csInf (relabelL1Values_nonempty μ W U)
  rintro d ⟨σ,hσ,rfl⟩
  exact kernelL1Distance_nonneg μ _ U

theorem relabelL1Distance_le_relabel (W U : Kernel Ω) (σ : Ω ≃ᵐ Ω)
    (hσ : MeasurePreserving σ μ μ) :
    relabelL1Distance μ W U≤kernelL1Distance μ (W.comap σ hσ.measurable) U :=
  csInf_le (relabelL1Values_bddBelow μ W U) ⟨σ,hσ,rfl⟩

/-- The full cut-to-L¹ statement, including minimization over relabellings. -/
theorem binary_step_relabelL1_le_card_sq_mul_cutDistance
    [StandardBorelSpace Ω] [NullSingletonClass μ] {I : Type*} [Fintype I]
    (W U : Kernel Ω) (label : Ω → I)
    (hlabel : ∀ i, MeasurableSet {x | label x=i})
    (A : I → I → ℝ) (hA : ∀ i j, A i j=0 ∨ A i j=1)
    (hstep : ∀ x y, U x y=A (label x) (label y)) :
    relabelL1Distance μ W U ≤ (Fintype.card I:ℝ)^2*
      Vendor.Graphon.cutDistance (W.toVendorGraphon μ) (U.toVendorGraphon μ) := by
  let C : ℝ := (Fintype.card I:ℝ)^2
  have hC : 0≤C := sq_nonneg _
  have hC1 : 0<C+1 := by linarith
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨σ,hσ,hcut⟩ := Vendor.Graphon.exists_mpEquiv_cutNormDiff_lt_add
    (W.toVendorGraphon μ) (U.toVendorGraphon μ) (div_pos hε hC1)
  have hlocal := binary_step_L1_le_card_sq_mul_cut μ (W.comap σ hσ.measurable)
    U label hlabel A hA hstep
  have hn := relabelL1Distance_le_relabel μ W U σ hσ
  rw [← cutNormDiff_toVendorGraphon,toVendorGraphon_comap (ν := μ) W hσ] at hlocal
  have hm := mul_le_mul_of_nonneg_left hcut.le hC
  have he : ε/(C+1)*(C+1)=ε := div_mul_cancel₀ ε hC1.ne'
  have hδ : 0<ε/(C+1) := div_pos hε hC1
  change relabelL1Distance μ W U ≤ C*Vendor.Graphon.cutDistance
    (W.toVendorGraphon μ) (U.toVendorGraphon μ)+ε
  change kernelL1Distance μ (W.comap σ hσ.measurable) U ≤ C*_ at hlocal
  nlinarith

end DensityHS.Graphon
