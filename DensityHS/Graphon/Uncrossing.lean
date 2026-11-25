module

public import DensityHS.Graphon.FiniteUncrossing
public import DensityHS.Graphon.FlatDirection
public import DensityHS.Graphon.Variation

/-!
# Actual uncrossing of zero-cover twin defects

Author and maintainer: Xizhi Liu.

The bounded Hilbert-space direction is replaced by its explicit four-step
representative.  Its positive endpoint changes the actual measure and
strictly lowers the finite complexity.  Tangent nonpositivity is rederived
from the density theorem at every new measure, so the iteration needs no
unproved invariance of a variational hypothesis.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal InnerProductSpace

variable {Ω I : Type*} [MeasurableSpace Ω]

/-- Exact extremality alone gives nonpositivity on every bounded direction
preserving both mass and the cost of the same cover. -/
theorem kernel_tangent_nonpositive_of_extremal {r : ℕ} (hr : 2 ≤ r)
    (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {c : Ω → ℝ} (hc : IsKernelCover r W μ c) {x : ℝ}
    (hx : x ≤ 1 / (r : ℝ)) (hcx : (∫ z, c z ∂μ) = x)
    (he : density μ W = Phi r x) (f : Lp ℝ 2 μ)
    (hf : f ∈ DensityHS.Analysis.boundedL2 μ)
    (hfmean : (∫ z, f z ∂μ) = 0) (hfcost : (∫ z, c z * f z ∂μ) = 0) :
    ⟪f, kernelOperator W μ f⟫_ℝ ≤ 0 := by
  obtain ⟨g, B, hgm, hB0, hB, hgf⟩ := exists_bounded_measurable_representative hf
  have hg : Integrable g μ := integrable_of_norm_bounded hgm hB
  have hgmean : (∫ z, g z ∂μ) = 0 := (integral_congr_ae hgf).trans hfmean
  have hgcost : (∫ z, c z * g z ∂μ) = 0 := by
    calc
      _ = ∫ z, c z * f z ∂μ := by
        apply integral_congr_ae
        filter_upwards [hgf] with z hz
        rw [hz]
      _ = 0 := hfcost
  have hpoly : ∀ t : ℝ, |t| < 1 / (B + 1) →
      (∫ z, kernelDegree W μ z * g z ∂μ) * t +
        (kernelQuadratic W μ g / 2) * t ^ 2 ≤ 0 := by
    intro t ht
    have hw := perturbationWeight_nonneg_of_abs_lt hB0 hB ht
    letI := isProbabilityMeasure_perturbedMeasure hg hgmean t hw
    have hcost : (∫ z, c z ∂perturbedMeasure μ g t) = x := by
      rw [hc.cost_perturbed hg t hw, hcx, hgcost, mul_zero, add_zero]
    have hbd := kernel_clique_cover_density_bound hr (hc.perturbed hg t)
      (by rw [hcost]; exact hx)
    rw [hcost, density_perturbedMeasure W hg t hw, he] at hbd
    nlinarith
  have hq := (local_quadratic_coefficients (by positivity : 0 < 1 / (B + 1)) hpoly).2
  have hq' : kernelQuadratic W μ g ≤ 0 := by linarith
  rwa [kernelQuadratic_congr_ae W μ hgf, kernelQuadratic_eq_inner] at hq'

/-- The explicit simple-function representative of the four-block move. -/
noncomputable def fourBlockDirection (μ : Measure Ω) (A B C D : Set Ω)
    (α β : ℝ) (z : Ω) : ℝ :=
  β * (normalizedBlock μ A z - normalizedBlock μ C z) +
    α * (normalizedBlock μ D z - normalizedBlock μ B z)

theorem normalizedBlock_nonneg (μ : Measure Ω) (S : Set Ω) (z : Ω) :
    0 ≤ normalizedBlock μ S z :=
  Set.indicator_nonneg (fun _ _ => inv_nonneg.mpr measureReal_nonneg) z

theorem fourBlockDirection_coe (μ : Measure Ω) [IsFiniteMeasure μ]
    {A B C D : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hD : MeasurableSet D) (α β : ℝ) :
    ⇑(β • (normalizedBlockL2 μ A hA - normalizedBlockL2 μ C hC) +
      α • (normalizedBlockL2 μ D hD - normalizedBlockL2 μ B hB) : Lp ℝ 2 μ) =ᵐ[μ]
        fourBlockDirection μ A B C D α β := by
  let a := normalizedBlockL2 μ A hA
  let b := normalizedBlockL2 μ B hB
  let j := normalizedBlockL2 μ C hC
  let k := normalizedBlockL2 μ D hD
  filter_upwards [Lp.coeFn_add (β • (a - j)) (α • (k - b)),
    Lp.coeFn_smul β (a - j), Lp.coeFn_smul α (k - b), Lp.coeFn_sub a j,
    Lp.coeFn_sub k b, normalizedBlockL2_coe μ A hA, normalizedBlockL2_coe μ B hB,
    normalizedBlockL2_coe μ C hC, normalizedBlockL2_coe μ D hD]
      with z hsum hs₁ hs₂ hsub₁ hsub₂ ha hb hj hk
  change (β • (a - j) + α • (k - b) : Lp ℝ 2 μ) z = _
  rw [hsum, Pi.add_apply, hs₁, hs₂, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
    smul_eq_mul, hsub₁, hsub₂, Pi.sub_apply, Pi.sub_apply]
  change β * (a z - j z) + α * (k z - b z) = _
  rw [show a z = normalizedBlock μ A z from ha,
    show b z = normalizedBlock μ B z from hb,
    show j z = normalizedBlock μ C z from hj,
    show k z = normalizedBlock μ D z from hk]
  rfl

theorem fourBlockDirection_endpoint {μ : Measure Ω} [IsFiniteMeasure μ]
    {A B C D : Set Ω} (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hB0 : μ B ≠ 0) (hC0 : μ C ≠ 0)
    (hCA : Disjoint C A) (hCB : Disjoint C B) (hCD : Disjoint C D)
    (hBA : Disjoint B A) (hBD : Disjoint B D)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∃ t : ℝ, 0 < t ∧ (∀ z, 0 ≤ perturbationWeight t (fourBlockDirection μ A B C D α β) z) ∧
      (perturbedMeasure μ (fourBlockDirection μ A B C D α β) t C = 0 ∨
        perturbedMeasure μ (fourBlockDirection μ A B C D α β) t B = 0) := by
  have hCm : 0 < μ.real C := ENNReal.toReal_pos hC0 (measure_ne_top μ C)
  have hBm : 0 < μ.real B := ENNReal.toReal_pos hB0 (measure_ne_top μ B)
  apply exists_positive_flat_endpoint hC hB
    (mul_pos hβ (inv_pos.mpr hCm)) (mul_pos hα (inv_pos.mpr hBm))
  · intro z hz
    have hzA : z ∉ A := fun h => Set.disjoint_left.mp hCA hz h
    have hzB : z ∉ B := fun h => Set.disjoint_left.mp hCB hz h
    have hzD : z ∉ D := fun h => Set.disjoint_left.mp hCD hz h
    simp [fourBlockDirection, normalizedBlock, hz, hzA, hzB, hzD]
  · intro z hz
    have hzA : z ∉ A := fun h => Set.disjoint_left.mp hBA hz h
    have hzC : z ∉ C := fun h => Set.disjoint_left.mp hCB h hz
    have hzD : z ∉ D := fun h => Set.disjoint_left.mp hBD hz h
    simp [fourBlockDirection, normalizedBlock, hz, hzA, hzC, hzD]
  · intro z hz
    have hzC : z ∉ C := fun h => hz (Or.inl h)
    have hzB : z ∉ B := fun h => hz (Or.inr h)
    have he : fourBlockDirection μ A B C D α β z =
        β * normalizedBlock μ A z + α * normalizedBlock μ D z := by
      simp [fourBlockDirection, normalizedBlock, hzC, hzB]
    rw [he]
    exact add_nonneg (mul_nonneg hβ.le (normalizedBlock_nonneg μ A z))
      (mul_nonneg hα.le (normalizedBlock_nonneg μ D z))

/-- The exact invariants retained throughout uncrossing. -/
structure UncrossingInvariant (r : ℕ) (W : Kernel Ω) (c : Ω → ℝ)
    (x L θ : ℝ) (μ : Measure Ω) : Prop where
  probability : IsProbabilityMeasure μ
  cover : IsKernelCover r W μ c
  cost : (∫ z, c z ∂μ) = x
  extremal : density μ W = Phi r x
  degree : ∀ᵐ z ∂μ, kernelDegree W μ z = 1 - L + θ * c z

namespace ZeroTwinData

variable {W : Kernel Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {r : ℕ} {c : Ω → ℝ}

/-- Every actual crossing of active twins has an actual positive endpoint
with all extremal data preserved and one positive set killed. -/
theorem exists_crossing_endpoint (P : ZeroTwinData W μ c I) (hr : 2 ≤ r)
    {x L θ : ℝ} (hx0 : x ≠ 0) (hx1 : x ≤ 1 / (r : ℝ))
    (hc : IsKernelCover r W μ c) (hcx : (∫ z, c z ∂μ) = x)
    (he : density μ W = Phi r x)
    (hd : ∀ᵐ z ∂μ, kernelDegree W μ z = 1 - L + θ * c z)
    {i j : I} (hi : μ (P.block i) ≠ 0) (hj : μ (P.block j) ≠ 0)
    (hij : μ (P.defect i \ P.defect j) ≠ 0)
    (hji : μ (P.defect j \ P.defect i) ≠ 0) :
    ∃ ν : Measure Ω, ν ≪ μ ∧ UncrossingInvariant r W c x L θ ν ∧
      (ν (P.block i) = 0 ∨ ν (P.defect j \ P.defect i) = 0) := by
  let A := P.defect i \ P.defect j
  let B := P.defect j \ P.defect i
  let C := P.block i
  let D := P.block j
  have hA : MeasurableSet A := (P.measurable_defect i).diff (P.measurable_defect j)
  have hB : MeasurableSet B := (P.measurable_defect j).diff (P.measurable_defect i)
  have hC : MeasurableSet C := P.measurable_block i
  have hD : MeasurableSet D := P.measurable_block j
  have hne : i ≠ j := by
    intro heq
    exact hij (by simp [heq])
  have hCA : Disjoint C A := (P.block_defect_disjoint i i).mono_right Set.diff_subset
  have hCB : Disjoint C B := (P.block_defect_disjoint i j).mono_right Set.diff_subset
  have hCD : Disjoint C D := P.disjoint hne
  have hBA : Disjoint B A := Set.disjoint_left.mpr fun z hzB hzA => hzB.2 hzA.1
  have hBD : Disjoint B D := (P.block_defect_disjoint j j).symm.mono_left Set.diff_subset
  have hWCA : ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ C → z.2 ∈ A → W z.1 z.2 = 0 := by
    filter_upwards [P.defect_anticomplete i] with z hz hzC hzA
    exact hz hzC hzA.1
  have hWCB : ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ C → z.2 ∈ B → W z.1 z.2 = 1 := by
    filter_upwards [P.outside_complete i] with z hz hzC hzB
    apply hz hzC
    rintro (hzCi | hzDi)
    · exact Set.disjoint_left.mp (P.block_defect_disjoint i j) hzCi hzB.1
    · exact hzB.2 hzDi
  have hWDA : ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ D → z.2 ∈ A → W z.1 z.2 = 1 := by
    filter_upwards [P.outside_complete j] with z hz hzD hzA
    apply hz hzD
    rintro (hzCj | hzDj)
    · exact Set.disjoint_left.mp (P.block_defect_disjoint j i) hzCj hzA.1
    · exact hzA.2 hzDj
  have hWDB : ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ D → z.2 ∈ B → W z.1 z.2 = 0 := by
    filter_upwards [P.defect_anticomplete j] with z hz hzD hzB
    exact hz hzD hzB.1
  let a := normalizedBlockL2 μ A hA
  let b := normalizedBlockL2 μ B hB
  let j₀ := normalizedBlockL2 μ C hC
  let k₀ := normalizedBlockL2 μ D hD
  let α := ∫ z, c z * a z ∂μ
  let β := ∫ z, c z * b z ∂μ
  let f : Lp ℝ 2 μ := β • (a - j₀) + α • (k₀ - b)
  let h := fourBlockDirection μ A B C D α β
  have hflat := four_block_flat_direction W μ hc hx0 hcx hd
    (kernel_tangent_nonpositive_of_extremal hr W μ hc hx1 hcx he)
    hA hB hC hD hij hji hi hj
    (fun z hz => P.defect_pos i z hz.1) (fun z hz => P.defect_pos j z hz.1)
    (P.block_zero i) (P.block_zero j) hWCA hWCB hWDA hWDB
    (P.cross_complete i j hne) (P.independent i) (P.independent j)
  change 0 < α ∧ 0 < β ∧ f ∈ DensityHS.Analysis.boundedL2 μ ∧
    (∫ z, f z ∂μ) = 0 ∧ (∫ z, c z * f z ∂μ) = 0 ∧ kernelOperator W μ f = 0 at hflat
  obtain ⟨hα, hβ, _, hfmean, hfcost, hfzero⟩ := hflat
  have hfh : (f : Ω → ℝ) =ᵐ[μ] h := fourBlockDirection_coe μ hA hB hC hD α β
  have hhi : Integrable h μ := (l2_integrable μ f).congr hfh
  have hhmean : (∫ z, h z ∂μ) = 0 := (integral_congr_ae hfh).symm.trans hfmean
  have hhcost : (∫ z, c z * h z ∂μ) = 0 := by
    calc
      _ = ∫ z, c z * f z ∂μ := by
        apply integral_congr_ae
        filter_upwards [hfh] with z hz
        rw [hz]
      _ = 0 := hfcost
  have hpot : ∀ᵐ z ∂μ, kernelPotential W μ h z = 0 := by
    have hcoe := kernelOperator_coe W μ f
    rw [hfzero] at hcoe
    filter_upwards [hcoe, Lp.coeFn_zero ℝ 2 μ] with z hz hz0
    calc
      kernelPotential W μ h z = kernelPotential W μ f z := by
        apply integral_congr_ae
        filter_upwards [hfh] with y hy
        rw [hy]
      _ = 0 := hz.symm.trans hz0
  obtain ⟨t, _, hweight, hkill⟩ := fourBlockDirection_endpoint hB hC hji hi
    hCA hCB hCD hBA hBD hα hβ
  obtain ⟨hprob, hcover, hcost, hedensity, _⟩ :=
    flat_perturbation_preserves hc hhi hhmean hhcost hpot t hweight
  refine ⟨perturbedMeasure μ h t, perturbedMeasure_absolutelyContinuous μ h t,
    ⟨hprob, hcover, hcost.trans hcx, hedensity.trans he, ?_⟩, hkill⟩
  exact affine_degree_perturbedMeasure W hhi hpot hd t hweight

/-- Finite uncrossing of an actual extremizer.  The original kernel, cover,
parameter, density, and affine degree relation are retained; only the base
measure changes.  No local-move or tangent-inequality premise remains. -/
theorem exists_uncrossed_extremal [Fintype I] [DecidableEq I]
    (P : ZeroTwinData W μ c I) (hr : 2 ≤ r)
    {x L θ : ℝ} (hx0 : x ≠ 0) (hx1 : x ≤ 1 / (r : ℝ))
    (hc : IsKernelCover r W μ c) (hcx : (∫ z, c z ∂μ) = x)
    (he : density μ W = Phi r x)
    (hd : ∀ᵐ z ∂μ, kernelDegree W μ z = 1 - L + θ * c z) :
    ∃ ν : Measure Ω, ν ≪ μ ∧ UncrossingInvariant r W c x L θ ν ∧
      ActiveDefectsComparable ν P.block P.defect := by
  apply P.exists_uncrossed_measure (UncrossingInvariant r W c x L θ)
    ⟨inferInstance, hc, hcx, he, hd⟩
  intro ν hν hG i j hi hj hij hji
  letI := hG.probability
  let Pν := P.mono_measure hν
  exact Pν.exists_crossing_endpoint hr hx0 hx1 hG.cover hG.cost hG.extremal hG.degree
    hi hj hij hji

theorem exists_uncrossed_extremal_atomless [Fintype I] [DecidableEq I]
    [NullSingletonClass μ] (P : ZeroTwinData W μ c I) (hr : 2 ≤ r)
    {x L θ : ℝ} (hx0 : x ≠ 0) (hx1 : x ≤ 1 / (r : ℝ))
    (hc : IsKernelCover r W μ c) (hcx : (∫ z, c z ∂μ) = x)
    (he : density μ W = Phi r x)
    (hd : ∀ᵐ z ∂μ, kernelDegree W μ z = 1 - L + θ * c z) :
    ∃ ν : Measure Ω, ν ≪ μ ∧ NullSingletonClass ν ∧
      UncrossingInvariant r W c x L θ ν ∧ ActiveDefectsComparable ν P.block P.defect := by
  obtain ⟨ν, hν, hG, hcomp⟩ := P.exists_uncrossed_extremal hr hx0 hx1 hc hcx he hd
  exact ⟨ν, hν, ⟨fun z => hν (measure_singleton z)⟩, hG, hcomp⟩

end ZeroTwinData

end DensityHS.Graphon
