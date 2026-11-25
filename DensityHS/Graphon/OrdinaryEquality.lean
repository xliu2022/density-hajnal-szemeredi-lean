module

public import DensityHS.Graphon.OrdinaryClassification
public import DensityHS.Basic.LocalBranches

/-!
# Equality on a unique ordinary phase

Author and maintainer: Xizhi Liu.

The hypotheses of the unique-branch theorem are exactly extremality and
unique activity. The proof derives a minimum cover, its actual second variation,
the complementary cluster partition, and the balanced finite construction.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set Filter
open scoped ENNReal NNReal InnerProductSpace

universe u
variable {Ω : Type u} [MeasurableSpace Ω] [MetricSpace Ω]
  [SecondCountableTopology Ω] [BorelSpace Ω]

/-- The ordinary-family classification under the second-order sign already
implied by any ordinary branch identity, including at a transition. -/
theorem B_classification_of_complement_positive {r : ℕ} (hr : 3 ≤ r)
    (ν : Measure Ω) [SFinite ν] [IsLocallyFiniteMeasure ν] [IsUnifLocDoublingMeasure ν]
    {D : Set Ω} (hD : MeasurableSet D) [IsProbabilityMeasure (ν.restrict D)]
    (W : Kernel Ω) {x : ℝ} (hx : 0 < x) (hx1 : x < 1 / (r : ℝ))
    (htiling : tilingNumber r W (ν.restrict D) ≤ x)
    (he : density (ν.restrict D) W = Phi r x)
    (hpos : IsConditionallyPositive W.complement (ν.restrict D)) :
    ∃ q : ℕ, 1 ≤ q ∧ q < r ∧ Phi r x = B r q x ∧
      Nonempty (OrdinaryPartition r q x W (ν.restrict D)) := by
  have hcover : coverNumber r W (ν.restrict D) ≤ x := by
    simpa only [kernel_tiling_cover_duality r W (ν.restrict D) (by omega)] using htiling
  have hbin := extremal_zero_one_ae (by omega : 2 ≤ r) (ν.restrict D) W
    ⟨hx.le, hx1.le⟩ hcover he
  obtain ⟨P⟩ := conditionallyPositive_cluster_measurable ν hD W.complement
    (complement_binary W (ν.restrict D) hbin) hpos
  exact ordinary_classification_of_cluster hr P hx hx1 htiling he

/-- Full classification when an ordinary branch is the unique active
construction. No variational or structural conclusion is assumed. -/
theorem B_classification_unique {r i : ℕ} (hr : 3 ≤ r)
    (ν : Measure Ω) [SFinite ν] [IsLocallyFiniteMeasure ν] [IsUnifLocDoublingMeasure ν]
    {D : Set Ω} (hD : MeasurableSet D) [IsProbabilityMeasure (ν.restrict D)]
    (W : Kernel Ω) {x : ℝ} (hx : x ∈ Icc 0 (1 / (r : ℝ)))
    (hunique : UniqueBActive r i x)
    (htiling : tilingNumber r W (ν.restrict D) ≤ x)
    (he : density (ν.restrict D) W = Phi r x) :
    Nonempty (OrdinaryPartition r i x W (ν.restrict D)) := by
  obtain ⟨hx0, hx1⟩ := hunique.interior hr hx
  have hcover : coverNumber r W (ν.restrict D) ≤ x := by
    simpa only [kernel_tiling_cover_duality r W (ν.restrict D) (by omega)] using htiling
  have hnum := extremal_coverNumber_eq (by omega : 2 ≤ r) (ν.restrict D) W hx hcover he
  obtain ⟨c, hc, hmin⟩ := exists_minimum_kernel_cover r W (ν.restrict D) (by omega)
  have hcx : (∫ z, c z ∂ν.restrict D) = x := hmin.trans hnum
  have hpos := B_complement_conditionallyPositive (by omega : 2 ≤ r) hunique.index_lt
    W (ν.restrict D) hc hx0 hx1 hcx he (B_local_majorant (hunique.eventually_eq hr))
  obtain ⟨q, hq, hqr, hactive, hmodel⟩ :=
    B_classification_of_complement_positive hr ν hD W hx0 hx1 htiling he hpos
  have hqi : q = i := by
    by_contra hne
    have hlt := hunique.B_lt q hq hqr hne
    rw [hactive] at hlt
    exact (lt_irrefl _) hlt
  simpa only [hqi] using hmodel

/-- The same full classification on an arbitrary normalized measurable
region, matching the conditional measures used in recursive equality proofs. -/
theorem B_classification_unique_cond {r i : ℕ} (hr : 3 ≤ r)
    (ν : Measure Ω) [SFinite ν] [IsLocallyFiniteMeasure ν] [IsUnifLocDoublingMeasure ν]
    {D : Set Ω} (hD : MeasurableSet D) (hD0 : ν D ≠ 0) (hDtop : ν D ≠ ∞)
    (W : Kernel Ω) {x : ℝ} (hx : x ∈ Icc 0 (1 / (r : ℝ)))
    (hunique : UniqueBActive r i x)
    (htiling : tilingNumber r W (ProbabilityTheory.cond ν D) ≤ x)
    (he : density (ProbabilityTheory.cond ν D) W = Phi r x) :
    Nonempty (OrdinaryPartition r i x W (ProbabilityTheory.cond ν D)) := by
  let c : ℝ≥0 := (ν D).toNNReal⁻¹
  let ν' : Measure Ω := c • ν
  have hc : (c : ℝ≥0∞) = (ν D)⁻¹ := by
    dsimp [c]
    rw [← ENNReal.toNNReal_inv, ENNReal.coe_toNNReal (ENNReal.inv_ne_top.mpr hD0)]
  have hmeasure : ν'.restrict D = ProbabilityTheory.cond ν D := by
    change ((c : ℝ≥0∞) • ν).restrict D = _
    rw [hc, Measure.restrict_smul]
    rfl
  letI : IsUnifLocDoublingMeasure ν' := isUnifLocDoublingMeasure_nnreal_smul ν c
  letI : IsProbabilityMeasure (ProbabilityTheory.cond ν D) :=
    ProbabilityTheory.cond_isProbabilityMeasure_of_finite hD0 hDtop
  letI : IsProbabilityMeasure (ν'.restrict D) := by rw [hmeasure]; infer_instance
  have htiling' : tilingNumber r W (ν'.restrict D) ≤ x := by simpa only [hmeasure] using htiling
  have he' : density (ν'.restrict D) W = Phi r x := by simpa only [hmeasure] using he
  have h := B_classification_unique hr ν' hD W hx hunique htiling' he'
  simpa only [hmeasure] using h

end DensityHS.Graphon
