module

public import DensityHS.Graphon.ZeroTwins
public import DensityHS.Graphon.NestedPeeling

/-!
# Complete reduction of a strict transition multiplier

Author and maintainer: Xizhi Liu.

Starting with an actual extremal kernel and its affine degree identity,
this file constructs a finite zero-cover twin system, performs the actual
finite measure uncrossing, and selects its smallest positive-class defect.
The resulting scalar recursion and cover-cost bounds contain no assumed
structural classification or perturbation certificate.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter TopologicalSpace
open scoped ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω]

theorem extremal_zero_mass_lower {r : ℕ} (hr : 2 ≤ r) (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {c : Ω → ℝ} (hc : IsKernelCover r W μ c)
    {x : ℝ} (hx : x ∈ Icc 0 (1 / (r : ℝ))) (hcx : (∫ z, c z ∂μ) = x)
    (he : density μ W = Phi r x) : 1 - (r : ℝ) * x ≤ μ.real {z | c z = 0} := by
  have hnum := extremal_coverNumber_eq hr μ W hx
    (by rw [← hcx]; exact coverNumber_le_cost hc) he
  have hmin : (∫ z, c z ∂μ) = coverNumber r W μ := hcx.trans hnum.symm
  have hbound := minimum_cover_support_measure_bound (by omega : 0 < r) hc hmin
  have hZ : {z | c z = 0} = {z | 0 < c z}ᶜ := by
    ext z
    simp only [mem_setOf_eq, mem_compl_iff, not_lt]
    exact ⟨fun hz => hz.le, fun hz => le_antisymm hz (hc.nonneg z)⟩
  rw [hZ, measureReal_compl (measurableSet_lt measurable_const hc.measurable), probReal_univ]
  rw [hcx] at hbound
  linarith

structure UncrossedPeelingWitness (r : ℕ) (W : Kernel Ω) (c : Ω → ℝ) (x L θ : ℝ) where
  measure : Measure Ω
  invariant : UncrossingInvariant r W c x L θ measure
  count : ℕ
  count_lt : count < r
  twins : ZeroTwinData W measure c (Fin count)
  index : Fin count
  positive : measure (twins.block index) ≠ 0
  minimum : ∀ j, measure (twins.block j) ≠ 0 → twins.defect index ≤ᵐ[measure] twins.defect j

namespace UncrossedPeelingWitness

variable {r : ℕ} {W : Kernel Ω} {c : Ω → ℝ} {x L θ : ℝ}

/-- Integrating the actual affine degree identity determines its constant
term from the extremal density and the cover cost. -/
theorem peel_parameter (T : UncrossedPeelingWitness r W c x L θ) :
    L = 1 - 2 * Phi r x + θ * x := by
  letI := T.invariant.probability
  have hi := integral_congr_ae T.invariant.degree
  rw [integral_kernelDegree, T.invariant.extremal,
    integral_add (integrable_const _) (T.invariant.cover.integrable.const_mul θ),
    integral_const_mul, T.invariant.cost] at hi
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hi
  linarith

noncomputable def defectCost (T : UncrossedPeelingWitness r W c x L θ) : ℝ :=
  ∫ z in T.twins.defect T.index, c z ∂T.measure

noncomputable def defectMass (T : UncrossedPeelingWitness r W c x L θ) : ℝ :=
  T.measure.real (T.twins.defect T.index)

noncomputable def zeroMass (T : UncrossedPeelingWitness r W c x L θ) : ℝ :=
  T.measure.real {z | c z = 0}

theorem zeroMass_lower (T : UncrossedPeelingWitness r W c x L θ)
    (hr : 2 ≤ r) (hx : x ∈ Icc 0 (1 / (r : ℝ))) : 1 - (r : ℝ) * x ≤ T.zeroMass := by
  letI := T.invariant.probability
  exact extremal_zero_mass_lower hr W T.measure T.invariant.cover hx T.invariant.cost T.invariant.extremal

theorem defectCost_range (T : UncrossedPeelingWitness r W c x L θ) : T.defectCost ∈ Icc 0 x := by
  letI := T.invariant.probability
  exact T.twins.defect_cost_range T.invariant.cover T.invariant.cost T.index

theorem defectMass_range (T : UncrossedPeelingWitness r W c x L θ) : T.defectMass ∈ Icc 0 L := by
  letI := T.invariant.probability
  have hm := T.twins.mass_eq T.invariant.degree T.index T.positive
  have hp : 0 ≤ T.measure.real (T.twins.block T.index) := measureReal_nonneg
  exact ⟨measureReal_nonneg, by dsimp [defectMass]; linarith⟩

theorem defectCost_bound (T : UncrossedPeelingWitness r W c x L θ) :
    θ * T.defectCost ≤ T.defectMass * (L - T.zeroMass) := by
  letI := T.invariant.probability
  exact T.twins.minimal_defect_cost_bound T.invariant.cover T.invariant.degree T.index T.minimum

theorem defectCost_cap (T : UncrossedPeelingWitness r W c x L θ)
    (hθ : 0 < θ) {ell : ℝ} (hell : ell ≤ T.zeroMass) (hL : ell ≤ L) :
    T.defectCost ≤ L * (L - ell) / θ := by
  apply (le_div_iff₀ hθ).mpr
  have h1 : T.defectMass * (L - T.zeroMass) ≤ T.defectMass * (L - ell) :=
    mul_le_mul_of_nonneg_left (by linarith) T.defectMass_range.1
  have h2 : T.defectMass * (L - ell) ≤ L * (L - ell) :=
    mul_le_mul_of_nonneg_right T.defectMass_range.2 (sub_nonneg.mpr hL)
  nlinarith [T.defectCost_bound]

theorem defectCost_eq_zero_of_zeroMass_gt (T : UncrossedPeelingWitness r W c x L θ)
    (hθ : 0 < θ) (hL : L < T.zeroMass) : T.defectCost = 0 := by
  have hnon : T.defectMass * (L - T.zeroMass) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos T.defectMass_range.1 (by linarith)
  have ha := T.defectCost_range.1
  nlinarith [T.defectCost_bound]

theorem recursion (T : UncrossedPeelingWitness r W c x L θ) (hr : 3 ≤ r)
    (hL1 : L < 1) (hLx : L ≤ 1 - ((r - 1 : ℕ) : ℝ) * x) :
    Phi r x ≤ L * (1 - L) + (1 - L)^2 * Phi (r - 1) ((x - T.defectCost) / (1 - L)) +
      θ * T.defectCost / 2 := by
  letI := T.invariant.probability
  have h := T.twins.peeling_recursion hr T.invariant.cover T.invariant.cost T.invariant.degree
    hL1 hLx T.index T.positive
  rwa [T.invariant.extremal] at h

theorem universal_peel (T : UncrossedPeelingWitness r W c x L θ) (hr : 3 ≤ r)
    (hθ : 0 < θ) (hL1 : L < 1) (hLx : L ≤ 1 - ((r - 1 : ℕ) : ℝ) * x)
    (hL : L < T.zeroMass) :
    Phi r x ≤ L * (1 - L) + (1 - L)^2 * Phi (r - 1) (x / (1 - L)) := by
  have h := T.recursion hr hL1 hLx
  simpa only [T.defectCost_eq_zero_of_zeroMass_gt hθ hL, sub_zero, mul_zero, zero_div,
    add_zero] using h

end UncrossedPeelingWitness

section Ambient

variable [MetricSpace Ω] [SecondCountableTopology Ω] [BorelSpace Ω]
    (ν : Measure Ω) [SFinite ν] [IsLocallyFiniteMeasure ν] [IsUnifLocDoublingMeasure ν]

theorem exists_uncrossedPeelingWitness (W : Kernel Ω) {E : Set Ω}
    (hE : MeasurableSet E) (hE0 : ν E ≠ 0) (hEtop : ν E ≠ ∞)
    {r : ℕ} (hr : 3 ≤ r) {c : Ω → ℝ} (hc : IsKernelCover r W (cond ν E) c)
    {x L θ : ℝ} (hx0 : 0 < x) (hx1 : x < 1 / (r : ℝ))
    (hcx : (∫ z, c z ∂cond ν E) = x) (he : density (cond ν E) W = Phi r x)
    (hd : ∀ᵐ z ∂cond ν E, kernelDegree W (cond ν E) z = 1 - L + θ * c z) :
    Nonempty (UncrossedPeelingWitness r W c x L θ) := by
  classical
  let μ := cond ν E
  letI : IsProbabilityMeasure μ := cond_isProbabilityMeasure_of_finite hE0 hEtop
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have hrp : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hell : 0 < 1 - (r : ℝ) * x := by
    have h := (lt_div_iff₀ hrp).mp hx1
    nlinarith
  have hZp : 0 < μ.real {z | c z = 0} := hell.trans_le
    (extremal_zero_mass_lower (by omega) W μ hc ⟨hx0.le, hx1.le⟩ hcx he)
  have hZ0 : μ {z | c z = 0} ≠ 0 := by
    intro hz
    have he : μ.real {z | c z = 0} = 0 := by simp [measureReal_def, hz]
    linarith
  have hcover : coverNumber r W μ ≤ x := by rw [← hcx]; exact coverNumber_le_cost hc
  have hbin := extremal_zero_one_ae (by omega : 2 ≤ r) μ W ⟨hx0.le, hx1.le⟩ hcover he
  have hq := kernel_tangent_nonpositive_of_extremal (by omega : 2 ≤ r) W μ hc hx1.le hcx he
  obtain ⟨n, hn, P, _⟩ := exists_zeroTwinData ν W hE hE0 hEtop hc hx0.ne' hcx hd hq hbin hZ0
  obtain ⟨μ', hμ', hG, hcomp⟩ := P.exists_uncrossed_extremal (by omega : 2 ≤ r)
    hx0.ne' hx1.le hc hcx he hd
  letI := hG.probability
  let P' := P.mono_measure hμ'
  have hZp' : 0 < μ'.real {z | c z = 0} := hell.trans_le
    (extremal_zero_mass_lower (by omega) W μ' hG.cover ⟨hx0.le, hx1.le⟩ hG.cost hG.extremal)
  have hZ0' : μ' {z | c z = 0} ≠ 0 := by
    intro hz
    have he : μ'.real {z | c z = 0} = 0 := by simp [measureReal_def, hz]
    linarith
  obtain ⟨i, hi, hmin⟩ := hcomp.exists_minimal P'.measurable_defect (P'.activeClasses_nonempty hZ0')
  exact ⟨{
    measure := μ'
    invariant := hG
    count := n
    count_lt := hn
    twins := P'
    index := i
    positive := hi
    minimum := hmin
  }⟩

end Ambient

end DensityHS.Graphon
