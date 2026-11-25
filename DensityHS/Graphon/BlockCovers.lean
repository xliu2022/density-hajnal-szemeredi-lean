module

public import DensityHS.Graphon.Duality
public import DensityHS.Graphon.SamplingCover
public import DensityHS.Weighted.Hypersimplex
public import Mathlib.Probability.ConditionalProbability

/-!
# Covers averaged over complete measurable blocks

Author and maintainer: Xizhi Liu.

Independent samples from absolutely continuous block distributions turn an
actual kernel cover into a finite complete-support cover.  This includes
repeated copies of a clique remainder: the block distributions need not have
disjoint supports.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Absolute continuity of a finite product, allowing a different measure at
each coordinate. -/
theorem absolutelyContinuous_finPi_family (μ : Measure Ω) [IsFiniteMeasure μ]
    (n : ℕ) (ν : Fin n → Measure Ω) [∀ i, IsFiniteMeasure (ν i)]
    (hν : ∀ i, ν i ≪ μ) : Measure.pi ν ≪ Measure.pi (fun _ : Fin n => μ) := by
  induction n with
  | zero => rw [Measure.pi_of_empty, Measure.pi_of_empty]
  | succ n ih =>
    let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Ω) 0).symm
    have hn := (measurePreserving_piFinSuccAbove ν 0).symm
    have hm := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
    rw [← hn.map_eq, ← hm.map_eq]
    exact e.measurableEmbedding.absolutelyContinuous_map
      ((hν 0).prod (ih (fun i => ν (Fin.succAbove 0 i)) (fun i => hν _)))

/-- Two different coordinates of a product have the corresponding pair of
marginal distributions. -/
theorem measurePreserving_pair_coordinates {I : Type*} [Fintype I]
    (ν : I → Measure Ω) [∀ i, IsProbabilityMeasure (ν i)] {i j : I} (hij : i ≠ j) :
    MeasurePreserving (fun z : I → Ω => (z i, z j)) (Measure.pi ν) ((ν i).prod (ν j)) := by
  have hind : iIndepFun (fun i (z : I → Ω) => z i) (Measure.pi ν) :=
    iIndepFun_pi (X := fun _ : I => id) (fun _ => aemeasurable_id)
  refine ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j), ?_⟩
  rw [IndepFun.map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
    (measurable_pi_apply j).aemeasurable (hind.indepFun hij),
    (measurePreserving_eval ν i).map_eq, (measurePreserving_eval ν j).map_eq]

/-- Averaging any feasible kernel cover over pairwise complete probability
blocks gives an actual finite cover of the complete support. -/
theorem IsKernelCover.average_complete {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {c : Ω → ℝ} (hc : IsKernelCover r W μ c)
    {I : Type*} [Fintype I] (ν : I → Measure Ω) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, ν i ≪ μ)
    (hcross : ∀ i j, i ≠ j → ∀ᵐ z : Ω × Ω ∂(ν i).prod (ν j), 0 < W z.1 z.2) :
    IsCliqueCover r (⊤ : SimpleGraph I) (fun i => ∫ z, c z ∂ν i) := by
  classical
  refine ⟨fun i => MeasureTheory.integral_nonneg hc.nonneg, ?_⟩
  intro K hK
  let eK : Fin r ≃ K := (K.equivFinOfCardEq hK.card_eq).symm
  let e : Fin r ↪ I := ⟨fun i => (eK i).1, fun i j h => eK.injective (Subtype.ext h)⟩
  let η : Fin r → Measure Ω := fun i => ν (e i)
  have hcover : ∀ᵐ t : Fin r → Ω ∂Measure.pi η,
      (∀ i j, i ≠ j → 0 < W (t i) (t j)) → 1 ≤ ∑ i, c (t i) :=
    hc.2.2.filter_mono (absolutelyContinuous_finPi_family μ r η (fun i => hν _)).ae_le
  have hclique : ∀ᵐ t : Fin r → Ω ∂Measure.pi η,
      ∀ i j, i ≠ j → 0 < W (t i) (t j) := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ h => False.elim (h hij)
    exact ((measurePreserving_pair_coordinates η hij).quasiMeasurePreserving.ae
      (hcross (e i) (e j) (fun h => hij (e.injective h)))).mono fun _ h _ => h
  have hsum : ∀ᵐ t : Fin r → Ω ∂Measure.pi η, 1 ≤ ∑ i, c (t i) := by
    filter_upwards [hcover, hclique] with t ht htc
    exact ht htc
  have hci : ∀ i : Fin r, Integrable (fun t : Fin r → Ω => c (t i)) (Measure.pi η) :=
    fun i => integrable_of_unitInterval (hc.measurable.comp (measurable_pi_apply i))
      (fun _ => hc.nonneg _) (fun _ => hc.le_one _)
  have hint := integral_mono_ae (integrable_const (1 : ℝ))
    (integrable_finsetSum _ (fun i _ => hci i)) hsum
  rw [integral_finsetSum _ (fun i _ => hci i)] at hint
  have heval : ∀ i : Fin r,
      (∫ t : Fin r → Ω, c (t i) ∂Measure.pi η) = ∫ z, c z ∂ν (e i) := by
    intro i
    change (∫ t : Fin r → Ω, c (t i) ∂Measure.pi η) = ∫ z, c z ∂η i
    rw [← (measurePreserving_eval η i).map_eq]
    exact (integral_map (measurable_pi_apply i).aemeasurable
      hc.measurable.aestronglyMeasurable).symm
  have hint' : 1 ≤ ∑ i : Fin r, ∫ z, c z ∂ν (e i) := by simpa only [heval, integral_const, probReal_univ, smul_eq_mul, one_mul] using hint
  convert hint' using 1
  exact ((eK.sum_comp (fun v : K => ∫ z, c z ∂ν v)).trans
    (Finset.sum_coe_sort K (fun v => ∫ z, c z ∂ν v))).symm

/-- A finite complete collection of block distributions, with no more than
the original total cover cost, gives a graphon tiling-number lower bound. -/
theorem tilingNumber_ge_of_complete_block_distributions {r : ℕ} (hr : 0 < r)
    (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {I : Type*} [Fintype I] [DecidableEq I]
    (ν : I → Measure Ω) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, ν i ≪ μ)
    (hcross : ∀ i j, i ≠ j → ∀ᵐ z : Ω × Ω ∂(ν i).prod (ν j), 0 < W z.1 z.2)
    (p : I → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hcost : ∀ c : Ω → ℝ, IsKernelCover r W μ c →
      (∑ i, p i * ∫ z, c z ∂ν i) ≤ ∫ z, c z ∂μ)
    {q : ℝ} (hq : 0 ≤ q) (hcap : (r : ℝ) * q ≤ cappedMass p q) :
    q ≤ tilingNumber r W μ := by
  rw [kernel_tiling_cover_duality r W μ hr]
  apply le_csInf (kernelCoverCosts_nonempty r W μ hr)
  rintro x ⟨c, hc, rfl⟩
  exact (complete_cover_bound_of_cappedMass hr hp hq hcap
    (hc.average_complete ν hν hcross)).trans (hcost c hc)

/-- Conditional block averages are normalized set integrals. -/
theorem integral_cond_eq_normalized (μ : Measure Ω) (S : Set Ω) (c : Ω → ℝ) :
    (∫ z, c z ∂ProbabilityTheory.cond μ S) = (μ.real S)⁻¹ * ∫ z in S, c z ∂μ := by
  rw [ProbabilityTheory.cond, integral_smul_measure]
  simp only [ENNReal.toReal_inv, Measure.real, smul_eq_mul]

/-- Cross-completeness passes to the actual conditional distributions. -/
theorem cross_positive_cond (W : Kernel Ω) (μ : Measure Ω) [IsFiniteMeasure μ]
    {S T : Set Ω} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hcross : ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ S → z.2 ∈ T → 0 < W z.1 z.2) :
    ∀ᵐ z : Ω × Ω ∂(ProbabilityTheory.cond μ S).prod (ProbabilityTheory.cond μ T),
      0 < W z.1 z.2 := by
  have hac := (ProbabilityTheory.cond_absolutelyContinuous (μ := μ) (s := S)).prod
    (ProbabilityTheory.cond_absolutelyContinuous (μ := μ) (s := T))
  have hmemS : ∀ᵐ x ∂ProbabilityTheory.cond μ S, x ∈ S :=
    ProbabilityTheory.ae_cond_of_forall_mem hS (fun _ hx => hx)
  have hmemT : ∀ᵐ x ∂ProbabilityTheory.cond μ T, x ∈ T :=
    ProbabilityTheory.ae_cond_of_forall_mem hT (fun _ hx => hx)
  filter_upwards [hcross.filter_mono hac.ae_le,
    Measure.quasiMeasurePreserving_fst.ae hmemS,
    Measure.quasiMeasurePreserving_snd.ae hmemT] with z hz hzS hzT
  exact hz hzS hzT

/-- A kernel cover cannot vanish on `r` pairwise complete probability
blocks. The blocks may even be repeated if they are themselves cliques. -/
theorem IsKernelCover.not_zero_complete_distributions {r : ℕ} {W : Kernel Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {c : Ω → ℝ} (hc : IsKernelCover r W μ c)
    (ν : Fin r → Measure Ω) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, ν i ≪ μ)
    (hcross : ∀ i j, i ≠ j → ∀ᵐ z : Ω × Ω ∂(ν i).prod (ν j), 0 < W z.1 z.2)
    (hzero : ∀ i, (∫ z, c z ∂ν i) = 0) : False := by
  classical
  have h := (hc.average_complete ν hν hcross).2 Finset.univ
    ⟨by intro i _ j _ hij; exact hij, by simp⟩
  simp only [hzero, Finset.sum_const_zero] at h
  norm_num at h

/-- The concrete measurable-set form of the zero-cover clique obstruction. -/
theorem IsKernelCover.not_zero_complete_blocks {r : ℕ} {W : Kernel Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {c : Ω → ℝ} (hc : IsKernelCover r W μ c)
    (S : Fin r → Set Ω) (hS : ∀ i, MeasurableSet (S i)) (hpos : ∀ i, μ (S i) ≠ 0)
    (hcross : ∀ i j, i ≠ j → ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      z.1 ∈ S i → z.2 ∈ S j → 0 < W z.1 z.2)
    (hzero : ∀ i, ∀ᵐ z ∂μ, z ∈ S i → c z = 0) : False := by
  let ν : Fin r → Measure Ω := fun i => ProbabilityTheory.cond μ (S i)
  letI : ∀ i, IsProbabilityMeasure (ν i) := fun i =>
    ProbabilityTheory.cond_isProbabilityMeasure_of_finite (hpos i) (measure_ne_top μ _)
  apply hc.not_zero_complete_distributions ν (fun _ => ProbabilityTheory.cond_absolutelyContinuous)
    (fun i j hij => cross_positive_cond W μ (hS i) (hS j) (hcross i j hij))
  intro i
  apply integral_eq_zero_of_ae
  have hmem : ∀ᵐ z ∂ν i, z ∈ S i :=
    ProbabilityTheory.ae_cond_of_forall_mem (hS i) (fun _ hx => hx)
  filter_upwards [(hzero i).filter_mono
    (ProbabilityTheory.cond_absolutelyContinuous (μ := μ) (s := S i)).ae_le, hmem]
    with z hz hm
  exact hz hm

end DensityHS.Graphon
