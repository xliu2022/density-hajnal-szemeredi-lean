module

public import DensityHS.Graphon.Sampling
public import DensityHS.Weighted.Main
public import DensityHS.Basic.EnvelopeStrict
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Clique supersaturation from finite sampling and the weighted Turán bound

Sampling a fixed number of vertices converts the zero-cover density theorem
into an explicit lower bound for the number of labelled cliques.  Repeated
sampled vertices cause no problem: an actual clique cannot use a repeated
vertex because the original graph has no loops.

Formalization author and maintainer: Xizhi Liu.
-/

@[expose] public section

open Finset MeasureTheory
open scoped BigOperators ENNReal

namespace DensityHS

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]

noncomputable def finiteGraphKernel (G : SimpleGraph V) : Graphon.Kernel V where
  toFun x y := if G.Adj x y then 1 else 0
  measurable_uncurry := measurable_of_countable _
  symmetric x y := by simp only [G.adj_comm]
  nonneg x y := by split_ifs <;> norm_num
  le_one x y := by split_ifs <;> norm_num

noncomputable def cliqueMapIndicator (r : ℕ) (G : SimpleGraph V) (f : Fin r → V) : ℝ :=
  if ∀ i j, i ≠ j → G.Adj (f i) (f j) then 1 else 0

theorem cliqueMapIndicator_nonneg (r : ℕ) (G : SimpleGraph V) (f : Fin r → V) :
    0 ≤ cliqueMapIndicator r G f := by unfold cliqueMapIndicator; split_ifs <;> norm_num

noncomputable def cliqueMapProbability (r : ℕ) (G : SimpleGraph V) (μ : Measure V) : ℝ :=
  ∫ f : Fin r → V, cliqueMapIndicator r G f ∂Graphon.sampleMeasure μ r

theorem cliqueMapProbability_nonneg (r : ℕ) (G : SimpleGraph V) (μ : Measure V) :
    0 ≤ cliqueMapProbability r G μ :=
  integral_nonneg (cliqueMapIndicator_nonneg r G)

theorem sample_density_le_zero_cover_plus_cliques {r s : ℕ}
    (hr : 2 ≤ r) (hs : 0 < s) (G : SimpleGraph V) (ω : Fin s → V) :
    Graphon.samplePairDensity s (finiteGraphKernel G) ω ≤ Phi r 0 +
      (∑ e : Fin r ↪ Fin s, cliqueMapIndicator r G (ω ∘ e)) / 2 := by
  classical
  have hPhi : 0 ≤ Phi r 0 := by
    rw [Phi_zero hr]
    have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
    exact div_nonneg (by linarith) (by linarith)
  have hsum0 : 0 ≤ ∑ e : Fin r ↪ Fin s, cliqueMapIndicator r G (ω ∘ e) :=
    sum_nonneg fun _ _ => cliqueMapIndicator_nonneg _ _ _
  by_cases hc : ∃ K : Finset (Fin s), (Graphon.sampleGraph (finiteGraphKernel G) s ω).IsNClique r K
  · obtain ⟨K, hK⟩ := hc
    let eK : Fin r ≃ K := (K.equivFinOfCardEq hK.card_eq).symm
    let e : Fin r ↪ Fin s :=
      ⟨fun i => (eK i).1, fun i j hij => eK.injective (Subtype.ext hij)⟩
    have he : cliqueMapIndicator r G (ω ∘ e) = 1 := by
      unfold cliqueMapIndicator
      apply if_pos
      intro i j hij
      have hh := (hK.isClique (eK i).2 (eK j).2
        (fun h => hij (e.injective h))).2
      change 0 < (if G.Adj (ω (e i)) (ω (e j)) then (1 : ℝ) else 0) at hh
      by_contra hnot
      change ¬G.Adj (ω (e i)) (ω (e j)) at hnot
      simp only [hnot, ite_false, lt_self_iff_false] at hh
    have hsum1 : (1 : ℝ) ≤ ∑ e : Fin r ↪ Fin s, cliqueMapIndicator r G (ω ∘ e) := by
      rw [← he]
      exact single_le_sum
        (fun e' (_ : e' ∈ (univ : Finset (Fin r ↪ Fin s))) =>
          cliqueMapIndicator_nonneg r G (ω ∘ e')) (mem_univ e)
    have hhalf := (Graphon.samplePairDensity_mem_Icc
      (fun x y => ⟨(finiteGraphKernel G).nonneg x y, (finiteGraphKernel G).le_one x y⟩)
      hs ω).2
    linarith
  · have hcover : IsCliqueCover r (Graphon.sampleGraph (finiteGraphKernel G) s ω)
        (fun _ => 0) := by
      refine ⟨fun _ => le_rfl, fun K hK => ?_⟩
      exact False.elim (hc ⟨K, hK⟩)
    have hed := weighted_clique_cover_bound hr (Graphon.probability_sampleWeight hs)
      hcover (by simp only [coverCost, mul_zero, sum_const_zero]; positivity)
    simp only [coverCost, mul_zero, sum_const_zero] at hed
    have hdom := Graphon.samplePairDensity_le_edgeMass (finiteGraphKernel G) s ω
    linarith

theorem sampling_clique_supersaturation {r s : ℕ} (hr : 2 ≤ r) (hs : 0 < s)
    (G : SimpleGraph V) (μ : Measure V) [IsProbabilityMeasure μ] :
    (1 - (s : ℝ)⁻¹) * Graphon.density μ (finiteGraphKernel G) ≤
      Phi r 0 + (s : ℝ) ^ r * cliqueMapProbability r G μ / 2 := by
  classical
  have heint (e : Fin r ↪ Fin s) :
      (∫ ω : Fin s → V, cliqueMapIndicator r G (ω ∘ e)
        ∂Graphon.sampleMeasure μ s) = cliqueMapProbability r G μ := by
    have hmp := Graphon.measurePreserving_coordinates μ e
    have hh := integral_map (μ := Graphon.sampleMeasure μ s) hmp.measurable.aemeasurable
      (measurable_of_countable (cliqueMapIndicator r G)).aestronglyMeasurable
    dsimp only [Graphon.sampleMeasure] at hh
    rw [hmp.map_eq] at hh
    exact hh.symm
  have hmean := integral_mono
    (Graphon.integrable_samplePairDensity (finiteGraphKernel G).measurable_uncurry
      (fun x y => ⟨(finiteGraphKernel G).nonneg x y, (finiteGraphKernel G).le_one x y⟩) hs)
    (Integrable.of_finite : Integrable
      (fun ω : Fin s → V => Phi r 0 +
        (∑ e : Fin r ↪ Fin s, cliqueMapIndicator r G (ω ∘ e)) / 2)
      (Graphon.sampleMeasure μ s))
    (sample_density_le_zero_cover_plus_cliques hr hs G)
  rw [Graphon.integral_samplePairDensity (finiteGraphKernel G).measurable_uncurry
    (fun x y => ⟨(finiteGraphKernel G).nonneg x y, (finiteGraphKernel G).le_one x y⟩) hs,
    ← Graphon.density_eq_prod_integral,
    integral_add (integrable_const _) Integrable.of_finite, integral_const,
    integral_div, integral_finsetSum univ (fun _ _ => Integrable.of_finite)] at hmean
  simp only [heint, sum_const, card_univ, nsmul_eq_mul, probReal_univ, smul_eq_mul,
    one_mul] at hmean
  have hcard : Fintype.card (Fin r ↪ Fin s) ≤ s ^ r := by
    calc
      Fintype.card (Fin r ↪ Fin s) ≤ Fintype.card (Fin r → Fin s) :=
        Fintype.card_le_of_injective (fun e : Fin r ↪ Fin s => (e : Fin r → Fin s))
          (fun e f h => Function.Embedding.ext (congrFun h))
      _ = s ^ r := by simp
  have hcR : (Fintype.card (Fin r ↪ Fin s) : ℝ) ≤ (s : ℝ) ^ r := by exact_mod_cast hcard
  have hn := cliqueMapProbability_nonneg r G μ
  nlinarith

omit [MeasurableSpace V] [MeasurableSingletonClass V] in
noncomputable def labelledCliqueMaps (r : ℕ) (G : SimpleGraph V) : Finset (Fin r → V) :=
  univ.filter fun f => ∀ i j, i ≠ j → G.Adj (f i) (f j)

omit [MeasurableSpace V] [MeasurableSingletonClass V] in
@[simp] theorem mem_labelledCliqueMaps {r : ℕ} {G : SimpleGraph V} {f : Fin r → V} :
    f ∈ labelledCliqueMaps r G ↔ ∀ i j, i ≠ j → G.Adj (f i) (f j) := by
  simp only [labelledCliqueMaps, mem_filter, mem_univ, true_and]

omit [MeasurableSpace V] [MeasurableSingletonClass V] in
theorem cliqueMap_injective {r : ℕ} {G : SimpleGraph V} {f : Fin r → V}
    (hf : ∀ i j, i ≠ j → G.Adj (f i) (f j)) : Function.Injective f := by
  intro i j hij
  by_contra hne
  exact (hf i j hne).ne hij

omit [MeasurableSpace V] [MeasurableSingletonClass V] in
theorem isNClique_image_of_pairwise_adj [DecidableEq V] {r : ℕ}
    {G : SimpleGraph V} {f : Fin r → V}
    (hf : ∀ i j, i ≠ j → G.Adj (f i) (f j)) : G.IsNClique r (univ.image f) := by
  refine ⟨?_, ?_⟩
  · intro u hu v hv huv
    obtain ⟨i, _, rfl⟩ := mem_image.mp hu
    obtain ⟨j, _, rfl⟩ := mem_image.mp hv
    exact hf i j (fun hij => huv (congrArg f hij))
  · rw [card_image_of_injective _ (cliqueMap_injective hf), card_univ, Fintype.card_fin]

theorem integral_uniform_fintype [Nonempty V] (f : V → ℝ) :
    ∫ x, f x ∂(PMF.uniformOfFintype V).toMeasure =
      (Fintype.card V : ℝ)⁻¹ * ∑ x, f x := by
  rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    smul_eq_mul, mul_sum]

theorem integral_uniform_product [Nonempty V] {I : Type*} [Fintype I] (f : (I → V) → ℝ) :
    ∫ x, f x ∂Measure.pi (fun _ : I => (PMF.uniformOfFintype V).toMeasure) =
      (Fintype.card V : ℝ)⁻¹ ^ Fintype.card I * ∑ x, f x := by
  classical
  rw [integral_fintype Integrable.of_finite]
  have hsingle (x : I → V) :
      (Measure.pi (fun _ : I => (PMF.uniformOfFintype V).toMeasure)).real {x} =
        (Fintype.card V : ℝ)⁻¹ ^ Fintype.card I := by
    simp only [measureReal_def, Measure.pi_singleton,
      PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _),
      PMF.uniformOfFintype_apply, prod_const, card_univ,
      ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  simp only [hsingle, smul_eq_mul, mul_sum]

theorem cliqueMapProbability_uniform [Nonempty V] (r : ℕ) (G : SimpleGraph V) :
    cliqueMapProbability r G (PMF.uniformOfFintype V).toMeasure =
      (Fintype.card V : ℝ)⁻¹ ^ r * (labelledCliqueMaps r G).card := by
  classical
  rw [cliqueMapProbability, Graphon.sampleMeasure, integral_uniform_product]
  simp only [Fintype.card_fin, cliqueMapIndicator, sum_boole, labelledCliqueMaps]
  apply congrArg (fun S : Finset (Fin r → V) => (Fintype.card V : ℝ)⁻¹ ^ r * (S.card : ℝ))
  ext f
  simp only [mem_filter, mem_univ, true_and]

theorem finiteGraphKernel_density_uniform [Nonempty V] (G : SimpleGraph V) :
    Graphon.density (PMF.uniformOfFintype V).toMeasure (finiteGraphKernel G) =
      edgeMass G (fun _ => 1 / (Fintype.card V : ℝ)) := by
  classical
  unfold Graphon.density
  rw [integral_uniform_fintype]
  simp_rw [integral_uniform_fintype]
  unfold edgeMass
  congr 1
  simp only [finiteGraphKernel, mul_sum]
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro y _
  by_cases hxy : G.Adj x y <;> simp [hxy]

omit [MeasurableSpace V] [MeasurableSingletonClass V] in
/-- An explicit labelled-clique lower bound above the Turán density.  The
sample size `s` depends only on the density margin, not on the graph order. -/
theorem finite_clique_supersaturation [Nonempty V] {r s : ℕ}
    (hr : 2 ≤ r) (hs : 0 < s) {δ : ℝ} (hδ : 0 < δ)
    (hsδ : (s : ℝ)⁻¹ ≤ δ) (G : SimpleGraph V)
    (hdensity : Phi r 0 + δ ≤ edgeMass G (fun _ => 1 / (Fintype.card V : ℝ))) :
    δ / (s : ℝ) ^ r * (Fintype.card V : ℝ) ^ r ≤
      ((labelledCliqueMaps r G).card : ℝ) := by
  classical
  letI : MeasurableSpace V := ⊤
  letI : MeasurableSingletonClass V := ⟨fun _ => trivial⟩
  let μ := (PMF.uniformOfFintype V).toMeasure
  let d := edgeMass G (fun _ => 1 / (Fintype.card V : ℝ))
  have hsup := sampling_clique_supersaturation hr hs G μ
  dsimp only [μ] at hsup
  rw [finiteGraphKernel_density_uniform, cliqueMapProbability_uniform] at hsup
  have hdhalf : d ≤ 1 / 2 := by
    dsimp only [d]
    rw [← finiteGraphKernel_density_uniform]
    exact Graphon.density_le_half μ (finiteGraphKernel G)
  have hsz : (0 : ℝ) < s := by exact_mod_cast hs
  have hn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hloss : (s : ℝ)⁻¹ * d ≤ δ / 2 := by
    calc
      (s : ℝ)⁻¹ * d ≤ (s : ℝ)⁻¹ * (1 / 2) :=
        mul_le_mul_of_nonneg_left hdhalf (inv_nonneg.mpr hsz.le)
      _ ≤ δ / 2 := by linarith
  have hcount : δ ≤ (s : ℝ) ^ r * (Fintype.card V : ℝ)⁻¹ ^ r *
      ((labelledCliqueMaps r G).card : ℝ) := by
    dsimp only [d] at hloss hdhalf
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hcount
    (show 0 ≤ (Fintype.card V : ℝ) ^ r by positivity)
  have hcancel : ((s : ℝ) ^ r * (Fintype.card V : ℝ)⁻¹ ^ r *
      ((labelledCliqueMaps r G).card : ℝ)) * (Fintype.card V : ℝ) ^ r =
      (s : ℝ) ^ r * ((labelledCliqueMaps r G).card : ℝ) := by
    calc
      _ = (s : ℝ) ^ r * ((labelledCliqueMaps r G).card : ℝ) *
          ((Fintype.card V : ℝ)⁻¹ * Fintype.card V) ^ r := by ring
      _ = _ := by rw [inv_mul_cancel₀ hn]; simp
  rw [hcancel] at hmul
  calc
    δ / (s : ℝ) ^ r * (Fintype.card V : ℝ) ^ r =
        (δ * (Fintype.card V : ℝ) ^ r) / (s : ℝ) ^ r := by ring
    _ ≤ _ := (div_le_iff₀ (pow_pos hsz r)).mpr (by simpa only [mul_comm] using hmul)

end DensityHS
