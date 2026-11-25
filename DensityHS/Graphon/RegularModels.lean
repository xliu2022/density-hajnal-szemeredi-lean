module

public import DensityHS.Graphon.FiniteModels
public import DensityHS.Finite.RegularStep
public import DensityHS.Finite.Rounding
public import DensityHS.Finite.AsymptoticParameters

/-!
# Finite integral packing restrictions and nearby graphon models

Author and maintainer: Xizhi Liu.

The original graph is represented on equal-measure vertex cells. Its
regular dense model is close in cut norm and has fractional kernel tiling
number at most the normalized integral packing bound, with a uniformly
vanishing error. The integral-to-fractional step uses the proved actual
regular-pair embedding and integer rounding theorem.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set Finset Fintype Filter Regularity MatrixRegularity
open scoped BigOperators

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {V : Type v} [Fintype V] [DecidableEq V]
  [MeasurableSpace V] [MeasurableSingletonClass V]

noncomputable def regularModel (P : Finpartition (Finset.univ : Finset V))
    (G : SimpleGraph V) [DecidableRel G.Adj] (ε d : ℝ)
    (label : Ω → V) (hlabel : Measurable label) : Kernel Ω :=
  finiteLabelKernel (reducedStepMatrix P G ε d)
    (fun x y => reducedStepEntry_symm P G ε d _ _)
    (fun x y => reducedStepEntry_nonneg P G ε d _ _)
    (fun x y => reducedStepEntry_le_one P G ε d _ _) label hlabel

theorem cluster_label_mass (μ : Measure Ω) [IsProbabilityMeasure μ]
    (label : Ω → V) (hlabel : Measurable label)
    (hmass : ∀ x, μ.real {z | label z = x} = 1/(Fintype.card V : ℝ))
    (P : Finpartition (Finset.univ : Finset V)) (i : P.parts) :
    μ.real {z | clusterOf P (label z) = i} = clusterWeight P i := by
  have hs := sum_measureReal_preimage_singleton (μ := μ) i.val
    (fun x _ => hlabel (measurableSet_singleton x))
  have he : {z | clusterOf P (label z) = i} = label ⁻¹' (i.val : Set V) := by
    ext z
    exact clusterOf_eq_iff
  rw [he,← hs]
  change (∑ x ∈ i.val, μ.real {z | label z = x}) = clusterWeight P i
  simp only [hmass,Finset.sum_const,nsmul_eq_mul,clusterWeight]
  ring

theorem regularModel_tiling_bound [Nonempty V]
    {r k M : ℕ} (hr : 0 < r) (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (Finset.univ : Finset V))
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (label : Ω → V) (hlabel : Measurable label)
    (hmass : ∀ x, μ.real {z | label z = x} = 1/(Fintype.card V : ℝ))
    {ε d β δ : ℝ} (hε : 0 < ε) (hd : ε < d) (hd1 : d-ε ≤ 1)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hβδ : β ≤ δ/4)
    (hsmall : ε*r < β*(d-ε)^(r-1))
    (hM : P.parts.card ≤ M)
    (hlarge : (2 : ℝ)^M/(Fintype.card V : ℝ) ≤ δ/4)
    (hpack : HasPackingNumberAtMost r G k) :
    tilingNumber r (regularModel P G ε d label hlabel) μ ≤
      (k : ℝ)/Fintype.card V+δ/2 := by
  classical
  letI : MeasurableSpace P.parts := ⊤
  haveI : MeasurableSingletonClass P.parts := ⟨fun _ => trivial⟩
  let H := clusterGraph P G ε d
  let q : Ω → P.parts := fun z => clusterOf P (label z)
  have hq : Measurable q := (measurable_of_finite (clusterOf P)).comp hlabel
  have hsupport : ∀ x y, 0 < regularModel P G ε d label hlabel x y → H.Adj (q x) (q y) := by
    intro x y h
    change 0 < reducedStepEntry P G ε d (q x) (q y) at h
    unfold reducedStepEntry at h
    split_ifs at h with hij
    · exact hij
    · exact False.elim (lt_irrefl _ h)
  have htil := tilingNumber_le_finite_tilingNumber hr
    (regularModel P G ε d label hlabel) μ q hq H hsupport
  have hweights : (fun i => μ.real {z | q z = i}) = clusterWeight P := by
    funext i
    exact cluster_label_mass μ label hlabel hmass P i
  rw [hweights] at htil
  obtain ⟨c,t,hc,ht,heq⟩ := fractional_strong_duality r H hr (clusterWeight P)
    (clusterWeight_probability P).1
  rw [← ht.size_eq_number] at htil
  have hN : 0 < (Fintype.card V : ℝ) := by exact_mod_cast Fintype.card_pos
  have hround := reduced_tiling_bound_of_packing_bound hr G H
    (fun i : P.parts => i.val) hε hd hd1 hβ hβ1 hN
    (fun i j hij => P.disjoint i.property j.property (fun h => hij (Subtype.ext h)))
    (fun i => P.nonempty_of_mem_parts i.property)
    (fun i j hij => hij.2.1) (fun i j hij => hij.2.2) hsmall hpack ht.1
  have hz : tilingSize r H t ≤ 1 :=
    (tilingSize_le_inv hr (clusterWeight_probability P) ht.1).trans
      ((div_le_one (by positivity)).mpr (by exact_mod_cast hr))
  have hcard : ((cliqueFamily r H).card : ℝ) ≤ (2 : ℝ)^M := by
    exact_mod_cast card_cliqueFamily_le_two_pow r H (by simpa using hM)
  exact htil.trans (fractional_gap_of_rounding hN hβ.le hβδ hz
    ((div_le_div_of_nonneg_right hcard hN.le).trans hlarge) hround)

/-- Uniform approximation of finite integral-packing constraints by actual
kernel tiling constraints. Both errors can be chosen independently. -/
theorem exists_regular_kernel_model {r : ℕ} (hr : 3 ≤ r)
    {ρ τ : ℝ} (hρ : 0 < ρ) (hτ : 0 < τ) :
    ∃ n₀ : ℕ, ∀ {V : Type v} [Fintype V] [DecidableEq V]
      [MeasurableSpace V] [MeasurableSingletonClass V]
      (G : SimpleGraph V) [DecidableRel G.Adj], n₀ ≤ Fintype.card V →
      ∀ (μ : Measure Ω) [IsProbabilityMeasure μ]
        (label : Ω → V) (hlabel : Measurable label),
        (∀ x, μ.real {z | label z = x} = 1/(Fintype.card V : ℝ)) →
        ∀ (W : Kernel Ω), (∀ x y, W x y = indicatorMatrix G (label x) (label y)) →
        ∀ k : ℕ, HasPackingNumberAtMost r G k →
        ∃ U : Kernel Ω, kernelCutDistance μ W U < ρ ∧
          tilingNumber r U μ ≤ (k : ℝ)/Fintype.card V+τ := by
  obtain ⟨β,d,ε,hβ,hβ1,hβδ,hε,hεd,hd1,hsmall,hloss⟩ :=
    exists_regular_rounding_parameters hr (show 0 < ρ/4 by positivity)
      (show 0 < 2*τ by positivity)
  let l : ℕ := ⌈4/ρ⌉₊
  let M : ℕ := SzemerediRegularity.bound ε l
  obtain ⟨n₀,hl,hn₀,hlarge⟩ := exists_order_bound l M (show 0 < 2*τ by positivity)
  refine ⟨n₀,?_⟩
  intro V instV instDecV instMeasV instSingleV G instAdj hn μ instProb label hlabel hmass W hW k hpack
  classical
  haveI : Nonempty V := Fintype.card_pos_iff.mp (hn₀.trans_le hn)
  have hN : 0 < (Fintype.card V : ℝ) := by exact_mod_cast Fintype.card_pos
  obtain ⟨P,hP,hPl,hPM,hPreg⟩ := szemeredi_regularity G hε (hl.trans hn)
  have hparts : 4/ρ ≤ (P.parts.card : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hPl)
  let U := regularModel P G ε d label hlabel
  refine ⟨U,?_,?_⟩
  · have hcut := kernelCutDistance_of_finite_rectangles μ W U label hlabel
      (indicatorMatrix G) (reducedStepMatrix P G ε d) hW (fun _ _ => rfl)
      hN hmass (reducedStep_discrepancy hε (hε.trans hεd).le hρ hP hPreg hparts)
    have hcancel : ((5*ε+4*d+ρ/2)*(Fintype.card V : ℝ)^2)/(Fintype.card V : ℝ)^2 =
        5*ε+4*d+ρ/2 := mul_div_cancel_right₀ _ (ne_of_gt (sq_pos_of_pos hN))
    rw [hcancel] at hcut
    exact hcut.trans_lt (by linarith [hε.trans hεd])
  · have h := regularModel_tiling_bound (by omega : 0 < r) G P μ label hlabel hmass
      hε hεd hd1 hβ hβ1.le hβδ hsmall hPM (hlarge _ hn) hpack
    simpa only [mul_div_cancel_left₀ τ (by norm_num : (2 : ℝ) ≠ 0)] using h

end DensityHS.Graphon
