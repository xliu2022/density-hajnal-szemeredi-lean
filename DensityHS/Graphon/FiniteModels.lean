module

public import DensityHS.Finite.MatrixCut
public import DensityHS.Basic.FiniteDuality
public import DensityHS.Graphon.Duality
public import DensityHS.Graphon.CutL1

/-!
# Actual finite labelled kernel models

Author and maintainer: Xizhi Liu.

Finite matrices are realized on arbitrary measurable finite partitions.
Exact rectangle integrals transfer finite cut estimates, and actual finite
clique covers pull back to measurable kernel covers.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set Finset Fintype Filter
open scoped BigOperators

variable {Ω Λ I J : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]
  [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]

/-- Realize a finite symmetric matrix using a measurable label map. -/
noncomputable def finiteLabelKernel (F : I → I → ℝ)
    (hsymm : ∀ i j, F i j = F j i) (h0 : ∀ i j, 0 ≤ F i j) (h1 : ∀ i j, F i j ≤ 1)
    (label : Ω → I) (hlabel : Measurable label) : Kernel Ω where
  toFun x y := F (label x) (label y)
  measurable_uncurry := (measurable_of_finite (fun z : I × I => F z.1 z.2)).comp
    (hlabel.prodMap hlabel)
  symmetric x y := hsymm _ _
  nonneg x y := h0 _ _
  le_one x y := h1 _ _

theorem integral_finite_label (μ : Measure Ω) [IsFiniteMeasure μ]
    (label : Ω → I) (hlabel : Measurable label) (f : I → ℝ) :
    (∫ x, f (label x) ∂μ) = ∑ i, μ.real {x | label x = i} * f i := by
  classical
  have hmeas (i : I) : MeasurableSet {x | label x = i} :=
    hlabel (measurableSet_singleton i)
  have hid (x : Ω) : (∑ i, ({x | label x = i}).indicator (fun _ => f i) x) = f (label x) := by
    rw [Finset.sum_eq_single (label x)]
    · simp
    · intro i _ hi
      simp [Ne.symm hi]
    · simp
  calc
    _ = ∫ x, ∑ i, ({x | label x = i}).indicator (fun _ => f i) x ∂μ :=
      integral_congr_ae (Eventually.of_forall fun x => (hid x).symm)
    _ = ∑ i, ∫ x, ({x | label x = i}).indicator (fun _ => f i) x ∂μ :=
      integral_finsetSum _ (fun i _ => (integrable_const _).indicator (hmeas i))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_indicator (hmeas i), setIntegral_const, smul_eq_mul]

theorem integral_finite_pair_labels (μ : Measure Ω) (ν : Measure Λ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (label : Ω → I) (hlabel : Measurable label)
    (label' : Λ → J) (hlabel' : Measurable label') (F : I → J → ℝ) :
    (∫ z : Ω × Λ, F (label z.1) (label' z.2) ∂μ.prod ν) =
      ∑ i, ∑ j, μ.real {x | label x = i} * ν.real {y | label' y = j} * F i j := by
  have h := integral_finite_label (μ.prod ν) (Prod.map label label')
    (hlabel.prodMap hlabel') (fun z : I × J => F z.1 z.2)
  rw [Fintype.sum_prod_type] at h
  convert h using 1
  · rfl
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have he : {z : Ω × Λ | Prod.map label label' z = (i,j)} =
        {x | label x = i} ×ˢ {y | label' y = j} := by
      ext z
      change (label z.1,label' z.2) = (i,j) ↔ label z.1 = i ∧ label' z.2 = j
      simp only [Prod.mk.injEq]
    rw [he, measureReal_prod_prod]

theorem setIntegral_finite_pair_labels (μ : Measure Ω) [IsFiniteMeasure μ]
    (label : Ω → I) (hlabel : Measurable label) (F : I → I → ℝ) (S T : Set Ω) :
    (∫ z : Ω × Ω in S ×ˢ T, F (label z.1) (label z.2) ∂μ.prod μ) =
      ∑ i, ∑ j, μ.real ({x | label x = i} ∩ S) *
        μ.real ({y | label y = j} ∩ T) * F i j := by
  rw [← Measure.prod_restrict]
  rw [integral_finite_pair_labels (μ.restrict S) (μ.restrict T) label hlabel label hlabel]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hreal (R : Set Ω) (k : I) : (μ.restrict R).real {x | label x = k} =
      μ.real ({x | label x = k} ∩ R) := by
    exact congrArg ENNReal.toReal (Measure.restrict_apply
      (μ := μ) (s := R) (measurableSet_eq_fun hlabel measurable_const))
  rw [hreal S i,hreal T j]

/-- Finite rectangle discrepancy controls the actual kernel cut norm on
equal-measure cells. This also covers tests cutting through vertex cells. -/
theorem kernelCutDistance_of_finite_rectangles (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W U : Kernel Ω) (label : Ω → I) (hlabel : Measurable label)
    (F H : I → I → ℝ)
    (hW : ∀ x y, W x y = F (label x) (label y))
    (hU : ∀ x y, U x y = H (label x) (label y))
    {N B : ℝ} (hN : 0 < N)
    (hmass : ∀ i, μ.real {x | label x = i} = 1/N)
    (hrect : ∀ S T : Finset I, |∑ i ∈ S, ∑ j ∈ T, (F i j-H i j)| ≤ B) :
    kernelCutDistance μ W U ≤ B/N^2 := by
  apply csSup_le ⟨0,zero_mem_rectangleDiscrepancies μ W U⟩
  rintro a ⟨S,T,hS,hT,rfl⟩
  have heq : (∫ z in S ×ˢ T, W z.1 z.2-U z.1 z.2 ∂μ.prod μ) =
      ∑ i, ∑ j, μ.real ({x | label x = i} ∩ S) *
        μ.real ({y | label y = j} ∩ T) * (F i j-H i j) := by
    simp_rw [hW,hU]
    exact setIntegral_finite_pair_labels μ label hlabel (fun i j => F i j-H i j) S T
  let a : I → ℝ := fun i => N*μ.real ({x | label x = i} ∩ S)
  let b : I → ℝ := fun i => N*μ.real ({x | label x = i} ∩ T)
  have ha0 : ∀ i, 0 ≤ a i := fun i => mul_nonneg hN.le (measureReal_nonneg)
  have hb0 : ∀ i, 0 ≤ b i := fun i => mul_nonneg hN.le (measureReal_nonneg)
  have hslice (i : I) (R : Set Ω) : N*μ.real ({x | label x = i} ∩ R) ≤ 1 := by
    calc
      _ ≤ N*μ.real {x | label x = i} :=
        mul_le_mul_of_nonneg_left (measureReal_mono Set.inter_subset_left) hN.le
      _ = 1 := by rw [hmass]; field_simp
  have hbil := MatrixRegularity.abs_bilinear_le_of_rectangles (fun i j => F i j-H i j)
    a b ha0 (fun i => hslice i S) hb0 (fun i => hslice i T) hrect
  have hscale : (∑ i, ∑ j, (F i j-H i j)*a i*b j) =
      N^2*(∑ i, ∑ j, μ.real ({x | label x = i} ∩ S) *
        μ.real ({y | label y = j} ∩ T) * (F i j-H i j)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [a,b]
    ring
  rw [hscale,abs_mul,abs_of_nonneg (sq_nonneg N)] at hbil
  rw [heq]
  apply (le_div_iff₀ (sq_pos_of_pos hN)).mpr
  simpa only [mul_comm] using hbil

/-- A finite clique cover is an actual measurable cover of any kernel
whose positive pairs follow the finite support graph. -/
theorem isKernelCover_of_finite_cover [DecidableEq I]
    {r : ℕ} (W : Kernel Ω) (μ : Measure Ω)
    (label : Ω → I) (hlabel : Measurable label) (H : SimpleGraph I)
    (hsupport : ∀ x y, 0 < W x y → H.Adj (label x) (label y))
    {c : I → ℝ} (hc : IsCliqueCover r H c) (hc1 : ∀ i, c i ≤ 1) :
    IsKernelCover r W μ (c ∘ label) := by
  classical
  refine ⟨(measurable_of_finite c).comp hlabel, fun x => ⟨hc.1 _,hc1 _⟩,?_⟩
  apply Eventually.of_forall
  intro t ht
  let f : Fin r → I := fun i => label (t i)
  have hf : Function.Injective f := by
    intro i j heq
    by_contra hij
    have h := hsupport (t i) (t j) (ht i j hij)
    change H.Adj (f i) (f j) at h
    rw [heq] at h
    exact H.irrefl h
  have hK : H.IsNClique r (Finset.univ.image f) := by
    constructor
    · intro u hu v hv huv
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hv
      exact hsupport _ _ (ht i j (fun hij => huv (congrArg f hij)))
    · rw [Finset.card_image_of_injective _ hf]
      simp
  have h := hc.2 _ hK
  rw [Finset.sum_image (fun i _ j _ h => hf h)] at h
  exact h

theorem coverNumber_le_finite_cost [DecidableEq I]
    {r : ℕ} (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (label : Ω → I) (hlabel : Measurable label) (H : SimpleGraph I)
    (hsupport : ∀ x y, 0 < W x y → H.Adj (label x) (label y))
    {c : I → ℝ} (hc : IsCliqueCover r H c) :
    coverNumber r W μ ≤ coverCost (fun i => μ.real {x | label x = i}) c := by
  have hk := isKernelCover_of_finite_cover W μ label hlabel H hsupport hc.truncate
    (fun _ => min_le_right _ _)
  have h := coverNumber_le_cost hk
  change coverNumber r W μ ≤ ∫ x, min (c (label x)) 1 ∂μ at h
  rw [integral_finite_label μ label hlabel (fun i => min (c i) 1)] at h
  exact h.trans (coverCost_truncate_le (fun _ => measureReal_nonneg))

theorem tilingNumber_le_finite_tilingNumber [DecidableEq I]
    {r : ℕ} (hr : 0 < r) (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (label : Ω → I) (hlabel : Measurable label) (H : SimpleGraph I)
    (hsupport : ∀ x y, 0 < W x y → H.Adj (label x) (label y)) :
    tilingNumber r W μ ≤ fractionalTilingNumber r H (fun i => μ.real {x | label x = i}) := by
  obtain ⟨c,t,hc,ht,heq⟩ := fractional_strong_duality r H hr
    (fun i => μ.real {x | label x = i}) (fun _ => measureReal_nonneg)
  rw [kernel_tiling_cover_duality r W μ hr,← ht.size_eq_number,heq]
  exact coverNumber_le_finite_cost W μ label hlabel H hsupport hc.1

end DensityHS.Graphon
