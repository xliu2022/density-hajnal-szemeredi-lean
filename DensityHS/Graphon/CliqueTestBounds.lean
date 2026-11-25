module

public import DensityHS.Graphon.CliqueTests

/-!
# Uniform cut-norm estimates for cover tests

Author and maintainer: Xizhi Liu.

Every rectangle test changes by at most `(r+1)|E(K_r)|` times the cut norm,
uniformly over all measurable unit-interval-valued cover candidates.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set
open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]

theorem tupleRectangle_indicator_prod {r : ℕ} (S : Fin r → Set Ω)
    (g : Fin r → Ω → ℝ) (t : Fin r → Ω) :
    (∏ i, (S i).indicator (g i) (t i)) =
      (tupleRectangle r S).indicator (fun t => ∏ i, g i (t i)) t := by
  classical
  by_cases ht : t ∈ tupleRectangle r S
  · rw [Set.indicator_of_mem ht]
    apply Finset.prod_congr rfl
    intro i _
    exact Set.indicator_of_mem (mem_tupleRectangle.mp ht i) _
  · rw [Set.indicator_of_notMem ht]
    have hn : ∃ i, t i ∉ S i := by simpa only [mem_tupleRectangle,not_forall] using ht
    obtain ⟨i,hi⟩ := hn
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact Set.indicator_of_notMem hi _

theorem rect_weighted_clique_difference_le {r : ℕ} (W U : Kernel Ω)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Fin r → Set Ω) (hS : ∀ i, MeasurableSet (S i))
    (g : Fin r → Ω → ℝ) (hg : ∀ i, Measurable (g i))
    (hb : ∀ i x, g i x ∈ Icc (0:ℝ) 1) :
    |∫ t in tupleRectangle r S, (∏ i, g i (t i))*(cliqueWeight r W t-cliqueWeight r U t)
      ∂Measure.pi (fun _ => μ)| ≤
      (⊤ : SimpleGraph (Fin r)).edgeFinset.card*kernelCutDistance μ W U := by
  classical
  have h := vertex_weighted_kernel_product_sub_le (μ := μ) W U
    (⊤ : SimpleGraph (Fin r)).edgeFinset
    (fun e he => Vendor.Graphon.edge_out_ne (SimpleGraph.mem_edgeFinset.mp he))
    (fun i => (S i).indicator (g i)) (fun i => (hg i).indicator (hS i))
    (fun i x => by
      by_cases hx : x ∈ S i
      · simpa only [Set.indicator_of_mem hx] using hb i x
      · simp only [Set.indicator_of_notMem hx,mem_Icc]; norm_num)
  change |∫ t, (∏ i, (S i).indicator (g i) (t i))*
    (cliqueWeight r W t-cliqueWeight r U t) ∂Measure.pi (fun _ => μ)| ≤ _ at h
  rw [← integral_indicator (measurableSet_tupleRectangle hS)]
  convert h using 2
  apply integral_congr_ae
  filter_upwards with t
  rw [tupleRectangle_indicator_prod]
  by_cases ht : t ∈ tupleRectangle r S
  · rw [Set.indicator_of_mem ht,Set.indicator_of_mem ht]
  · rw [Set.indicator_of_notMem ht,Set.indicator_of_notMem ht,zero_mul]

theorem integrable_vertex_clique_difference {r : ℕ} (W U : Kernel Ω)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Fin r → Ω → ℝ) (hg : ∀ i, Measurable (g i))
    (hb : ∀ i x, g i x ∈ Icc (0:ℝ) 1) :
    Integrable (fun t : Fin r → Ω =>
      (∏ i, g i (t i))*(cliqueWeight r W t-cliqueWeight r U t))
      (Measure.pi (fun _ => μ)) := by
  apply Integrable.bdd_mul ((integrable_cliqueWeight r W μ).sub (integrable_cliqueWeight r U μ))
    (Finset.measurable_prod _ (fun i _ => (hg i).comp (measurable_pi_apply i))).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun t => by
    change ‖∏ i, g i (t i)‖ ≤ (1:ℝ)
    rw [Real.norm_eq_abs,abs_of_nonneg (Finset.prod_nonneg (fun i _ => (hb i (t i)).1))]
    exact Finset.prod_le_one₀ (fun i _ => (hb i (t i)).1) (fun i _ => (hb i (t i)).2)

/-- Uniform control of a single-coordinate weighted rectangle integral. -/
theorem rect_coordinate_clique_difference_le {r : ℕ} (W U : Kernel Ω)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Fin r → Set Ω) (hS : ∀ i, MeasurableSet (S i))
    {c : Ω → ℝ} (hc : Measurable c) (hb : ∀ x, c x ∈ Icc (0:ℝ) 1) (i : Fin r) :
    |∫ t in tupleRectangle r S, c (t i)*(cliqueWeight r W t-cliqueWeight r U t)
      ∂Measure.pi (fun _ => μ)| ≤
      (⊤ : SimpleGraph (Fin r)).edgeFinset.card*kernelCutDistance μ W U := by
  classical
  have h := rect_weighted_clique_difference_le W U μ S hS
    (fun j x => if j=i then c x else 1)
    (fun j => by split_ifs <;> first | exact hc | exact measurable_const)
    (fun j x => by split_ifs <;> first | exact hb x | exact ⟨by norm_num,le_rfl⟩)
  simpa only [Finset.prod_ite_eq',Finset.mem_univ,if_true] using h

theorem rectCliqueTest_cut_bound {r : ℕ} (W U : Kernel Ω)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Fin r → Set Ω) (hS : ∀ i, MeasurableSet (S i))
    {c : Ω → ℝ} (hc : Measurable c) (hb : ∀ x, c x ∈ Icc (0:ℝ) 1) :
    |rectCliqueTest r W μ S c-rectCliqueTest r U μ S c| ≤
      ((r:ℝ)+1)*(⊤ : SimpleGraph (Fin r)).edgeFinset.card*kernelCutDistance μ W U := by
  classical
  let π := (Measure.pi (fun _ : Fin r => μ)).restrict (tupleRectangle r S)
  let Δ : (Fin r → Ω) → ℝ := fun t => cliqueWeight r W t-cliqueWeight r U t
  have hci := integrable_of_unitInterval (μ := μ) hc (fun x => (hb x).1) (fun x => (hb x).2)
  have hd : Integrable Δ π :=
    ((integrable_cliqueWeight r W μ).sub (integrable_cliqueWeight r U μ)).integrableOn
  have hi (i : Fin r) : Integrable (fun t => c (t i)*Δ t) π := by
    apply hd.bdd_mul (hc.comp (measurable_pi_apply i)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun t => by
      change ‖c (t i)‖ ≤ (1:ℝ)
      rw [Real.norm_eq_abs,abs_of_nonneg (hb (t i)).1]
      exact (hb (t i)).2
  have heq : rectCliqueTest r W μ S c-rectCliqueTest r U μ S c =
      (∑ i : Fin r, ∫ t, c (t i)*Δ t ∂π)-(∫ t, Δ t ∂π) := by
    unfold rectCliqueTest
    rw [← integral_sub (integrable_clique_test W μ hci).integrableOn
      (integrable_clique_test U μ hci).integrableOn]
    change (∫ t, _ ∂π)=_
    rw [← integral_finsetSum _ (fun i _ => hi i),
      ← integral_sub (integrable_finsetSum _ (fun i _ => hi i)) hd]
    apply integral_congr_ae
    filter_upwards with t
    dsimp [Δ]
    rw [← Finset.sum_mul]
    ring
  rw [heq]
  calc
    _ ≤ |∑ i : Fin r, ∫ t, c (t i)*Δ t ∂π|+|∫ t, Δ t ∂π| := abs_sub _ _
    _ ≤ (∑ i : Fin r, |∫ t, c (t i)*Δ t ∂π|)+|∫ t, Δ t ∂π| :=
      add_le_add (Finset.abs_sum_le_sum_abs _ _) le_rfl
    _ ≤ (∑ _i : Fin r, (⊤ : SimpleGraph (Fin r)).edgeFinset.card*kernelCutDistance μ W U)+
        (⊤ : SimpleGraph (Fin r)).edgeFinset.card*kernelCutDistance μ W U := by
      apply add_le_add
      · exact Finset.sum_le_sum (fun i _ => rect_coordinate_clique_difference_le W U μ S hS hc hb i)
      · have h := rect_weighted_clique_difference_le W U μ S hS
          (fun _ _ => 1) (fun _ => measurable_const) (fun _ _ => ⟨by norm_num,le_rfl⟩)
        simpa only [Finset.prod_const_one,one_mul] using h
    _ = _ := by simp; ring

end DensityHS.Graphon
