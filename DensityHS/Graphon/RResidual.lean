module

public import DensityHS.Graphon.RTypes

/-!
# Vanishing marked row residual

Author and maintainer: Xizhi Liu.

The marked clique exclusions make a row residual nonnegative. The exact
terminal degree identity makes its integral zero, forcing a rigid row law.
-/

@[expose] public section

namespace DensityHS.Graphon.MarkedBlockSystem

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Classical

variable {Ω : Type*} [MeasurableSpace Ω] {W : Kernel Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Z : Set Ω}

noncomputable def neighborSum (P : MarkedBlockSystem W μ Z) (A : Finset P.Index) (z : Ω) : ℝ :=
  ∑ i ∈ A, (P.neighbor i).indicator (fun _ => (1 : ℝ)) z

theorem measurable_neighborSum (P : MarkedBlockSystem W μ Z) (A : Finset P.Index) :
    Measurable (P.neighborSum A) := by
  classical
  exact Finset.measurable_sum A (fun i _ => measurable_const.indicator (P.neighbor_measurable i))

theorem integrable_neighborSum (P : MarkedBlockSystem W μ Z) (A : Finset P.Index) :
    Integrable (P.neighborSum A) μ := by
  classical
  exact integrable_finsetSum A (fun i _ => (integrable_const (1 : ℝ)).indicator (P.neighbor_measurable i))

theorem neighborSum_eq_card_filter (P : MarkedBlockSystem W μ Z) (A : Finset P.Index) (z : Ω) :
    P.neighborSum A z = ((A.filter fun i => z ∈ P.neighbor i).card : ℝ) := by
  classical
  simp only [neighborSum, Set.indicator_apply, Finset.sum_boole]

theorem neighborSum_of_typeFiber (P : MarkedBlockSystem W μ Z)
    (A B : Finset P.Index) {z : Ω} (hz : z ∈ P.typeFiber B) :
    P.neighborSum A z = ((A ∩ B).card : ℝ) := by
  classical
  rw [P.neighborSum_eq_card_filter]
  congr 2
  ext i
  simp only [Finset.mem_filter, Finset.mem_inter, hz.2 i]

theorem integral_neighborSum (P : MarkedBlockSystem W μ Z) (hZ : MeasurableSet Z)
    (A : Finset P.Index) : (∫ z in Z, P.neighborSum A z ∂μ) = ∑ i ∈ A, P.mass i := by
  classical
  change (∫ z in Z, ∑ i ∈ A, (P.neighbor i).indicator (fun _ => (1 : ℝ)) z ∂μ) = _
  rw [integral_finsetSum A (fun i _ =>
    ((integrable_const (1 : ℝ)).indicator (P.neighbor_measurable i)).integrableOn)]
  apply Finset.sum_congr rfl
  intro i _
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun z hz => Set.indicator_of_notMem (fun hi => hz (P.neighbor_subset i hi)) _),
    integral_indicator_const (1 : ℝ) (P.neighbor_measurable i), smul_eq_mul, mul_one]
  exact P.neighbor_mass i

/-- The row residual is nonnegative by the two marked clique exclusions. -/
theorem ae_residual_nonneg (P : MarkedBlockSystem W μ Z) {r : ℕ} (hr : 3 ≤ r)
    (hZ : MeasurableSet Z) (hfree : NoCliqueMeets r W μ Z)
    (A : Finset P.Index) (hA : A.card ≤ r - 2) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ P.typeFiber A → z.2 ∈ Z →
      0 ≤ ((r : ℝ) - 2) - W z.1 z.2 - P.neighborSum A z.2 := by
  classical
  letI := P.countable
  have hall : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ∀ F : Finset P.Index, F.card = r - 2 →
      z.1 ∈ Z → z.2 ∈ Z → 0 < W z.1 z.2 →
        ¬ ∀ j ∈ F, z.1 ∈ P.neighbor j ∧ z.2 ∈ P.neighbor j := by
    apply ae_all_iff.mpr
    intro F
    by_cases hF : F.card = r - 2
    · exact (P.ae_edge_not_all_common_neighbors (by omega) hZ hfree F hF).mono fun _ hz _ => hz
    · exact Eventually.of_forall fun _ h => False.elim (hF h)
  filter_upwards [hall] with z hz hx hy
  rw [P.neighborSum_eq_card_filter]
  let F := A.filter fun i => z.2 ∈ P.neighbor i
  have hF : F.card ≤ r - 2 := (Finset.card_filter_le _ _).trans hA
  by_cases hW : 0 < W z.1 z.2
  · have hF' : F.card ≤ r - 3 := by
      by_contra! hn
      obtain ⟨E, hEF, hE⟩ := Finset.exists_subset_card_eq (show r - 2 ≤ F.card by omega)
      apply hz E hE hx.1 hy hW
      intro i hi
      have hfi := Finset.mem_filter.mp (hEF hi)
      exact ⟨(hx.2 i).mpr hfi.1, hfi.2⟩
    have hFr : (F.card : ℝ) ≤ (r : ℝ) - 3 := by
      have hh : (F.card : ℝ) ≤ ((r - 3 : ℕ) : ℝ) := by exact_mod_cast hF'
      simpa only [Nat.cast_sub (show 3 ≤ r from hr), Nat.cast_ofNat] using hh
    have hw1 := W.le_one z.1 z.2
    change 0 ≤ ((r : ℝ) - 2) - W z.1 z.2 - (F.card : ℝ)
    linarith
  · have hw0 : W z.1 z.2 = 0 := le_antisymm (le_of_not_gt hW) (W.nonneg _ _)
    have hFr : (F.card : ℝ) ≤ (r : ℝ) - 2 := by
      have hh : (F.card : ℝ) ≤ ((r - 2 : ℕ) : ℝ) := by exact_mod_cast hF
      simpa only [Nat.cast_sub (show 2 ≤ r by omega), Nat.cast_ofNat] using hh
    change 0 ≤ ((r : ℝ) - 2) - W z.1 z.2 - (F.card : ℝ)
    rw [hw0]
    linarith

/-- Equality of the marked degree forces an exact finite neighbor row law. -/
theorem ae_marked_row_of_degree (P : MarkedBlockSystem W μ Z) {r : ℕ} (hr : 3 ≤ r)
    (hZ : MeasurableSet Z) (hfree : NoCliqueMeets r W μ Z)
    (hd : ∀ᵐ z ∂μ, z ∈ Z → kernelDegree W μ z = ((r : ℝ) - 2) * μ.real Z)
    (A : Finset P.Index) (hA : A.card ≤ r - 2) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ P.typeFiber A → z.2 ∈ Z →
      W z.1 z.2 = ((r : ℝ) - 2) - P.neighborSum A z.2 := by
  have hn := ae_ae_of_ae_prod (P.ae_residual_nonneg hr hZ hfree A hA)
  have hall : ∀ᵐ z ∂μ, ∀ᵐ y ∂μ, z ∈ P.typeFiber A → y ∈ Z →
      W z y = ((r : ℝ) - 2) - P.neighborSum A y := by
    filter_upwards [hn, hd, P.ae_degree_of_typeFiber hZ] with z hz hdz hdeg
    by_cases hzt : z ∈ P.typeFiber A
    · let f : Ω → ℝ := fun y => ((r : ℝ) - 2) - W z y - P.neighborSum A y
      have hfi : Integrable f μ := ((integrable_const _).sub (W.integrable_left μ z)).sub
        (P.integrable_neighborSum A)
      have hnon : 0 ≤ᵐ[μ.restrict Z] f := by
        filter_upwards [ae_restrict_mem hZ, ae_restrict_of_ae hz] with y hy hzy
        exact hzy hzt hy
      have hzero : (∫ y in Z, f y ∂μ) = 0 := by
        change (∫ y in Z, ((r : ℝ) - 2) - W z y - P.neighborSum A y ∂μ) = 0
        have hiC : Integrable (fun _ : Ω => (r : ℝ) - 2) (μ.restrict Z) := integrable_const _
        have hiW : Integrable (fun y => W z y) (μ.restrict Z) := (W.integrable_left μ z).integrableOn
        have hiD : Integrable (fun y => ((r : ℝ) - 2) - W z y) (μ.restrict Z) := hiC.sub hiW
        rw [integral_sub hiD (P.integrable_neighborSum A).integrableOn,
          integral_sub hiC hiW, setIntegral_const, smul_eq_mul, P.integral_neighborSum hZ]
        have he := hdeg A hzt
        rw [hdz hzt.1] at he
        nlinarith
      have he := (integral_eq_zero_iff_of_nonneg_ae hnon hfi.integrableOn).mp hzero
      filter_upwards [(ae_restrict_iff' hZ).mp he] with y hy _ hyZ
      have hz0 := hy hyZ
      change ((r : ℝ) - 2) - W z y - P.neighborSum A y = 0 at hz0
      linarith
    · exact Eventually.of_forall fun _ h _ => False.elim (hzt h)
  have hm : MeasurableSet {z : Ω × Ω | z.1 ∈ P.typeFiber A → z.2 ∈ Z →
      W z.1 z.2 = ((r : ℝ) - 2) - P.neighborSum A z.2} := by
    have he : MeasurableSet {z : Ω × Ω | W z.1 z.2 = ((r : ℝ) - 2) - P.neighborSum A z.2} :=
      measurableSet_eq_fun W.measurable_uncurry
        ((measurable_const (a := (r : ℝ) - 2)).fun_sub
          ((P.measurable_neighborSum A).comp measurable_snd))
    have heq : {z : Ω × Ω | z.1 ∈ P.typeFiber A → z.2 ∈ Z →
        W z.1 z.2 = ((r : ℝ) - 2) - P.neighborSum A z.2} =
        ((P.typeFiber A) ×ˢ Z)ᶜ ∪ {z | W z.1 z.2 = ((r : ℝ) - 2) - P.neighborSum A z.2} := by
      ext z
      simp only [mem_setOf_eq, mem_union, mem_compl_iff, mem_prod]
      tauto
    rw [heq]
    exact ((P.measurable_typeFiber hZ A).prod hZ).compl.union he
  exact (ae_prod_iff_ae_ae hm).mpr hall

end DensityHS.Graphon.MarkedBlockSystem
