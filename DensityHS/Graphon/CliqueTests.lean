module

public import DensityHS.Graphon.WeightedCounting
public import DensityHS.Graphon.Duality

/-!
# Rectangular integral tests for fractional clique covers

Author and maintainer: Xizhi Liu.

Cover feasibility is equivalent to nonnegativity of concrete clique-weighted
rectangle tests. The converse uses countably many rational boxes in the
cover values; it does not assume a product-measure positivity principle.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set
open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]

theorem Kernel.pairFun_out_mk (W : Kernel Ω) {V : Type*} (t : V → Ω) (i j : V) :
    W.pairFun (t (Quot.out s(i,j)).1,t (Quot.out s(i,j)).2) = W (t i) (t j) := by
  let f : Sym2 V → ℝ := Sym2.lift ⟨fun a b => W (t a) (t b),fun a b => W.symmetric _ _⟩
  have h : s((Quot.out s(i,j)).1,(Quot.out s(i,j)).2) = s(i,j) := Quot.out_eq _
  exact congrArg f h

/-- Product of the edge values on a labelled complete graph. -/
noncomputable def cliqueWeight (r : ℕ) (W : Kernel Ω) (t : Fin r → Ω) : ℝ := by
  classical
  exact ∏ e ∈ (⊤ : SimpleGraph (Fin r)).edgeFinset,
    W.pairFun (t (Quot.out e).1,t (Quot.out e).2)

theorem cliqueWeight_mem_Icc (r : ℕ) (W : Kernel Ω) (t : Fin r → Ω) :
    cliqueWeight r W t ∈ Icc (0:ℝ) 1 := by
  classical
  exact kernel_edge_product_mem_Icc _ (fun _ => W) t

theorem measurable_cliqueWeight (r : ℕ) (W : Kernel Ω) : Measurable (cliqueWeight r W) := by
  classical
  exact measurable_kernel_edge_product _ (fun _ => W)

theorem integrable_cliqueWeight (r : ℕ) (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] : Integrable (cliqueWeight r W) (Measure.pi (fun _ => μ)) :=
  integrable_of_unitInterval (measurable_cliqueWeight r W)
    (fun t => (cliqueWeight_mem_Icc r W t).1) (fun t => (cliqueWeight_mem_Icc r W t).2)

theorem cliqueWeight_pos_iff (r : ℕ) (W : Kernel Ω) (t : Fin r → Ω) :
    0 < cliqueWeight r W t ↔ t ∈ cliqueTuples r W := by
  classical
  constructor
  · intro h i j hij
    have he : s(i,j) ∈ (⊤ : SimpleGraph (Fin r)).edgeFinset := by simp [hij]
    have hn := Finset.prod_ne_zero_iff.mp h.ne' _ he
    rw [W.pairFun_out_mk t i j] at hn
    exact lt_of_le_of_ne (W.nonneg _ _) (Ne.symm hn)
  · intro h
    apply Finset.prod_pos
    intro e he
    exact h _ _ (Vendor.Graphon.edge_out_ne (SimpleGraph.mem_edgeFinset.mp he))

/-- A finite product of measurable vertex sets. -/
def tupleRectangle (r : ℕ) (S : Fin r → Set Ω) : Set (Fin r → Ω) :=
  Set.pi Set.univ S

theorem measurableSet_tupleRectangle {r : ℕ} {S : Fin r → Set Ω}
    (hS : ∀ i, MeasurableSet (S i)) : MeasurableSet (tupleRectangle r S) :=
  MeasurableSet.univ_pi hS

theorem mem_tupleRectangle {r : ℕ} {S : Fin r → Set Ω} {t : Fin r → Ω} :
    t ∈ tupleRectangle r S ↔ ∀ i, t i ∈ S i := by simp [tupleRectangle]

/-- A cover test on a measurable rectangle, using actual clique products. -/
noncomputable def rectCliqueTest (r : ℕ) (W : Kernel Ω) (μ : Measure Ω)
    (S : Fin r → Set Ω) (c : Ω → ℝ) : ℝ :=
  ∫ t in tupleRectangle r S, cliqueWeight r W t*(∑ i, c (t i)-1)
    ∂Measure.pi (fun _ => μ)

theorem integrable_clique_test {r : ℕ} (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {c : Ω → ℝ} (hc : Integrable c μ) :
    Integrable (fun t : Fin r → Ω => cliqueWeight r W t*(∑ i, c (t i)-1))
      (Measure.pi (fun _ => μ)) := by
  apply Integrable.bdd_mul
    ((integrable_finsetSum Finset.univ (fun i _ => integrable_comp_eval hc)).sub
      (integrable_const (1:ℝ)))
    (measurable_cliqueWeight r W).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun t => by
    rw [Real.norm_eq_abs,abs_of_nonneg (cliqueWeight_mem_Icc r W t).1]
    exact (cliqueWeight_mem_Icc r W t).2

theorem IsKernelCover.rectCliqueTest_nonneg {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {c : Ω → ℝ} (hc : IsKernelCover r W μ c)
    (S : Fin r → Set Ω) : 0 ≤ rectCliqueTest r W μ S c := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_of_ae hc.2.2] with t ht
  by_cases hp : 0 < cliqueWeight r W t
  · exact mul_nonneg hp.le (sub_nonneg.mpr (ht ((cliqueWeight_pos_iff r W t).mp hp)))
  · have hz : cliqueWeight r W t=0 := le_antisymm (le_of_not_gt hp)
      (cliqueWeight_mem_Icc r W t).1
    simp [hz]

/-- Any strictly deficient finite vector admits a coordinatewise larger
rational vector that is still strictly deficient. -/
theorem exists_rat_tuple_above_of_sum_lt_one {r : ℕ} (a : Fin r → ℝ)
    (ha : ∑ i, a i < 1) :
    ∃ q : Fin r → ℚ, (∀ i, a i < (q i:ℝ)) ∧ ∑ i, (q i:ℝ) < 1 := by
  let δ := (1-∑ i, a i)/((r:ℝ)+1)
  have hd : 0 < δ := div_pos (sub_pos.mpr ha) (by positivity)
  have hq : ∀ i, ∃ q : ℚ, a i < (q:ℝ) ∧ (q:ℝ) < a i+δ :=
    fun i => exists_rat_btwn (by linarith)
  choose q hq0 hq1 using hq
  refine ⟨q,hq0,?_⟩
  have hs : (∑ i, (q i:ℝ)) ≤ (∑ i, a i)+(r:ℝ)*δ := by
    calc
      _ ≤ ∑ i, (a i+δ) := Finset.sum_le_sum (fun i _ => (hq1 i).le)
      _ = _ := by simp [Finset.sum_add_distrib]
  have he : δ*((r:ℝ)+1)=1-∑ i, a i :=
    div_mul_cancel₀ _ (by positivity)
  nlinarith

theorem isKernelCover_of_rectCliqueTests {r : ℕ} (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {c : Ω → ℝ} (hc : Measurable c)
    (hb : ∀ x, c x ∈ Icc (0:ℝ) 1)
    (htest : ∀ S : Fin r → Set Ω, (∀ i, MeasurableSet (S i)) →
      0 ≤ rectCliqueTest r W μ S c) : IsKernelCover r W μ c := by
  classical
  have hci := integrable_of_unitInterval (μ := μ) hc (fun x => (hb x).1) (fun x => (hb x).2)
  have hzero (q : Fin r → ℚ) (hq : ∑ i, (q i:ℝ) < 1) :
      ∀ᵐ t : Fin r → Ω ∂Measure.pi (fun _ => μ),
        (∀ i, c (t i)<(q i:ℝ)) → cliqueWeight r W t=0 := by
    let S : Fin r → Set Ω := fun i => {x | c x<(q i:ℝ)}
    have hS (i : Fin r) : MeasurableSet (S i) := measurableSet_lt hc measurable_const
    have hR := measurableSet_tupleRectangle hS
    have hupper : rectCliqueTest r W μ S c ≤
        ((∑ i, (q i:ℝ))-1)*(∫ t in tupleRectangle r S,
          cliqueWeight r W t ∂Measure.pi (fun _ => μ)) := by
      change (∫ t in tupleRectangle r S, cliqueWeight r W t*(∑ i, c (t i)-1)
        ∂Measure.pi (fun _ => μ)) ≤
          ((∑ i, (q i:ℝ))-1)*(∫ t in tupleRectangle r S,
            cliqueWeight r W t ∂Measure.pi (fun _ => μ))
      rw [← integral_const_mul]
      apply integral_mono_ae (integrable_clique_test W μ hci).integrableOn
        ((integrable_cliqueWeight r W μ).integrableOn.const_mul _)
      filter_upwards [ae_restrict_mem hR] with t ht
      have ht' := mem_tupleRectangle.mp ht
      have hsum : (∑ i, c (t i)) ≤ ∑ i, (q i:ℝ) :=
        Finset.sum_le_sum (fun i _ => (ht' i).le)
      have hnn := (cliqueWeight_mem_Icc r W t).1
      nlinarith
    have hn : 0 ≤ ∫ t in tupleRectangle r S, cliqueWeight r W t
        ∂Measure.pi (fun _ => μ) := integral_nonneg (fun t => (cliqueWeight_mem_Icc r W t).1)
    have hz : (∫ t in tupleRectangle r S, cliqueWeight r W t
        ∂Measure.pi (fun _ => μ))=0 := by
      have ht := htest S hS
      nlinarith
    have hae : cliqueWeight r W =ᵐ[(Measure.pi (fun _ : Fin r => μ)).restrict
        (tupleRectangle r S)] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun t => (cliqueWeight_mem_Icc r W t).1)
        (integrable_cliqueWeight r W μ).integrableOn).mp hz
    have ha := (ae_restrict_iff' hR).mp hae
    filter_upwards [ha] with t ht
    intro hall
    exact ht (mem_tupleRectangle.mpr hall)
  have hall : ∀ᵐ t : Fin r → Ω ∂Measure.pi (fun _ => μ),
      ∀ q : Fin r → ℚ, (∑ i, (q i:ℝ)<1) →
        (∀ i, c (t i)<(q i:ℝ)) → cliqueWeight r W t=0 := by
    apply ae_all_iff.mpr
    intro q
    by_cases hq : ∑ i, (q i:ℝ)<1
    · exact (hzero q hq).mono (fun _ ht _ => ht)
    · exact Filter.Eventually.of_forall (fun _ h => (hq h).elim)
  refine ⟨hc,hb,?_⟩
  filter_upwards [hall] with t ht
  intro hcl
  by_contra! hbad
  obtain ⟨q,hq0,hq1⟩ := exists_rat_tuple_above_of_sum_lt_one (fun i => c (t i)) hbad
  have hpos := (cliqueWeight_pos_iff r W t).mpr hcl
  rw [ht q hq1 hq0] at hpos
  exact lt_irrefl _ hpos

end DensityHS.Graphon
