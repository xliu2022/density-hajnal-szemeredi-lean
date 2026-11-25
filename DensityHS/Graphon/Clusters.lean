module

public import DensityHS.Graphon.PSDRestricted
public import Mathlib.Probability.ConditionalProbability

/-!
# Measurable clique classes of a zero-one kernel

Author and maintainer: Xizhi Liu.

Row equivalence is represented by the vanishing of an actual square-distance
integral. Its fibers are measurable; positive-measure fibers are countable.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set Filter
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

noncomputable def rowSqDistance (W : Kernel Ω) (μ : Measure Ω) (x y : Ω) : ℝ :=
  ∫ z, (W x z - W y z) ^ 2 ∂μ

theorem integrable_rowSqDiff (W : Kernel Ω) (μ : Measure Ω) [IsFiniteMeasure μ] (x y : Ω) :
    Integrable (fun z => (W x z - W y z) ^ 2) μ := by
  apply integrable_of_unitInterval ((W.measurable_left x).sub (W.measurable_left y) |>.pow_const 2)
    (fun _ => sq_nonneg _)
  intro z
  simp only [Pi.sub_apply]
  have hx0 := W.nonneg x z
  have hy0 := W.nonneg y z
  have hx1 := W.le_one x z
  have hy1 := W.le_one y z
  nlinarith [sq_nonneg (W x z - W y z), mul_nonneg hx0 hy0,
    mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr hy1)]

theorem rowSqDistance_eq_zero_iff (W : Kernel Ω) (μ : Measure Ω) [IsFiniteMeasure μ]
    (x y : Ω) : rowSqDistance W μ x y = 0 ↔ W x =ᵐ[μ] W y := by
  rw [rowSqDistance, integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _)
    (integrable_rowSqDiff W μ x y)]
  simp only [Filter.EventuallyEq, Pi.zero_apply, sq_eq_zero_iff, sub_eq_zero]

theorem measurable_rowSqDistance (W : Kernel Ω) (μ : Measure Ω) [SFinite μ] :
    Measurable (Function.uncurry (rowSqDistance W μ)) := by
  have h1 : Measurable (fun p : (Ω × Ω) × Ω => W p.1.1 p.2) := by
    simpa only [Function.uncurry_def, Function.comp_def] using
      W.measurable_uncurry.comp (measurable_fst.fst.prodMk measurable_snd)
  have h2 : Measurable (fun p : (Ω × Ω) × Ω => W p.1.2 p.2) := by
    simpa only [Function.uncurry_def, Function.comp_def] using
      W.measurable_uncurry.comp (measurable_fst.snd.prodMk measurable_snd)
  have hm := ((h1.sub h2).pow_const 2).stronglyMeasurable.integral_prod_right' (ν := μ) |>.measurable
  simpa only [Function.uncurry_def, rowSqDistance, Pi.sub_apply] using hm

/-- Equality of kernel rows as elements of the space of measurable functions
modulo almost-everywhere equality. -/
def rowSetoid (W : Kernel Ω) (μ : Measure Ω) : Setoid Ω where
  r x y := W x =ᵐ[μ] W y
  iseqv := ⟨fun _ => EventuallyEq.rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

abbrev RowClass (W : Kernel Ω) (μ : Measure Ω) := Quotient (rowSetoid W μ)

def rowFiber (W : Kernel Ω) (μ : Measure Ω) (q : RowClass W μ) : Set Ω :=
  {x | Quotient.mk (rowSetoid W μ) x = q}

theorem rowFiber_iff (W : Kernel Ω) (μ : Measure Ω) (q : RowClass W μ) (x : Ω) :
    x ∈ rowFiber W μ q ↔ W x =ᵐ[μ] W q.out := by
  change Quotient.mk (rowSetoid W μ) x = q ↔ _
  conv_lhs => rw [← Quotient.out_eq q, Quotient.eq]
  rfl

theorem measurableSet_rowFiber (W : Kernel Ω) (μ : Measure Ω) [IsFiniteMeasure μ]
    (q : RowClass W μ) : MeasurableSet (rowFiber W μ q) := by
  have hm : Measurable (fun x => rowSqDistance W μ x q.out) := by
    simpa only [Function.uncurry_def, Function.comp_def, id_eq] using
      (measurable_rowSqDistance W μ).comp (measurable_id.prodMk measurable_const)
  have he : rowFiber W μ q = {x | rowSqDistance W μ x q.out = 0} := by
    ext x
    simp only [rowFiber_iff, Set.mem_setOf_eq, rowSqDistance_eq_zero_iff]
  rw [he]
  exact measurableSet_eq_fun hm measurable_const

theorem rowFibers_disjoint (W : Kernel Ω) (μ : Measure Ω) :
    Pairwise (fun q q' => Disjoint (rowFiber W μ q) (rowFiber W μ q')) := by
  intro q q' hqq
  exact Set.disjoint_left.mpr (fun x hx hx' => hqq (hx.symm.trans hx'))

theorem countable_positive_rowFibers (W : Kernel Ω) (μ : Measure Ω) [IsFiniteMeasure μ] :
    {q : RowClass W μ | 0 < μ (rowFiber W μ q)}.Countable :=
  Measure.countable_meas_pos_of_disjoint_iUnion
    (measurableSet_rowFiber W μ) (rowFibers_disjoint W μ)

/-- The degree is constant on each row class. -/
theorem degree_eq_of_row_eq (W : Kernel Ω) (μ : Measure Ω) {x y : Ω}
    (h : W x =ᵐ[μ] W y) : kernelDegree W μ x = kernelDegree W μ y := integral_congr_ae h

theorem kernelDegree_nonneg (W : Kernel Ω) (μ : Measure Ω) (x : Ω) :
    0 ≤ kernelDegree W μ x := integral_nonneg (W.nonneg x)

theorem degree_zero_iff_row_zero (W : Kernel Ω) (μ : Measure Ω) [IsFiniteMeasure μ] (x : Ω) :
    kernelDegree W μ x = 0 ↔ W x =ᵐ[μ] (fun _ => 0) :=
  integral_eq_zero_iff_of_nonneg (W.nonneg x) (W.integrable_left μ x)

/-- Every good nonzero row belongs to a positive-measure equivalence class. -/
theorem positive_rowFiber_of_edge_rows (W : Kernel Ω) (μ : Measure Ω) [IsFiniteMeasure μ]
    (x : Ω) (hb : ∀ᵐ y ∂μ, W x y = 0 ∨ W x y = 1)
    (hr : ∀ᵐ y ∂μ, W x y = 1 → W x =ᵐ[μ] W y)
    (hd : 0 < kernelDegree W μ x) :
    0 < μ (rowFiber W μ (Quotient.mk (rowSetoid W μ) x)) := by
  by_contra! hn
  have hm : μ (rowFiber W μ (Quotient.mk (rowSetoid W μ) x)) = 0 := le_antisymm hn bot_le
  have hnot : ∀ᵐ y ∂μ, y ∉ rowFiber W μ (Quotient.mk (rowSetoid W μ) x) := by
    simpa only [ae_iff, not_not, Set.setOf_mem_eq] using hm
  have hz : W x =ᵐ[μ] (fun _ => 0) := by
    filter_upwards [hb, hr, hnot] with y hy hyr hyn
    rcases hy with hy | hy
    · exact hy
    · exact False.elim (hyn (Quotient.sound (hyr hy).symm))
  exact (ne_of_gt hd) ((degree_zero_iff_row_zero W μ x).mpr hz)


/-- All rows in a row fiber agree with any chosen representative, with the
exceptional sets assembled by Fubini on the product space. -/
theorem rowFiber_common_profile (W : Kernel Ω) (μ : Measure Ω) [IsFiniteMeasure μ]
    (q : RowClass W μ) {a : Ω} (ha : a ∈ rowFiber W μ q) :
    ∀ᵐ p : Ω × Ω ∂μ.prod μ, p.1 ∈ rowFiber W μ q → W p.1 p.2 = W a p.2 := by
  have hM : MeasurableSet {p : Ω × Ω | p.1 ∈ rowFiber W μ q → W p.1 p.2 = W a p.2} := by
    have heq := measurableSet_eq_fun W.measurable_uncurry
      ((W.measurable_left a).comp measurable_snd)
    convert ((measurableSet_rowFiber W μ q).preimage measurable_fst).compl.union heq using 1
    ext p
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_preimage, Set.mem_setOf_eq,
      Function.uncurry_def, Function.comp_def]
    tauto
  apply (Measure.ae_prod_iff_ae_ae hM).mpr
  exact Eventually.of_forall fun x => by
    by_cases hx : x ∈ rowFiber W μ q
    · have hxa := ((rowFiber_iff W μ q x).mp hx).trans ((rowFiber_iff W μ q a).mp ha).symm
      exact hxa.mono fun y hy _ => hy
    · exact Eventually.of_forall fun _ hh => False.elim (hx hh)

/-- A positive nonzero row class is a clique. No a priori step representation
of the kernel is used. -/
theorem rowFiber_clique (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hbin : ∀ᵐ p : Ω × Ω ∂μ.prod μ, W p.1 p.2 = 0 ∨ W p.1 p.2 = 1)
    (hrows : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, W x y = 1 → W x =ᵐ[μ] W y)
    (q : RowClass W μ) (hm : 0 < μ (rowFiber W μ q))
    (hd : 0 < kernelDegree W μ q.out) :
    ∀ᵐ p : Ω × Ω ∂μ.prod μ,
      p.1 ∈ rowFiber W μ q → p.2 ∈ rowFiber W μ q → W p.1 p.2 = 1 := by
  have hgood := (Measure.ae_ae_of_ae_prod hbin).and hrows
  obtain ⟨a, hac, hba, hra⟩ : ∃ a, a ∈ rowFiber W μ q ∧
      (∀ᵐ z ∂μ, W a z = 0 ∨ W a z = 1) ∧
      (∀ᵐ z ∂μ, W a z = 1 → W a =ᵐ[μ] W z) := by
    by_contra hn
    have hnot : ∀ᵐ x ∂μ, x ∉ rowFiber W μ q := by
      filter_upwards [hgood] with x hx hxc
      exact hn ⟨x, hxc, hx.1, hx.2⟩
    have hm0 : μ (rowFiber W μ q) = 0 := by
      simpa only [ae_iff, not_not, Set.setOf_mem_eq] using hnot
    exact (ne_of_gt hm) hm0
  have hda : 0 < kernelDegree W μ a := by
    rw [degree_eq_of_row_eq W μ ((rowFiber_iff W μ q a).mp hac)]
    exact hd
  have hprofile := rowFiber_common_profile W μ q hac
  have hswap := Measure.ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hprofile)
  obtain ⟨z, haz, hraz, hza⟩ : ∃ z, W a z = 1 ∧ (W a =ᵐ[μ] W z) ∧
      (∀ᵐ x ∂μ, x ∈ rowFiber W μ q → W x z = W a z) := by
    by_contra hn
    have hz : W a =ᵐ[μ] (fun _ => 0) := by
      filter_upwards [hba, hra, hswap] with z hb hr hs
      rcases hb with hb | hb
      · exact hb
      · exact False.elim (hn ⟨z, hb, hr hb, hs⟩)
    exact (ne_of_gt hda) ((degree_zero_iff_row_zero W μ a).mpr hz)
  have haone : ∀ᵐ x ∂μ, x ∈ rowFiber W μ q → W a x = 1 := by
    filter_upwards [hza, hraz] with x hx hr hxc
    rw [hr, ← W.symmetric x z, hx hxc, haz]
  filter_upwards [hprofile, Measure.quasiMeasurePreserving_snd.ae haone] with p hp hy hxC hyC
  exact (hp hxC).trans (hy hyC)

/-- Distinct row classes are anticomplete. -/
theorem rowFibers_anticomplete (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hbin : ∀ᵐ p : Ω × Ω ∂μ.prod μ, W p.1 p.2 = 0 ∨ W p.1 p.2 = 1)
    (hrows : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, W x y = 1 → W x =ᵐ[μ] W y)
    (q q' : RowClass W μ) (hqq : q ≠ q') :
    ∀ᵐ p : Ω × Ω ∂μ.prod μ,
      p.1 ∈ rowFiber W μ q → p.2 ∈ rowFiber W μ q' → W p.1 p.2 = 0 := by
  have hM : MeasurableSet {p : Ω × Ω |
      p.1 ∈ rowFiber W μ q → p.2 ∈ rowFiber W μ q' → W p.1 p.2 = 0} := by
    have heq := measurableSet_eq_fun W.measurable_uncurry (measurable_const (a := (0 : ℝ)))
    convert ((measurableSet_rowFiber W μ q).preimage measurable_fst).compl.union
      (((measurableSet_rowFiber W μ q').preimage measurable_snd).compl.union heq) using 1
    ext p
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_preimage, Set.mem_setOf_eq,
      Function.uncurry_def]
    tauto
  apply (Measure.ae_prod_iff_ae_ae hM).mpr
  filter_upwards [hrows, Measure.ae_ae_of_ae_prod hbin] with x hx hbx
  filter_upwards [hx, hbx] with y hxy hb hxC hyC
  rcases hb with hb | hb
  · exact hb
  · exfalso
    apply hqq
    exact hxC.symm.trans ((Quotient.sound (hxy hb)).trans hyC)


universe u

/-- A countable measurable partition into positive-measure cliques, with no
edges between distinct blocks. The complement of their union is the zero-row
remainder. All kernel assertions are almost-everywhere assertions. -/
structure ClusterPartition {Ω : Type u} [MeasurableSpace Ω]
    (W : Kernel Ω) (μ : Measure Ω) where
  Index : Type u
  countable : Countable Index
  block : Index → Set Ω
  measurable : ∀ i, MeasurableSet (block i)
  positive : ∀ i, 0 < μ (block i)
  disjoint : Pairwise (fun i j => Disjoint (block i) (block j))
  clique : ∀ i, ∀ᵐ p : Ω × Ω ∂μ.prod μ, p.1 ∈ block i → p.2 ∈ block i → W p.1 p.2 = 1
  anticomplete : ∀ i j, i ≠ j → ∀ᵐ p : Ω × Ω ∂μ.prod μ,
    p.1 ∈ block i → p.2 ∈ block j → W p.1 p.2 = 0
  zero_rows : ∀ᵐ p : Ω × Ω ∂μ.prod μ, p.1 ∉ ⋃ i, block i → W p.1 p.2 = 0

/-- Binary kernels whose endpoints of almost every edge have the same row
admit an actual countable measurable clique partition. -/
theorem exists_clusterPartition_of_edge_rows (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (hbin : ∀ᵐ p : Ω × Ω ∂μ.prod μ, W p.1 p.2 = 0 ∨ W p.1 p.2 = 1)
    (hrows : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, W x y = 1 → W x =ᵐ[μ] W y) :
    Nonempty (ClusterPartition W μ) := by
  let J := {q : RowClass W μ // 0 < μ (rowFiber W μ q) ∧ 0 < kernelDegree W μ q.out}
  have hJ : Countable J := (countable_positive_rowFibers W μ).mono (fun _ h => h.1)
  letI : Countable J := hJ
  let C : J → Set Ω := fun i => rowFiber W μ i.val
  have hC (i : J) : MeasurableSet (C i) := measurableSet_rowFiber W μ i.val
  have hU : MeasurableSet (⋃ i, C i) := MeasurableSet.iUnion hC
  have hzero : ∀ᵐ p : Ω × Ω ∂μ.prod μ, p.1 ∉ ⋃ i, C i → W p.1 p.2 = 0 := by
    have hM : MeasurableSet {p : Ω × Ω | p.1 ∉ ⋃ i, C i → W p.1 p.2 = 0} := by
      have heq := measurableSet_eq_fun W.measurable_uncurry (measurable_const (a := (0 : ℝ)))
      convert (hU.preimage measurable_fst).union heq using 1
      ext p
      simp only [Set.mem_union, Set.mem_preimage, Set.mem_setOf_eq, Function.uncurry_def]
      tauto
    apply (Measure.ae_prod_iff_ae_ae hM).mpr
    filter_upwards [Measure.ae_ae_of_ae_prod hbin, hrows] with x hb hr
    by_cases hxU : x ∈ ⋃ i, C i
    · exact Eventually.of_forall fun _ hn => False.elim (hn hxU)
    have hdx : kernelDegree W μ x = 0 := by
      apply le_antisymm _ (kernelDegree_nonneg W μ x)
      by_contra! hd
      let q : RowClass W μ := Quotient.mk (rowSetoid W μ) x
      have hmem : x ∈ rowFiber W μ q := rfl
      have hdq : 0 < kernelDegree W μ q.out := by
        rw [← degree_eq_of_row_eq W μ ((rowFiber_iff W μ q x).mp hmem)]
        exact hd
      let i : J := ⟨q, positive_rowFiber_of_edge_rows W μ x hb hr hd, hdq⟩
      exact hxU (mem_iUnion.mpr ⟨i, hmem⟩)
    exact ((degree_zero_iff_row_zero W μ x).mp hdx).mono fun _ hy _ => hy
  exact ⟨{
    Index := J
    countable := hJ
    block := C
    measurable := hC
    positive := fun i => i.property.1
    disjoint := fun i j hij => rowFibers_disjoint W μ (by
      intro he; exact hij (Subtype.ext he))
    clique := fun i => rowFiber_clique W μ hbin hrows i.val i.property.1 i.property.2
    anticomplete := fun i j hij => rowFibers_anticomplete W μ hbin hrows i.val j.val
      (fun he => hij (Subtype.ext he))
    zero_rows := hzero
  }⟩

/-- The conditionally positive half of the PSD-cluster lemma, with the full
measurable clique partition as conclusion. The ambient hypotheses specialize
to the Lebesgue unit interval used in the manuscript. -/
theorem conditionallyPositive_cluster {Ω : Type*} [MeasurableSpace Ω]
    [MetricSpace Ω] [SecondCountableTopology Ω] [BorelSpace Ω]
    (ν : Measure Ω) [SFinite ν] [IsLocallyFiniteMeasure ν] [IsUnifLocDoublingMeasure ν]
    [Measure.IsOpenPosMeasure ν] {D : Set Ω} (hD : IsOpen D)
    [IsProbabilityMeasure (ν.restrict D)] (W : Kernel Ω)
    (hbin : ∀ᵐ p : Ω × Ω ∂(ν.restrict D).prod (ν.restrict D),
      W p.1 p.2 = 0 ∨ W p.1 p.2 = 1)
    (hpos : IsConditionallyPositive W (ν.restrict D)) :
    Nonempty (ClusterPartition W (ν.restrict D)) :=
  exists_clusterPartition_of_edge_rows W (ν.restrict D) hbin
    (edge_rows_of_three_point W (ν.restrict D) hbin
      (conditionallyPositive_three_point ν W hD hpos))

/-- Positivity on all bounded functions implies the same cluster conclusion. -/
theorem positive_cluster {Ω : Type*} [MeasurableSpace Ω]
    [MetricSpace Ω] [SecondCountableTopology Ω] [BorelSpace Ω]
    (ν : Measure Ω) [SFinite ν] [IsLocallyFiniteMeasure ν] [IsUnifLocDoublingMeasure ν]
    [Measure.IsOpenPosMeasure ν] {D : Set Ω} (hD : IsOpen D)
    [IsProbabilityMeasure (ν.restrict D)] (W : Kernel Ω)
    (hbin : ∀ᵐ p : Ω × Ω ∂(ν.restrict D).prod (ν.restrict D),
      W p.1 p.2 = 0 ∨ W p.1 p.2 = 1)
    (hpos : ∀ f : Lp ℝ 2 (ν.restrict D), f ∈ DensityHS.Analysis.boundedL2 (ν.restrict D) →
      0 ≤ inner ℝ (kernelOperator W (ν.restrict D) f) f) :
    Nonempty (ClusterPartition W (ν.restrict D)) :=
  conditionallyPositive_cluster ν hD W hbin (fun f hf _ => hpos f hf)


/-- The PSD-cluster conclusion on an arbitrary measurable probability region,
including regions defined by cover values. -/
theorem conditionallyPositive_cluster_measurable {Ω : Type*} [MeasurableSpace Ω]
    [MetricSpace Ω] [SecondCountableTopology Ω] [BorelSpace Ω]
    (ν : Measure Ω) [SFinite ν] [IsLocallyFiniteMeasure ν] [IsUnifLocDoublingMeasure ν]
    {D : Set Ω} (hD : MeasurableSet D) [IsProbabilityMeasure (ν.restrict D)] (W : Kernel Ω)
    (hbin : ∀ᵐ p : Ω × Ω ∂(ν.restrict D).prod (ν.restrict D),
      W p.1 p.2 = 0 ∨ W p.1 p.2 = 1)
    (hpos : IsConditionallyPositive W (ν.restrict D)) :
    Nonempty (ClusterPartition W (ν.restrict D)) :=
  exists_clusterPartition_of_edge_rows W (ν.restrict D) hbin
    (edge_rows_of_three_point W (ν.restrict D) hbin
      (conditionallyPositive_three_point_measurable ν W hD hpos))

/-- The full PSD-cluster lemma on a normalized arbitrary measurable set of
finite positive measure. In particular this applies to `{c > 0}` and `{c = 0}`
in the equality reductions. -/
theorem conditionallyPositive_cluster_cond {Ω : Type*} [MeasurableSpace Ω]
    [MetricSpace Ω] [SecondCountableTopology Ω] [BorelSpace Ω]
    (ν : Measure Ω) [SFinite ν] [IsLocallyFiniteMeasure ν] [IsUnifLocDoublingMeasure ν]
    {D : Set Ω} (hD : MeasurableSet D) (hD0 : ν D ≠ 0) (hDtop : ν D ≠ ∞)
    (W : Kernel Ω)
    (hbin : ∀ᵐ p : Ω × Ω ∂(ProbabilityTheory.cond ν D).prod (ProbabilityTheory.cond ν D),
      W p.1 p.2 = 0 ∨ W p.1 p.2 = 1)
    (hpos : letI := ProbabilityTheory.cond_isProbabilityMeasure_of_finite hD0 hDtop
      IsConditionallyPositive W (ProbabilityTheory.cond ν D)) :
    Nonempty (ClusterPartition W (ProbabilityTheory.cond ν D)) := by
  let c : ℝ≥0 := (ν D).toNNReal⁻¹
  let ν' : Measure Ω := c • ν
  have hc : (c : ℝ≥0∞) = (ν D)⁻¹ := by
    dsimp [c]
    rw [← ENNReal.toNNReal_inv, ENNReal.coe_toNNReal (ENNReal.inv_ne_top.mpr hD0)]
  have he : ν'.restrict D = ProbabilityTheory.cond ν D := by
    change ((c : ℝ≥0∞) • ν).restrict D = _
    rw [hc, Measure.restrict_smul]
    rfl
  letI : IsUnifLocDoublingMeasure ν' := isUnifLocDoublingMeasure_nnreal_smul ν c
  letI : IsProbabilityMeasure (ProbabilityTheory.cond ν D) :=
    ProbabilityTheory.cond_isProbabilityMeasure_of_finite hD0 hDtop
  letI : IsProbabilityMeasure (ν'.restrict D) := by rw [he]; infer_instance
  have hb' : ∀ᵐ p : Ω × Ω ∂(ν'.restrict D).prod (ν'.restrict D),
      W p.1 p.2 = 0 ∨ W p.1 p.2 = 1 := by simpa only [he] using hbin
  have hp' : IsConditionallyPositive W (ν'.restrict D) := by simpa only [he] using hpos
  have h := conditionallyPositive_cluster_measurable ν' hD W hb' hp'
  simpa only [he] using h

end DensityHS.Graphon
