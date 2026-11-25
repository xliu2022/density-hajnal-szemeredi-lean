module

public import DensityHS.Graphon.MetricDensity
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Concrete interval step kernels

Author and maintainer: Xizhi Liu.

The common probability space is the real unit interval, with its restricted
Lebesgue measure. A finite symmetric matrix is evaluated on the rank labels
of a finite list of cuts. Moving the cuts changes the kernel only on the
corresponding vertical and horizontal strips.
-/

@[expose] public section

namespace DensityHS.Constructions

open MeasureTheory Set Filter
open scoped ENNReal

/-- Lebesgue probability measure on the real unit interval. -/
noncomputable def unitMeasure : Measure ℝ := volume.restrict (Ioc 0 1)

instance : IsProbabilityMeasure unitMeasure := by
  refine ⟨?_⟩
  simp [unitMeasure]

instance : NullSingletonClass unitMeasure := by
  dsimp [unitMeasure]
  infer_instance

/-- A bounded symmetric finite template, including allowed diagonal ones. -/
structure StepPattern (n : ℕ) where
  entry : Fin (n + 1) → Fin (n + 1) → ℝ
  symmetric : ∀ i j, entry i j = entry j i
  nonneg : ∀ i j, 0 ≤ entry i j
  le_one : ∀ i j, entry i j ≤ 1

/-- The rank of a point among the cuts. Equal cuts simply give empty cells. -/
noncomputable def cutLabel {n : ℕ} (cuts : Fin n → ℝ) (x : ℝ) : Fin (n + 1) := by
  classical
  exact ⟨(Finset.univ.filter (fun j => cuts j < x)).card, by
    have h := Finset.card_filter_le (s := (Finset.univ : Finset (Fin n))) (p := fun j => cuts j < x)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    omega⟩

theorem measurable_cutLabel {n : ℕ} (cuts : Fin n → ℝ) : Measurable (cutLabel cuts) := by
  classical
  have hcount : Measurable (fun x : ℝ => (Finset.univ.filter (fun j => cuts j < x)).card) := by
    simp only [Finset.card_filter]
    exact Finset.measurable_sum _ (fun j _ =>
      Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const measurable_const)
  apply measurable_to_countable'
  intro i
  have heq : (cutLabel cuts) ⁻¹' {i} =
      {x : ℝ | (Finset.univ.filter (fun j => cuts j < x)).card = i.val} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq, cutLabel, Fin.ext_iff]
  rw [heq]
  exact measurableSet_eq_fun hcount measurable_const

/-- Evaluate a fixed finite template on interval labels. -/
noncomputable def StepPattern.kernel {n : ℕ} (A : StepPattern n) (cuts : Fin n → ℝ) :
    Graphon.Kernel ℝ where
  toFun x y := A.entry (cutLabel cuts x) (cutLabel cuts y)
  measurable_uncurry := by
    exact (measurable_of_finite (fun z : Fin (n + 1) × Fin (n + 1) => A.entry z.1 z.2)).comp
      ((measurable_cutLabel cuts).comp measurable_fst |>.prodMk
        ((measurable_cutLabel cuts).comp measurable_snd))
  symmetric x y := A.symmetric _ _
  nonneg x y := A.nonneg _ _
  le_one x y := A.le_one _ _

/-- The strips on which at least one cut can change a vertex label. -/
def cutChangeSet {n : ℕ} (c d : Fin n → ℝ) : Set ℝ :=
  ⋃ j, Ioc (min (c j) (d j)) (max (c j) (d j))

theorem measurable_cutChangeSet {n : ℕ} (c d : Fin n → ℝ) :
    MeasurableSet (cutChangeSet c d) := MeasurableSet.iUnion fun _ => measurableSet_Ioc

theorem cutLabel_eq_off_change {n : ℕ} (c d : Fin n → ℝ) {x : ℝ}
    (hx : x ∉ cutChangeSet c d) : cutLabel c x = cutLabel d x := by
  classical
  apply Fin.ext
  change (Finset.univ.filter (fun j => c j < x)).card =
    (Finset.univ.filter (fun j => d j < x)).card
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hj : x ∉ Ioc (min (c j) (d j)) (max (c j) (d j)) :=
    fun h => hx (mem_iUnion.mpr ⟨j, h⟩)
  constructor
  · intro hcx
    by_contra hdx
    apply hj
    exact ⟨lt_of_le_of_lt (min_le_left _ _) hcx,
      (le_of_not_gt hdx).trans (le_max_right _ _)⟩
  · intro hdx
    by_contra hcx
    apply hj
    exact ⟨lt_of_le_of_lt (min_le_right _ _) hdx,
      (le_of_not_gt hcx).trans (le_max_left _ _)⟩

theorem unitMeasure_real_interval_le (a b : ℝ) :
    unitMeasure.real (Ioc (min a b) (max a b)) ≤ |a - b| := by
  have h := (Measure.restrict_le_self (μ := (volume : Measure ℝ)) (s := Ioc 0 1))
    (Ioc (min a b) (max a b))
  have htop : (volume : Measure ℝ) (Ioc (min a b) (max a b)) ≠ ∞ := by simp
  have hreal := ENNReal.toReal_mono htop h
  change unitMeasure.real _ ≤ (volume : Measure ℝ).real _ at hreal
  rw [Real.volume_real_Ioc_of_le min_le_max, max_sub_min_eq_abs, abs_sub_comm] at hreal
  exact hreal

theorem measure_cutChangeSet_le {n : ℕ} (c d : Fin n → ℝ) :
    unitMeasure.real (cutChangeSet c d) ≤ ∑ j, |c j - d j| := by
  exact (measureReal_iUnion_fintype_le _).trans
    (Finset.sum_le_sum fun j _ => unitMeasure_real_interval_le (c j) (d j))

/-- Agreement outside a vertex set changes at most its vertical and
horizontal strips. -/
theorem kernelL1_le_two_measure_of_agree_off {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W U : Graphon.Kernel Ω)
    (B : Set Ω) (hB : MeasurableSet B)
    (heq : ∀ x ∉ B, ∀ y ∉ B, W x y = U x y) :
    Graphon.kernelL1Distance μ W U ≤ 2 * μ.real B := by
  let E := (B ×ˢ Set.univ) ∪ (Set.univ ×ˢ B)
  have hE : MeasurableSet E := (hB.prod MeasurableSet.univ).union (MeasurableSet.univ.prod hB)
  have hbound : ∀ z : Ω × Ω, |W z.1 z.2 - U z.1 z.2| ≤ E.indicator (fun _ => (1 : ℝ)) z := by
    intro z
    classical
    by_cases hz : z ∈ E
    · rw [Set.indicator_of_mem hz]
      exact Graphon.kernel_diff_abs_le_one W U z
    · have hzx : z.1 ∉ B := fun hx => hz (Or.inl ⟨hx, Set.mem_univ _⟩)
      have hzy : z.2 ∉ B := fun hy => hz (Or.inr ⟨Set.mem_univ _, hy⟩)
      rw [heq z.1 hzx z.2 hzy, sub_self, abs_zero, Set.indicator_of_notMem hz]
  calc
    Graphon.kernelL1Distance μ W U ≤ ∫ z, E.indicator (fun _ => (1 : ℝ)) z ∂μ.prod μ :=
      integral_mono (Graphon.kernel_diff_abs_integrable μ W U)
        ((integrable_const (1 : ℝ)).indicator hE) hbound
    _ = (μ.prod μ).real E := by rw [integral_indicator hE, setIntegral_const]; simp
    _ ≤ (μ.prod μ).real (B ×ˢ Set.univ) + (μ.prod μ).real (Set.univ ×ˢ B) :=
      measureReal_union_le _ _
    _ = 2 * μ.real B := by rw [measureReal_prod_prod, measureReal_prod_prod]; simp; ring

/-- A quantitative continuity bound for actual interval step kernels. -/
theorem StepPattern.kernelL1_le {n : ℕ} (A : StepPattern n) (c d : Fin n → ℝ) :
    Graphon.kernelL1Distance unitMeasure (A.kernel c) (A.kernel d) ≤ 2 * ∑ j, |c j - d j| := by
  have h := kernelL1_le_two_measure_of_agree_off unitMeasure (A.kernel c) (A.kernel d)
    (cutChangeSet c d) (measurable_cutChangeSet c d) (by
      intro x hx y hy
      change A.entry (cutLabel c x) (cutLabel c y) = A.entry (cutLabel d x) (cutLabel d y)
      rw [cutLabel_eq_off_change c d hx, cutLabel_eq_off_change c d hy])
  exact h.trans (mul_le_mul_of_nonneg_left (measure_cutChangeSet_le c d) (by norm_num))

/-- The concrete interval kernel in the actual compact graphon quotient. -/
noncomputable def StepPattern.graphon {n : ℕ} (A : StepPattern n) (cuts : Fin n → ℝ) :
    Vendor.GraphonSpace ℝ unitMeasure :=
  Vendor.GraphonSpace.mk ((A.kernel cuts).toVendorGraphon unitMeasure)

theorem StepPattern.dist_graphon_le {n : ℕ} (A : StepPattern n) (c d : Fin n → ℝ) :
    dist (A.graphon c) (A.graphon d) ≤ 2 * ∑ j, |c j - d j| := by
  change Vendor.Graphon.cutDistance ((A.kernel c).toVendorGraphon unitMeasure)
    ((A.kernel d).toVendorGraphon unitMeasure) ≤ _
  apply (Vendor.Graphon.cutDistance_le_cutNormDiff _ _).trans
  rw [Graphon.cutNormDiff_toVendorGraphon]
  exact (Graphon.kernelCutDistance_le_L1 unitMeasure _ _).trans (A.kernelL1_le c d)

theorem StepPattern.lipschitz_graphon {n : ℕ} (A : StepPattern n) :
    LipschitzWith (2 * n) A.graphon := by
  apply LipschitzWith.of_dist_le_mul
  intro c d
  apply (A.dist_graphon_le c d).trans
  have hs : (∑ j, |c j - d j|) ≤ (n : ℝ) * dist c d := by
    calc
      _ ≤ ∑ _j : Fin n, dist c d := Finset.sum_le_sum fun j _ => by
        simpa only [Real.dist_eq] using dist_le_pi_dist c d j
      _ = _ := by simp
  have h := mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_natCast, mul_assoc] using h

theorem StepPattern.continuous_graphon {n : ℕ} (A : StepPattern n) : Continuous A.graphon :=
  A.lipschitz_graphon.continuous

end DensityHS.Constructions
