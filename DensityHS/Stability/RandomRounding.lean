module

public import DensityHS.Graphon.FiniteModels
public import DensityHS.Graphon.BlockCovers
public import DensityHS.Graphon.Pullback
public import DensityHS.Rainbow.AbsorberSelection
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.MeasureTheory.Integral.Average

/-!
# Independent rounding with simultaneous size control

Author and maintainer: Xizhi Liu.

A single expectation controls the disagreement cost and the sum of squared
part-size errors. This elementary second-moment argument is sufficient for
the finite edit-distance transfer and avoids an additional tail inequality.
-/

@[expose] public section

namespace DensityHS.Stability

open MeasureTheory ProbabilityTheory Finset Fintype Filter
open scoped BigOperators ENNReal

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I] [MeasurableSpace I] [MeasurableSingletonClass I]

/-- The actual probability law associated to a finite real weight vector. -/
noncomputable def weightPMF (p : I → ℝ) (hp : IsProbabilityWeight p) : PMF I :=
  PMF.ofFintype (fun i => ENNReal.ofReal (p i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hp.1 i),hp.2]
    simp)

theorem weightPMF_real_singleton (p : I → ℝ) (hp : IsProbabilityWeight p) (i : I) :
    (weightPMF p hp).toMeasure.real {i} = p i := by
  rw [Measure.real,PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton i)]
  exact ENNReal.toReal_ofReal (hp.1 i)

theorem integral_weightPMF (p : I → ℝ) (hp : IsProbabilityWeight p) (f : I → ℝ) :
    (∫ i, f i ∂(weightPMF p hp).toMeasure) = ∑ i, p i*f i := by
  rw [PMF.integral_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [weightPMF,PMF.ofFintype_apply,ENNReal.toReal_ofReal (hp.1 i),smul_eq_mul]

noncomputable def assignmentMeasure (p : V → I → ℝ) (hp : ∀ v, IsProbabilityWeight (p v)) :
    Measure (V → I) := Measure.pi (fun v => (weightPMF (p v) (hp v)).toMeasure)

instance (p : V → I → ℝ) (hp : ∀ v, IsProbabilityWeight (p v)) :
    IsProbabilityMeasure (assignmentMeasure p hp) := by
  unfold assignmentMeasure
  infer_instance

theorem integral_assignment_coordinate (p : V → I → ℝ) (hp : ∀ v, IsProbabilityWeight (p v))
    (v : V) (f : I → ℝ) :
    (∫ ω, f (ω v) ∂assignmentMeasure p hp) = ∑ i, p v i*f i := by
  unfold assignmentMeasure
  rw [integral_comp_eval (measurable_of_finite f).aestronglyMeasurable,integral_weightPMF]

theorem integral_assignment_pair (p : V → I → ℝ) (hp : ∀ v, IsProbabilityWeight (p v))
    {u v : V} (huv : u ≠ v) (F : I → I → ℝ) :
    (∫ ω, F (ω u) (ω v) ∂assignmentMeasure p hp) =
      ∑ i, ∑ j, p u i*p v j*F i j := by
  have hm := Graphon.measurePreserving_pair_coordinates
    (fun v => (weightPMF (p v) (hp v)).toMeasure) huv
  have h := Graphon.integral_comap_measurable hm
    (measurable_of_finite (fun z : I × I => F z.1 z.2))
  change (∫ ω, F (ω u) (ω v) ∂assignmentMeasure p hp) = _ at h
  apply h.trans
  apply (Graphon.integral_finite_pair_labels _ _ id measurable_id id measurable_id F).trans
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hi : {x : I | id x = i} = {i} := by ext x; rfl
  have hj : {x : I | id x = j} = {j} := by ext x; rfl
  rw [hi,hj,weightPMF_real_singleton,weightPMF_real_singleton]

def assignmentCoin (i j : I) : ℝ := if j=i then 1 else 0

theorem assignmentCoin_sq (i j : I) : (assignmentCoin i j)^2 = assignmentCoin i j := by
  unfold assignmentCoin
  split_ifs <;> norm_num

theorem integral_assignmentCoin (p : V → I → ℝ) (hp : ∀ v, IsProbabilityWeight (p v))
    (v : V) (i : I) :
    (∫ ω, assignmentCoin i (ω v) ∂assignmentMeasure p hp) = p v i := by
  rw [integral_assignment_coordinate]
  simp [assignmentCoin,mul_ite]

theorem integral_assignment_center (p : V → I → ℝ) (hp : ∀ v, IsProbabilityWeight (p v))
    (v : V) (i : I) :
    (∫ ω, (assignmentCoin i (ω v)-p v i) ∂assignmentMeasure p hp) = 0 := by
  rw [integral_sub (Rainbow.integrable_finite_function _ _) (integrable_const _),
    integral_assignmentCoin]
  simp

theorem integral_assignment_center_sq (p : V → I → ℝ) (hp : ∀ v, IsProbabilityWeight (p v))
    (v : V) (i : I) :
    (∫ ω, (assignmentCoin i (ω v)-p v i)^2 ∂assignmentMeasure p hp) =
      p v i-(p v i)^2 := by
  have heq (ω : V → I) : (assignmentCoin i (ω v)-p v i)^2 =
      assignmentCoin i (ω v)-2*p v i*assignmentCoin i (ω v)+(p v i)^2 := by
    nlinarith only [assignmentCoin_sq i (ω v)]
  simp_rw [heq]
  rw [integral_add (Rainbow.integrable_finite_function _ _) (integrable_const _),
    integral_sub (Rainbow.integrable_finite_function _ _) (Rainbow.integrable_finite_function _ _),
    integral_const_mul,integral_assignmentCoin]
  simp
  ring

theorem integral_assignment_center_mul (p : V → I → ℝ) (hp : ∀ v, IsProbabilityWeight (p v))
    {u v : V} (huv : u ≠ v) (i : I) :
    (∫ ω, (assignmentCoin i (ω u)-p u i)*(assignmentCoin i (ω v)-p v i)
      ∂assignmentMeasure p hp) = 0 := by
  have hind : iIndepFun
      (fun v (ω : V → I) => assignmentCoin i (ω v)-p v i) (assignmentMeasure p hp) :=
    iIndepFun_pi (fun v => (measurable_of_finite
      (fun j => assignmentCoin i j-p v i)).aemeasurable)
  rw [(hind.indepFun huv).integral_fun_mul_eq_mul_integral
    (measurable_of_finite _).aestronglyMeasurable (measurable_of_finite _).aestronglyMeasurable,
    integral_assignment_center,integral_assignment_center,zero_mul]

noncomputable def partCount (ω : V → I) (i : I) : ℝ := ∑ v, assignmentCoin i (ω v)

noncomputable def expectedPartSize (p : V → I → ℝ) (i : I) : ℝ := ∑ v, p v i

theorem integral_part_error_sq (p : V → I → ℝ) (hp : ∀ v, IsProbabilityWeight (p v)) (i : I) :
    (∫ ω, (partCount ω i-expectedPartSize p i)^2 ∂assignmentMeasure p hp) =
      ∑ v, (p v i-(p v i)^2) := by
  have heq (ω : V → I) : (partCount ω i-expectedPartSize p i)^2 =
      ∑ u, ∑ v, (assignmentCoin i (ω u)-p u i)*(assignmentCoin i (ω v)-p v i) := by
    simp only [partCount,expectedPartSize,← Finset.sum_sub_distrib,← Finset.sum_mul_sum,pow_two]
  simp_rw [heq]
  rw [integral_finsetSum _ (fun _ _ => Rainbow.integrable_finite_function _ _)]
  apply Finset.sum_congr rfl
  intro u _
  rw [integral_finsetSum _ (fun _ _ => Rainbow.integrable_finite_function _ _)]
  rw [Finset.sum_eq_single u]
  · simpa only [← pow_two] using integral_assignment_center_sq p hp u i
  · intro v _ hv
    exact integral_assignment_center_mul p hp (Ne.symm hv) i
  · simp

noncomputable def partSquareError (p : V → I → ℝ) (ω : V → I) : ℝ :=
  ∑ i, (partCount ω i-expectedPartSize p i)^2

theorem partSquareError_nonneg (p : V → I → ℝ) (ω : V → I) : 0 ≤ partSquareError p ω :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem integral_partSquareError_le (p : V → I → ℝ) (hp : ∀ v, IsProbabilityWeight (p v)) :
    (∫ ω, partSquareError p ω ∂assignmentMeasure p hp) ≤ Fintype.card V := by
  unfold partSquareError
  rw [integral_finsetSum _ (fun _ _ => Rainbow.integrable_finite_function _ _)]
  simp_rw [integral_part_error_sq]
  calc
    _ ≤ ∑ i, ∑ v, p v i := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_le_sum (fun v _ => sub_le_self _ (sq_nonneg _))
    _ = _ := by rw [Finset.sum_comm]; simp only [fun v => (hp v).2]; simp

noncomputable def assignmentCost (C : V → V → I → I → ℝ) (ω : V → I) : ℝ :=
  ∑ u, ∑ v, if u=v then 0 else C u v (ω u) (ω v)

noncomputable def expectedCostBound (p : V → I → ℝ) (C : V → V → I → I → ℝ) : ℝ :=
  ∑ u, ∑ v, ∑ i, ∑ j, p u i*p v j*C u v i j

theorem assignmentCost_nonneg {C : V → V → I → I → ℝ}
    (hC : ∀ u v i j, 0 ≤ C u v i j) (ω : V → I) : 0 ≤ assignmentCost C ω := by
  apply Finset.sum_nonneg
  intro u _
  apply Finset.sum_nonneg
  intro v _
  split_ifs
  · rfl
  · exact hC _ _ _ _

theorem integral_assignmentCost_le (p : V → I → ℝ) (hp : ∀ v, IsProbabilityWeight (p v))
    (C : V → V → I → I → ℝ) (hC : ∀ u v i j, 0 ≤ C u v i j) :
    (∫ ω, assignmentCost C ω ∂assignmentMeasure p hp) ≤ expectedCostBound p C := by
  unfold assignmentCost expectedCostBound
  rw [integral_finsetSum _ (fun _ _ => Rainbow.integrable_finite_function _ _)]
  apply Finset.sum_le_sum
  intro u _
  rw [integral_finsetSum _ (fun _ _ => Rainbow.integrable_finite_function _ _)]
  apply Finset.sum_le_sum
  intro v _
  by_cases huv : u=v
  · simp only [huv,ite_true,integral_zero]
    apply Finset.sum_nonneg
    intro i _
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (mul_nonneg ((hp _).1 _) ((hp _).1 _)) (hC _ _ _ _))
  · simp only [huv,ite_false]
    exact (integral_assignment_pair p hp huv (C u v)).le

/-- Actual independent rounding, simultaneously controlling pair cost and
the total squared part-size error. -/
theorem exists_assignment_with_cost_and_sizes
    (p : V → I → ℝ) (hp : ∀ v, IsProbabilityWeight (p v))
    (C : V → V → I → I → ℝ) (hC : ∀ u v i j, 0 ≤ C u v i j) :
    ∃ ω : V → I,
      assignmentCost C ω+partSquareError p ω ≤ expectedCostBound p C+Fintype.card V := by
  obtain ⟨ω,hω⟩ := exists_le_integral (μ := assignmentMeasure p hp)
    (Rainbow.integrable_finite_function (assignmentMeasure p hp)
      (fun ω => assignmentCost C ω+partSquareError p ω))
  refine ⟨ω,hω.trans ?_⟩
  rw [integral_add (Rainbow.integrable_finite_function _ _) (Rainbow.integrable_finite_function _ _)]
  exact add_le_add (integral_assignmentCost_le p hp C hC) (integral_partSquareError_le p hp)

end DensityHS.Stability
