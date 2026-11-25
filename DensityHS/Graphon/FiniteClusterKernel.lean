module

public import DensityHS.Graphon.ClusterMasses
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Finite cluster kernels and equality in the defect bound

Author and maintainer: Xizhi Liu.

The kernel of finitely many actual cluster blocks lies below the original
cluster kernel. Its density is the sum of squared block masses divided by two.
Equality of densities removes every other edge almost everywhere.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set Filter
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The disjoint union of cliques on a finite list of measurable sets. -/
noncomputable def finiteClusterKernel {I : Type*} (C : I → Set Ω)
    (hC : ∀ i, MeasurableSet (C i)) (F : Finset I) : Kernel Ω where
  toFun x y := (⋃ i ∈ F, C i ×ˢ C i).indicator (fun _ => (1 : ℝ)) (x, y)
  measurable_uncurry := by
    simpa only [Function.uncurry_def] using measurable_const.indicator
      (Finset.measurableSet_biUnion F (fun i _ => (hC i).prod (hC i)))
  symmetric x y := by
    classical
    have he : (x, y) ∈ (⋃ i ∈ F, C i ×ˢ C i) ↔ (y, x) ∈ (⋃ i ∈ F, C i ×ˢ C i) := by
      simp only [mem_iUnion, mem_prod]
      constructor <;> rintro ⟨i, hi, hx, hy⟩ <;> exact ⟨i, hi, hy, hx⟩
    by_cases h : (x, y) ∈ (⋃ i ∈ F, C i ×ˢ C i)
    · simp [h, he.mp h]
    · simp [h, mt he.mpr h]
  nonneg x y := by
    classical
    by_cases h : (x, y) ∈ (⋃ i ∈ F, C i ×ˢ C i) <;> simp [h]
  le_one x y := by
    classical
    by_cases h : (x, y) ∈ (⋃ i ∈ F, C i ×ˢ C i) <;> simp [h]

theorem density_finiteClusterKernel {I : Type*} (μ : Measure Ω) [IsFiniteMeasure μ]
    (C : I → Set Ω) (hC : ∀ i, MeasurableSet (C i))
    (hdisj : Pairwise fun i j => Disjoint (C i) (C j)) (F : Finset I) :
    density μ (finiteClusterKernel C hC F) = (∑ i ∈ F, (μ.real (C i)) ^ 2) / 2 := by
  have hm : MeasurableSet (⋃ i ∈ F, C i ×ˢ C i) :=
    Finset.measurableSet_biUnion F (fun i _ => (hC i).prod (hC i))
  have hd : Set.PairwiseDisjoint (F : Set I) (fun i => C i ×ˢ C i) := by
    intro i _ j _ hij
    exact Set.disjoint_left.mpr fun z hzi hzj => Set.disjoint_left.mp (hdisj hij) hzi.1 hzj.1
  rw [density_eq_prod_integral]
  change (∫ z, (⋃ i ∈ F, C i ×ˢ C i).indicator (fun _ => (1 : ℝ)) z ∂μ.prod μ) / 2 = _
  rw [integral_indicator hm, setIntegral_const, smul_eq_mul, mul_one,
    measureReal_biUnion_finset hd (fun i _ => (hC i).prod (hC i))]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [measureReal_prod_prod]
  ring

theorem density_complement (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    density μ W.complement = 1 / 2 - density μ W := by
  rw [density_eq_prod_integral, density_eq_prod_integral]
  change (∫ z : Ω × Ω, 1 - W z.1 z.2 ∂μ.prod μ) / 2 = _
  have hW : Integrable (fun z : Ω × Ω => W z.1 z.2) (μ.prod μ) := by
    simpa only [Function.uncurry_def] using W.integrable μ
  rw [integral_sub (integrable_const _) hW]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, Function.uncurry_def]
  ring

universe u
variable {Ω : Type u} [MeasurableSpace Ω] {W : Kernel Ω} {μ : Measure Ω}

namespace ClusterPartition

theorem finiteKernel_le (P : ClusterPartition W μ) (F : Finset P.Index) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      finiteClusterKernel P.block P.measurable F z.1 z.2 ≤ W z.1 z.2 := by
  letI := P.countable
  have hall : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ∀ i,
      z.1 ∈ P.block i → z.2 ∈ P.block i → W z.1 z.2 = 1 := ae_all_iff.mpr P.clique
  filter_upwards [hall] with z hz
  classical
  by_cases h : z ∈ (⋃ i ∈ F, P.block i ×ˢ P.block i)
  · obtain ⟨i, hi, hzi, hzj⟩ := by simpa only [mem_iUnion, mem_prod] using h
    rw [hz i hzi hzj]
    simp [finiteClusterKernel, h]
  · simpa [finiteClusterKernel, h] using W.nonneg z.1 z.2

theorem sum_mass_sq_le [IsFiniteMeasure μ] (P : ClusterPartition W μ) (F : Finset P.Index) :
    (∑ i ∈ F, P.mass i ^ 2) ≤ 2 * density μ W := by
  have h := density_le_of_ae_le (P.finiteKernel_le F)
  rw [density_finiteClusterKernel μ P.block P.measurable P.disjoint F] at h
  change (∑ i ∈ F, P.mass i ^ 2) / 2 ≤ density μ W at h
  linarith

theorem eq_finiteKernel_of_sum_mass_sq_eq [IsFiniteMeasure μ]
    (P : ClusterPartition W μ) (F : Finset P.Index)
    (he : (∑ i ∈ F, P.mass i ^ 2) = 2 * density μ W) :
    (fun z : Ω × Ω => W z.1 z.2) =ᵐ[μ.prod μ]
      (fun z => finiteClusterKernel P.block P.measurable F z.1 z.2) := by
  apply Filter.EventuallyEq.symm
  apply ae_eq_of_ae_le_of_density_eq (P.finiteKernel_le F)
  rw [density_finiteClusterKernel μ P.block P.measurable P.disjoint F]
  change (∑ i ∈ F, P.mass i ^ 2) / 2 = density μ W
  rw [he]
  ring

end ClusterPartition

/-- Equality in the finite variance inequality makes all masses equal. -/
theorem equal_of_sum_sq_eq {I : Type*} (F : Finset I) (p : I → ℝ) (a : ℝ)
    (hs : (∑ i ∈ F, p i) = (F.card : ℝ) * a)
    (hsq : (∑ i ∈ F, p i ^ 2) = (F.card : ℝ) * a ^ 2) :
    ∀ i ∈ F, p i = a := by
  have hv : (∑ i ∈ F, (p i - a) ^ 2) = 0 := by
    calc
      _ = (∑ i ∈ F, p i ^ 2) - 2 * a * (∑ i ∈ F, p i) + (F.card : ℝ) * a ^ 2 := by
        have hex : ∀ i, (p i - a) ^ 2 = p i ^ 2 - (2 * a) * p i + a ^ 2 := by
          intro i
          ring
        simp only [hex, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      _ = 0 := by rw [hs, hsq]; ring
  intro i hi
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ F) => sq_nonneg (p i - a))).mp hv i hi
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hzero)

end DensityHS.Graphon
