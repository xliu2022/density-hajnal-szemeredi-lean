module

public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Tactic

/-!
# Finite sampling moments

Author and maintainer: Xizhi Liu.

Finite product samples approximate the cost of a bounded measurable cover and
its kernel density simultaneously. Only the variance of an ordinary empirical
mean is needed; a quadratic penalty selects a sample with both properties.
-/

@[expose] public section

namespace DensityHS.Graphon

open Finset MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- The probability measure on an ordered finite sample. -/
noncomputable def sampleMeasure (n : ℕ) : Measure (Fin n → Ω) :=
  Measure.pi (fun _ => μ)

instance sampleMeasure_isProbability (n : ℕ) : IsProbabilityMeasure (sampleMeasure μ n) := by
  unfold sampleMeasure
  infer_instance

/-- The empirical average of a function on a finite sample. -/
noncomputable def sampleMean (n : ℕ) (f : Ω → ℝ) (ω : Fin n → Ω) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, f (ω i)

/-- The kernel contribution from distinct sampled indices, with each
unordered pair counted once. -/
noncomputable def samplePairDensity (n : ℕ) (W : Ω → Ω → ℝ) (ω : Fin n → Ω) : ℝ :=
  (n : ℝ)⁻¹ ^ 2 * (∑ i, ∑ j, if i = j then 0 else W (ω i) (ω j)) / 2

variable {μ}

theorem measurable_sampleMean {f : Ω → ℝ} (hf : Measurable f) (n : ℕ) :
    Measurable (sampleMean n f) := by
  unfold sampleMean
  fun_prop

theorem sampleMean_mem_Icc {f : Ω → ℝ} (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    {n : ℕ} (hn : 0 < n) (ω : Fin n → Ω) :
    sampleMean n f ω ∈ Set.Icc (0 : ℝ) 1 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsum : (∑ i, f (ω i)) ≤ (n : ℝ) := by
    calc
      (∑ i, f (ω i)) ≤ ∑ _ : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum (fun i _ => (hf (ω i)).2)
      _ = n := by simp
  constructor
  · exact mul_nonneg (inv_nonneg.mpr hnR.le) (Finset.sum_nonneg (fun i _ => (hf (ω i)).1))
  · unfold sampleMean
    calc
      (n : ℝ)⁻¹ * ∑ i, f (ω i) ≤ (n : ℝ)⁻¹ * n :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hnR.le)
      _ = 1 := inv_mul_cancel₀ hnR.ne'

theorem memLp_sampleMean {f : Ω → ℝ} (hf : Measurable f)
    (hbound : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) {n : ℕ} (hn : 0 < n) :
    MemLp (sampleMean n f) 2 (sampleMeasure μ n) :=
  memLp_of_bounded (ae_of_all _ (sampleMean_mem_Icc hbound hn))
    (measurable_sampleMean hf n).aestronglyMeasurable 2

theorem integral_sampleMean {f : Ω → ℝ} (hf : Integrable f μ)
    {n : ℕ} (hn : 0 < n) :
    (∫ ω, sampleMean n f ω ∂sampleMeasure μ n) = ∫ x, f x ∂μ := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold sampleMean sampleMeasure
  rw [integral_const_mul, integral_finsetSum]
  · have he : ∀ i : Fin n,
        (∫ ω : Fin n → Ω, f (ω i) ∂Measure.pi (fun _ => μ)) = ∫ x, f x ∂μ :=
      fun i => integral_comp_eval (μ := fun _ : Fin n => μ) (i := i) hf.aestronglyMeasurable
    simp only [he, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ hnR, one_mul]
  · intro i _
    exact integrable_comp_eval hf

theorem variance_sampleMean {f : Ω → ℝ} (hf : MemLp f 2 μ) {n : ℕ} (hn : 0 < n) :
    variance (sampleMean n f) (sampleMeasure μ n) = variance f μ / n := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have heq : (fun ω : Fin n → Ω => ∑ i, f (ω i)) = ∑ i : Fin n, fun ω => f (ω i) := by
    ext ω
    simp
  unfold sampleMean sampleMeasure
  rw [variance_const_mul, heq, variance_sum_pi (fun _ => hf)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem mean_square_sampleMean_le {f : Ω → ℝ} (hf : Measurable f)
    (hbound : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) {n : ℕ} (hn : 0 < n) :
    (∫ ω, (sampleMean n f ω - ∫ x, f x ∂μ) ^ 2 ∂sampleMeasure μ n) ≤ 1 / (4 * n) := by
  have hfLp : MemLp f 2 μ := memLp_of_bounded (ae_of_all _ hbound) hf.aestronglyMeasurable 2
  have hv := variance_eq_integral (μ := sampleMeasure μ n)
    (measurable_sampleMean hf n).aemeasurable
  rw [integral_sampleMean (hfLp.integrable (by norm_num)) hn] at hv
  rw [← hv, variance_sampleMean hfLp hn]
  have hvar : variance f μ ≤ (1 / 4 : ℝ) := by
    have h := variance_le_sq_of_bounded (ae_of_all μ hbound) hf.aemeasurable
    norm_num at h ⊢
    exact h
  have hnR : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  calc
    variance f μ / n ≤ (1 / 4 : ℝ) / n := div_le_div_of_nonneg_right hvar hnR
    _ = 1 / (4 * n) := by ring

/-- Two distinct sample coordinates have the original product distribution. -/
theorem sampleMeasure_map_pair {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    (sampleMeasure μ n).map (fun ω => (ω i, ω j)) = μ.prod μ := by
  have hind : iIndepFun (fun i : Fin n => fun ω : Fin n → Ω => ω i)
      (Measure.pi (fun _ => μ)) :=
    iIndepFun_pi (fun _ => aemeasurable_id)
  have h := (hind.indepFun hij).map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
  simpa only [sampleMeasure, (measurePreserving_eval (fun _ : Fin n => μ) i).map_eq,
    (measurePreserving_eval (fun _ : Fin n => μ) j).map_eq] using h

/-- Integrating a function of two distinct sample coordinates is the same as
integrating against the original product measure. -/
theorem integral_sample_pair {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {W : Ω → Ω → ℝ} (hW : Measurable (Function.uncurry W)) :
    (∫ ω, W (ω i) (ω j) ∂sampleMeasure μ n) =
      ∫ z : Ω × Ω, W z.1 z.2 ∂μ.prod μ := by
  have h := integral_map (μ := sampleMeasure μ n) (f := Function.uncurry W)
    ((measurable_pi_apply i).prodMk (measurable_pi_apply j)).aemeasurable
    hW.aestronglyMeasurable
  rw [sampleMeasure_map_pair hij] at h
  exact h.symm

theorem measurable_samplePairDensity {W : Ω → Ω → ℝ}
    (hW : Measurable (Function.uncurry W)) (n : ℕ) :
    Measurable (samplePairDensity n W) := by
  have hterm : ∀ i j : Fin n,
      Measurable (fun ω : Fin n → Ω => if i = j then (0 : ℝ) else W (ω i) (ω j)) := by
    intro i j
    split_ifs
    · exact measurable_const
    · exact hW.comp (show Measurable (fun ω : Fin n → Ω => (ω i, ω j)) from
        (measurable_pi_apply i).prodMk (measurable_pi_apply j))
  unfold samplePairDensity
  exact ((Finset.measurable_sum _ (fun i _ =>
    Finset.measurable_sum _ (fun j _ => hterm i j))).const_mul _).div_const _

theorem samplePairDensity_mem_Icc {W : Ω → Ω → ℝ}
    (hbound : ∀ x y, W x y ∈ Set.Icc (0 : ℝ) 1)
    {n : ℕ} (hn : 0 < n) (ω : Fin n → Ω) :
    samplePairDensity n W ω ∈ Set.Icc (0 : ℝ) (1 / 2) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hterm0 : ∀ i j : Fin n, 0 ≤ if i = j then (0 : ℝ) else W (ω i) (ω j) := by
    intro i j
    split_ifs
    · exact le_rfl
    · exact (hbound (ω i) (ω j)).1
  have hsum : (∑ i, ∑ j, if i = j then (0 : ℝ) else W (ω i) (ω j)) ≤ (n : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ _ : Fin n, ∑ _ : Fin n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        split_ifs
        · norm_num
        · exact (hbound (ω i) (ω j)).2
      _ = (n : ℝ) ^ 2 := by simp; ring
  constructor
  · unfold samplePairDensity
    exact div_nonneg (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg
      (fun i _ => Finset.sum_nonneg (fun j _ => hterm0 i j)))) (by norm_num)
  · unfold samplePairDensity
    calc
      _ ≤ (n : ℝ)⁻¹ ^ 2 * (n : ℝ) ^ 2 / 2 := by gcongr
      _ = 1 / 2 := by field_simp

theorem integrable_samplePairDensity {W : Ω → Ω → ℝ}
    (hW : Measurable (Function.uncurry W))
    (hbound : ∀ x y, W x y ∈ Set.Icc (0 : ℝ) 1) {n : ℕ} (hn : 0 < n) :
    Integrable (samplePairDensity n W) (sampleMeasure μ n) :=
  (memLp_of_bounded (ae_of_all _ (samplePairDensity_mem_Icc hbound hn))
    (measurable_samplePairDensity hW n).aestronglyMeasurable 1).integrable le_rfl

/-- The diagonal omission costs exactly the factor `1 - 1/n` in expectation. -/
theorem integral_samplePairDensity {W : Ω → Ω → ℝ}
    (hW : Measurable (Function.uncurry W))
    (hbound : ∀ x y, W x y ∈ Set.Icc (0 : ℝ) 1) {n : ℕ} (hn : 0 < n) :
    (∫ ω, samplePairDensity n W ω ∂sampleMeasure μ n) =
      (1 - (n : ℝ)⁻¹) * ((∫ z : Ω × Ω, W z.1 z.2 ∂μ.prod μ) / 2) := by
  classical
  let D := ∫ z : Ω × Ω, W z.1 z.2 ∂μ.prod μ
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hterm : ∀ i j : Fin n,
      Integrable (fun ω : Fin n → Ω => if i = j then (0 : ℝ) else W (ω i) (ω j))
        (sampleMeasure μ n) := by
    intro i j
    split_ifs
    · exact integrable_const 0
    · exact (memLp_of_bounded
        (ae_of_all (sampleMeasure μ n) (fun ω : Fin n → Ω => hbound (ω i) (ω j)))
        (hW.comp (show Measurable (fun ω : Fin n → Ω => (ω i, ω j)) from
          (measurable_pi_apply i).prodMk (measurable_pi_apply j))).aestronglyMeasurable
        1).integrable le_rfl
  have he : ∀ i j : Fin n,
      (∫ ω, (if i = j then (0 : ℝ) else W (ω i) (ω j)) ∂sampleMeasure μ n) =
      if i = j then 0 else D := by
    intro i j
    by_cases hij : i = j
    · simp [hij]
    · simpa only [hij, ↓reduceIte] using integral_sample_pair (μ := μ) hij hW
  have hrow : ∀ i : Fin n, (∑ j : Fin n, if i = j then (0 : ℝ) else D) = n * D - D := by
    intro i
    calc
      _ = ∑ j : Fin n, (D - if i = j then D else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> ring
      _ = n * D - D := by simp [Finset.sum_sub_distrib]
  unfold samplePairDensity
  rw [integral_div, integral_const_mul, integral_finsetSum]
  · simp_rw [integral_finsetSum _ (fun j _ => hterm _ j), he, hrow]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    dsimp [D]
    field_simp
  · intro i _
    exact integrable_finsetSum _ (fun j _ => hterm i j)

/-- A quadratic penalty gives one finite sample which has both nearly the
correct cost and at least nearly the correct density. Any almost-sure property
may be required of the same sample. -/
theorem exists_sample_approx_of_large {W : Ω → Ω → ℝ}
    (hW : Measurable (Function.uncurry W))
    (hWbound : ∀ x y, W x y ∈ Set.Icc (0 : ℝ) 1)
    {f : Ω → ℝ} (hf : Measurable f) (hfbound : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 0 < n)
    (hlarge : 1 / 2 + ((1 + ε) / ε ^ 2) / 4 < ε * n)
    (P : (Fin n → Ω) → Prop) (hP : ∀ᵐ ω ∂sampleMeasure μ n, P ω) :
    ∃ ω : Fin n → Ω, P ω ∧
      |sampleMean n f ω - ∫ x, f x ∂μ| < ε ∧
      (∫ z : Ω × Ω, W z.1 z.2 ∂μ.prod μ) / 2 - ε < samplePairDensity n W ω := by
  let D : ℝ := (∫ z : Ω × Ω, W z.1 z.2 ∂μ.prod μ) / 2
  let M : ℝ := (1 + ε) / ε ^ 2
  let q : (Fin n → Ω) → ℝ := fun ω =>
    samplePairDensity n W ω - M * (sampleMean n f ω - ∫ x, f x ∂μ) ^ 2
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hM : 0 < M := div_pos (by linarith) (sq_pos_of_pos hε)
  have hWint : Integrable (Function.uncurry W) (μ.prod μ) :=
    (memLp_of_bounded (ae_of_all _ (fun z : Ω × Ω => hWbound z.1 z.2))
      hW.aestronglyMeasurable 1).integrable le_rfl
  have hD0 : 0 ≤ D := div_nonneg (integral_nonneg (fun z => (hWbound z.1 z.2).1)) (by norm_num)
  have hD1 : D ≤ 1 / 2 := by
    have h : (∫ z : Ω × Ω, W z.1 z.2 ∂μ.prod μ) ≤ 1 := by
      calc
        (∫ z : Ω × Ω, W z.1 z.2 ∂μ.prod μ) ≤ ∫ _ : Ω × Ω, (1 : ℝ) ∂μ.prod μ :=
          integral_mono hWint (integrable_const (1 : ℝ))
            (fun z => (hWbound z.1 z.2).2)
        _ = 1 := by simp
    dsimp [D]
    linarith
  have heInt := integrable_samplePairDensity (μ := μ) hW hWbound hn
  have hdevInt : Integrable (fun ω : Fin n → Ω =>
      (sampleMean n f ω - ∫ x, f x ∂μ) ^ 2) (sampleMeasure μ n) :=
    ((memLp_sampleMean (μ := μ) hf hfbound hn).sub
      (memLp_const (∫ x, f x ∂μ))).integrable_sq
  have hqInt : Integrable q (sampleMeasure μ n) := heInt.sub (hdevInt.const_mul M)
  have hqE : (∫ ω, q ω ∂sampleMeasure μ n) =
      (1 - (n : ℝ)⁻¹) * D - M *
        (∫ ω, (sampleMean n f ω - ∫ x, f x ∂μ) ^ 2 ∂sampleMeasure μ n) := by
    dsimp [q]
    rw [integral_sub heInt (hdevInt.const_mul M), integral_const_mul,
      integral_samplePairDensity hW hWbound hn]
  have hdev := mean_square_sampleMean_le (μ := μ) hf hfbound hn
  have hsmall : (D + M / 4) / n < ε := by
    calc
      (D + M / 4) / n ≤ (1 / 2 + M / 4) / n :=
        div_le_div_of_nonneg_right (by linarith) hnR.le
      _ < ε := (div_lt_iff₀ hnR).2 hlarge
  have hE : D - ε < ∫ ω, q ω ∂sampleMeasure μ n := by
    rw [hqE]
    calc
      D - ε < D - (D + M / 4) / n := sub_lt_sub_left hsmall D
      _ = (1 - (n : ℝ)⁻¹) * D - M * (1 / (4 * n)) := by ring
      _ ≤ _ := sub_le_sub_left (mul_le_mul_of_nonneg_left hdev hM.le) _
  have hex : ∃ ω : Fin n → Ω, P ω ∧ D - ε < q ω := by
    by_contra h
    push_neg at h
    have hh := integral_mono_ae hqInt (integrable_const (D - ε))
      (hP.mono (fun ω hω => h ω hω))
    have hh' : (∫ ω, q ω ∂sampleMeasure μ n) ≤ D - ε := by simpa using hh
    exact hE.not_ge hh'
  obtain ⟨ω, hω, hqω⟩ := hex
  have hedge := (samplePairDensity_mem_Icc hWbound hn ω).2
  have hnorm : M * ε ^ 2 = 1 + ε :=
    div_mul_cancel₀ _ (pow_ne_zero 2 hε.ne')
  refine ⟨ω, hω, ?_, ?_⟩
  · by_contra! habs
    have hsq : ε ^ 2 ≤ (sampleMean n f ω - ∫ x, f x ∂μ) ^ 2 := by
      nlinarith [sq_abs (sampleMean n f ω - ∫ x, f x ∂μ)]
    have hmul := mul_le_mul_of_nonneg_left hsq hM.le
    dsimp [q] at hqω
    nlinarith
  · dsimp [q] at hqω
    have hpen := mul_nonneg hM.le (sq_nonneg (sampleMean n f ω - ∫ x, f x ∂μ))
    dsimp [D] at hqω
    linarith

/-- Samples with simultaneous cost and density approximation exist with
arbitrarily many vertices, together with any almost-sure feasibility condition. -/
theorem exists_large_sample_approx {W : Ω → Ω → ℝ}
    (hW : Measurable (Function.uncurry W))
    (hWbound : ∀ x y, W x y ∈ Set.Icc (0 : ℝ) 1)
    {f : Ω → ℝ} (hf : Measurable f) (hfbound : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    {ε : ℝ} (hε : 0 < ε) (N : ℕ)
    (P : ∀ n : ℕ, (Fin n → Ω) → Prop)
    (hP : ∀ n, ∀ᵐ ω ∂sampleMeasure μ n, P n ω) :
    ∃ n : ℕ, N ≤ n ∧ 0 < n ∧ ∃ ω : Fin n → Ω, P n ω ∧
      |sampleMean n f ω - ∫ x, f x ∂μ| < ε ∧
      (∫ z : Ω × Ω, W z.1 z.2 ∂μ.prod μ) / 2 - ε < samplePairDensity n W ω := by
  let C : ℝ := 1 / 2 + ((1 + ε) / ε ^ 2) / 4
  obtain ⟨n, hn⟩ := exists_nat_gt (max (N : ℝ) (C / ε))
  have hN : (N : ℝ) < n := (le_max_left _ _).trans_lt hn
  have hn0 : 0 < (n : ℝ) := lt_of_le_of_lt (Nat.cast_nonneg N) hN
  have hnNat : 0 < n := by exact_mod_cast hn0
  have hlarge : C < ε * n := by
    have h := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hn)
    nlinarith
  refine ⟨n, ?_, hnNat, ?_⟩
  · exact_mod_cast hN.le
  · exact exists_sample_approx_of_large hW hWbound hf hfbound hε hnNat hlarge (P n) (hP n)

end DensityHS.Graphon
