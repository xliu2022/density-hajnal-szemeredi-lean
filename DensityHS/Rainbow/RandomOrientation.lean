module

public import DensityHS.Rainbow.AbsorberSelection

/-!
# Independent unequal Bernoulli choices with simultaneous degree bounds

Each query may read either orientation of a Boolean coordinate, or a constant
zero or one.  The conclusion is obtained by integrating an exponential
potential over the actual product probability measure.

Formalization author and maintainer: Xizhi Liu.
-/

@[expose] public section

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace DensityHS.Rainbow

variable {I Q : Type*} [Fintype I] [Fintype Q]

noncomputable def unequalSelectionMeasure (p : I → unitInterval) : Measure (I → Bool) :=
  Measure.pi (fun i => bernoulliMeasure true false (p i))

instance (p : I → unitInterval) : IsProbabilityMeasure (unequalSelectionMeasure p) := by
  unfold unequalSelectionMeasure
  infer_instance

def binaryMean (p : unitInterval) (f : Bool → ℝ) : ℝ :=
  (p : ℝ) * f true + (1 - (p : ℝ)) * f false

theorem integral_binary_exp_le (p : unitInterval) (f : Bool → ℝ)
    (hf : ∀ b, f b = 0 ∨ f b = 1) (t : ℝ) :
    ∫ b, Real.exp (-t * f b) ∂bernoulliMeasure true false p ≤
      Real.exp (-(1 - Real.exp (-t)) * binaryMean p f) := by
  have hfexp (b : Bool) : Real.exp (-t * f b) =
      1 - (1 - Real.exp (-t)) * f b := by
    rcases hf b with h | h <;> simp [h]
  rw [integral_bernoulliMeasure]
  simp only [smul_eq_mul, hfexp]
  convert Real.add_one_le_exp (-(1 - Real.exp (-t)) * binaryMean p f) using 1 <;>
    simp only [binaryMean] <;> ring

theorem integral_exp_binary_sum_le (p : I → unitInterval) (f : I → Bool → ℝ)
    (hf : ∀ i b, f i b = 0 ∨ f i b = 1) (t : ℝ) :
    ∫ ω, Real.exp (-t * ∑ i, f i (ω i)) ∂unequalSelectionMeasure p ≤
      Real.exp (-(1 - Real.exp (-t)) * ∑ i, binaryMean (p i) (f i)) := by
  classical
  have heq (ω : I → Bool) : Real.exp (-t * ∑ i, f i (ω i)) =
      ∏ i, Real.exp (-t * f i (ω i)) := by
    rw [mul_sum, Real.exp_sum]
  simp_rw [heq]
  unfold unequalSelectionMeasure
  rw [integral_fintype_prod_eq_prod (fun (i : I) (b : Bool) => Real.exp (-t * f i b))]
  calc
    (∏ i, ∫ b, Real.exp (-t * f i b) ∂bernoulliMeasure true false (p i)) ≤
        ∏ i, Real.exp (-(1 - Real.exp (-t)) * binaryMean (p i) (f i)) := by
      apply prod_le_prod₀
      · intro i _
        exact integral_nonneg fun _ => (Real.exp_pos _).le
      · intro i _
        exact integral_binary_exp_le (p i) (f i) (hf i) t
    _ = _ := by rw [← Real.exp_sum, ← mul_sum]

theorem integral_binary_loss_le (p : I → unitInterval) (f : I → Bool → ℝ)
    (hf : ∀ i b, f i b = 0 ∨ f i b = 1) {t m : ℝ} (ht : 0 ≤ t)
    (hm : m ≤ ∑ i, binaryMean (p i) (f i)) (a : ℝ) :
    ∫ ω, Real.exp (t * a - t * ∑ i, f i (ω i)) ∂unequalSelectionMeasure p ≤
      Real.exp (t * a - (1 - Real.exp (-t)) * m) := by
  have hfac : 0 ≤ 1 - Real.exp (-t) := by
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht))
  have heq (ω : I → Bool) : Real.exp (t * a - t * ∑ i, f i (ω i)) =
      Real.exp (t * a) * Real.exp (-t * ∑ i, f i (ω i)) := by
    rw [sub_eq_add_neg, Real.exp_add, neg_mul]
  simp_rw [heq]
  rw [integral_const_mul]
  calc
    Real.exp (t * a) *
        (∫ ω, Real.exp (-t * ∑ i, f i (ω i)) ∂unequalSelectionMeasure p) ≤
      Real.exp (t * a) *
        Real.exp (-(1 - Real.exp (-t)) * ∑ i, binaryMean (p i) (f i)) :=
      mul_le_mul_of_nonneg_left (integral_exp_binary_sum_le p f hf t) (Real.exp_pos _).le
    _ = Real.exp (t * a - (1 - Real.exp (-t)) *
        ∑ i, binaryMean (p i) (f i)) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left hm hfac
      linarith

/-- A simultaneous strict lower bound for finitely many sums of independently
chosen zero-one coordinates.  Different queries may use opposite outcomes of
the same coordinate, so this directly supports random reduced orientations. -/
theorem exists_simultaneous_binary_scores (p : I → unitInterval)
    (f : Q → I → Bool → ℝ) (hf : ∀ q i b, f q i b = 0 ∨ f q i b = 1)
    (m a : Q → ℝ) {t : ℝ} (ht : 0 < t)
    (hm : ∀ q, m q ≤ ∑ i, binaryMean (p i) (f q i))
    (hpotential : (∑ q, Real.exp (t * a q - (1 - Real.exp (-t)) * m q)) < 1) :
    ∃ ω : I → Bool, ∀ q, a q < ∑ i, f q i (ω i) := by
  classical
  let μ := unequalSelectionMeasure p
  let Z : (I → Bool) → ℝ := fun ω =>
    ∑ q, Real.exp (t * a q - t * ∑ i, f q i (ω i))
  have hmean : ∫ ω, Z ω ∂μ < 1 := by
    dsimp only [Z, μ]
    rw [integral_finsetSum univ (fun _ _ => integrable_finite_function _ _)]
    exact lt_of_le_of_lt
      (sum_le_sum fun q _ => integral_binary_loss_le p (f q) (hf q) ht.le (hm q) (a q))
      hpotential
  have hex : ∃ ω, Z ω < 1 := by
    by_contra h
    push Not at h
    have hlow : (1 : ℝ) ≤ ∫ ω, Z ω ∂μ := by
      simpa using integral_mono (integrable_const (1 : ℝ))
        (integrable_finite_function μ Z) h
    linarith
  obtain ⟨ω, hω⟩ := hex
  refine ⟨ω, fun q => ?_⟩
  dsimp only [Z] at hω
  have hh : Real.exp (t * a q - t * ∑ i, f q i (ω i)) < 1 :=
    lt_of_le_of_lt (single_le_sum
      (fun q' (_ : q' ∈ (univ : Finset Q)) =>
        (Real.exp_pos (t * a q' - t * ∑ i, f q' i (ω i))).le) (mem_univ q)) hω
  have hneg := Real.exp_lt_one_iff.mp hh
  nlinarith

end DensityHS.Rainbow
