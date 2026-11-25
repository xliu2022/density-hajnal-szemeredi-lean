module

public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Tactic

/-!
# Simultaneous random selection of local absorbers

The selection argument uses independent Bernoulli choices and one positive
potential.  Its expectation controls the size, the number of intersecting
pairs, and the number of selected absorbers for every target set at once.

Formalization author and maintainer: Xizhi Liu.
-/

@[expose] public section

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace DensityHS.Rainbow

theorem integrable_finite_function {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) : Integrable f μ := by
  classical
  refine Integrable.of_bound (measurable_of_countable f).aestronglyMeasurable
    (∑ ω, ‖f ω‖) (ae_of_all _ fun ω => ?_)
  exact Finset.single_le_sum (fun _ _ => norm_nonneg _) (mem_univ ω)

def selectionCoin (b : Bool) : ℝ := if b then 1 else 0

theorem selectionCoin_nonneg (b : Bool) : 0 ≤ selectionCoin b := by
  cases b <;> norm_num [selectionCoin]

noncomputable def selectionMeasure (I : Type*) [Fintype I] (p : unitInterval) :
    Measure (I → Bool) :=
  Measure.pi (fun _ : I => bernoulliMeasure true false p)

instance {I : Type*} [Fintype I] (p : unitInterval) :
    IsProbabilityMeasure (selectionMeasure I p) := by
  unfold selectionMeasure
  infer_instance

variable {I Q : Type*} [Fintype I] [Fintype Q]

noncomputable def selectedCount (U : Finset I) (ω : I → Bool) : ℝ :=
  ∑ i ∈ U, selectionCoin (ω i)

theorem selectedCount_nonneg (U : Finset I) (ω : I → Bool) :
    0 ≤ selectedCount U ω :=
  sum_nonneg fun _ _ => selectionCoin_nonneg _

theorem integral_selectionCoin (p : unitInterval) (i : I) :
    ∫ ω, selectionCoin (ω i) ∂selectionMeasure I p = (p : ℝ) := by
  unfold selectionMeasure
  rw [integral_comp_eval (measurable_of_countable selectionCoin).aestronglyMeasurable,
    integral_bernoulliMeasure]
  simp [selectionCoin]

theorem integral_selectedCount (p : unitInterval) (U : Finset I) :
    ∫ ω, selectedCount U ω ∂selectionMeasure I p = (p : ℝ) * U.card := by
  classical
  unfold selectedCount
  rw [integral_finsetSum U (fun _ _ => integrable_finite_function _ _)]
  simp only [integral_selectionCoin, sum_const, nsmul_eq_mul]
  ring

theorem integral_selectionCoin_mul (p : unitInterval) {i j : I} (hij : i ≠ j) :
    ∫ ω, selectionCoin (ω i) * selectionCoin (ω j) ∂selectionMeasure I p =
      (p : ℝ) ^ 2 := by
  have hind : iIndepFun (fun (i : I) (ω : I → Bool) => selectionCoin (ω i))
      (selectionMeasure I p) :=
    iIndepFun_pi (fun _ => (measurable_of_countable selectionCoin).aemeasurable)
  rw [(hind.indepFun hij).integral_fun_mul_eq_mul_integral
    (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_countable _).aestronglyMeasurable,
    integral_selectionCoin, integral_selectionCoin]
  ring

noncomputable def selectedConflictCount (E : Finset (I × I)) (ω : I → Bool) : ℝ :=
  ∑ e ∈ E, selectionCoin (ω e.1) * selectionCoin (ω e.2)

theorem selectedConflictCount_nonneg (E : Finset (I × I)) (ω : I → Bool) :
    0 ≤ selectedConflictCount E ω :=
  sum_nonneg fun _ _ => mul_nonneg (selectionCoin_nonneg _) (selectionCoin_nonneg _)

theorem integral_selectedConflictCount (p : unitInterval) (E : Finset (I × I))
    (hE : ∀ e ∈ E, e.1 ≠ e.2) :
    ∫ ω, selectedConflictCount E ω ∂selectionMeasure I p =
      (p : ℝ) ^ 2 * E.card := by
  classical
  unfold selectedConflictCount
  rw [integral_finsetSum E (fun _ _ => integrable_finite_function _ _)]
  calc
    ∑ e ∈ E, ∫ ω, selectionCoin (ω e.1) * selectionCoin (ω e.2)
        ∂selectionMeasure I p = ∑ _e ∈ E, (p : ℝ) ^ 2 := by
      apply sum_congr rfl
      intro e he
      exact integral_selectionCoin_mul p (hE e he)
    _ = (p : ℝ) ^ 2 * E.card := by simp [mul_comm]

theorem integral_exp_neg_selectedCount (p : unitInterval) (U : Finset I) :
    ∫ ω, Real.exp (-selectedCount U ω) ∂selectionMeasure I p =
      (1 - (p : ℝ) + (p : ℝ) * Real.exp (-1)) ^ U.card := by
  classical
  have heq (ω : I → Bool) : Real.exp (-selectedCount U ω) =
      ∏ i : I, if i ∈ U then Real.exp (-selectionCoin (ω i)) else 1 := by
    simp only [selectedCount, ← sum_neg_distrib, Real.exp_sum]
    simp
  simp_rw [heq]
  unfold selectionMeasure
  rw [integral_fintype_prod_eq_prod
    (fun (i : I) (b : Bool) => if i ∈ U then Real.exp (-selectionCoin b) else 1)]
  have hsingle (i : I) :
      (∫ b, (if i ∈ U then Real.exp (-selectionCoin b) else 1 : ℝ)
        ∂bernoulliMeasure true false p) =
      if i ∈ U then 1 - (p : ℝ) + (p : ℝ) * Real.exp (-1) else 1 := by
    rw [integral_bernoulliMeasure]
    by_cases hi : i ∈ U <;> simp [hi, selectionCoin] <;> ring
  simp_rw [hsingle]
  simp

/-- The fixed positive exponent in the lower-tail estimate. -/
noncomputable def selectionDecay : ℝ := 1 / 2 - Real.exp (-1)

theorem selectionDecay_pos : 0 < selectionDecay := by
  have h : (2 : ℝ) < Real.exp 1 := by
    convert Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num) using 1 <;> norm_num
  rw [selectionDecay, Real.exp_neg]
  apply sub_pos.mpr
  simpa only [one_div] using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 2) h

theorem integral_exp_selection_loss_le (p : unitInterval) (U : Finset I)
    {m : ℝ} (hm : m ≤ U.card) :
    ∫ ω, Real.exp ((p : ℝ) * m / 2 - selectedCount U ω)
      ∂selectionMeasure I p ≤ Real.exp (-selectionDecay * (p : ℝ) * m) := by
  have hp := p.property.1
  have hep : 0 ≤ 1 - (p : ℝ) + (p : ℝ) * Real.exp (-1) := by
    have hp1 := p.property.2
    positivity
  have hbase : 1 - (p : ℝ) + (p : ℝ) * Real.exp (-1) ≤
      Real.exp (-(p : ℝ) * (1 - Real.exp (-1))) := by
    convert Real.add_one_le_exp (-(p : ℝ) * (1 - Real.exp (-1))) using 1 <;> ring
  have hfac : 0 ≤ (p : ℝ) * (1 - Real.exp (-1)) := by
    have h := selectionDecay_pos
    unfold selectionDecay at h
    exact mul_nonneg hp (by linarith)
  simp_rw [sub_eq_add_neg, Real.exp_add]
  rw [integral_const_mul, integral_exp_neg_selectedCount]
  calc
    Real.exp ((p : ℝ) * m / 2) *
        (1 - (p : ℝ) + (p : ℝ) * Real.exp (-1)) ^ U.card ≤
      Real.exp ((p : ℝ) * m / 2) *
        Real.exp (-(p : ℝ) * (1 - Real.exp (-1))) ^ U.card :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hep hbase U.card) (Real.exp_pos _).le
    _ = Real.exp ((p : ℝ) * m / 2 -
        U.card * (p : ℝ) * (1 - Real.exp (-1))) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-selectionDecay * (p : ℝ) * m) := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_right hm hfac
      unfold selectionDecay
      nlinarith

/-- A single averaging argument enforces all lower-tail requirements as well
as the two upper bounds.  `E` may list either orientation of every conflict;
only its diagonal must be empty. -/
theorem exists_simultaneous_selection (p : unitInterval) (Good : Q → Finset I)
    (E : Finset (I × I)) (hE : ∀ e ∈ E, e.1 ≠ e.2)
    {m S T : ℝ} (hgood : ∀ q, m ≤ (Good q).card) (hS : 0 < S) (hT : 0 < T)
    (hpotential : (p : ℝ) * Fintype.card I / S +
      (p : ℝ) ^ 2 * E.card / T +
      Fintype.card Q * Real.exp (-selectionDecay * (p : ℝ) * m) < 1) :
    ∃ ω : I → Bool,
      selectedCount univ ω < S ∧ selectedConflictCount E ω < T ∧
      ∀ q, (p : ℝ) * m / 2 < selectedCount (Good q) ω := by
  classical
  let μ := selectionMeasure I p
  let Z : (I → Bool) → ℝ := fun ω =>
    selectedCount univ ω / S + selectedConflictCount E ω / T +
      ∑ q, Real.exp ((p : ℝ) * m / 2 - selectedCount (Good q) ω)
  have hZI : Integrable Z μ := integrable_finite_function _ _
  have hmean : ∫ ω, Z ω ∂μ ≤ (p : ℝ) * Fintype.card I / S +
      (p : ℝ) ^ 2 * E.card / T +
      Fintype.card Q * Real.exp (-selectionDecay * (p : ℝ) * m) := by
    dsimp only [Z, μ]
    rw [integral_add (integrable_finite_function _ _) (integrable_finite_function _ _),
      integral_add (integrable_finite_function _ _) (integrable_finite_function _ _),
      integral_div, integral_div, integral_selectedCount,
      integral_selectedConflictCount p E hE,
      integral_finsetSum univ (fun _ _ => integrable_finite_function _ _), card_univ]
    apply add_le_add le_rfl
    calc
      (∑ q, ∫ ω, Real.exp ((p : ℝ) * m / 2 - selectedCount (Good q) ω)
          ∂selectionMeasure I p) ≤
        ∑ _q : Q, Real.exp (-selectionDecay * (p : ℝ) * m) :=
          sum_le_sum fun q _ => integral_exp_selection_loss_le p (Good q) (hgood q)
      _ = _ := by simp
  have hex : ∃ ω, Z ω < 1 := by
    by_contra h
    push Not at h
    have hlow : (1 : ℝ) ≤ ∫ ω, Z ω ∂μ := by
      simpa using integral_mono (integrable_const (1 : ℝ)) hZI h
    linarith
  obtain ⟨ω, hω⟩ := hex
  have hsize0 := div_nonneg (selectedCount_nonneg (univ : Finset I) ω) hS.le
  have hconf0 := div_nonneg (selectedConflictCount_nonneg E ω) hT.le
  have hsum0 : 0 ≤ ∑ q, Real.exp ((p : ℝ) * m / 2 - selectedCount (Good q) ω) :=
    sum_nonneg fun _ _ => (Real.exp_pos _).le
  dsimp only [Z] at hω
  refine ⟨ω, ?_, ?_, ?_⟩
  · have hh : selectedCount univ ω / S < 1 := by linarith
    exact (div_lt_one hS).mp hh
  · have hh : selectedConflictCount E ω / T < 1 := by linarith
    exact (div_lt_one hT).mp hh
  · intro q
    have hq := single_le_sum
      (fun q' (_ : q' ∈ (univ : Finset Q)) =>
        (Real.exp_pos ((p : ℝ) * m / 2 - selectedCount (Good q') ω)).le)
      (mem_univ q)
    have hh : Real.exp ((p : ℝ) * m / 2 - selectedCount (Good q) ω) < 1 := by
      linarith
    exact sub_neg.mp (Real.exp_lt_one_iff.mp hh)

/-- The finite set selected by a Boolean sample. -/
noncomputable def selectedSet (ω : I → Bool) : Finset I :=
  univ.filter fun i => ω i = true

variable [DecidableEq I]

theorem selectedCount_eq_card (U : Finset I) (ω : I → Bool) :
    selectedCount U ω = ((U ∩ selectedSet ω).card : ℝ) := by
  classical
  have hsets : U.filter (fun i => ω i = true) = U ∩ selectedSet ω := by
    ext i
    simp [selectedSet]
  simp only [selectedCount, selectionCoin, sum_boole, hsets]

theorem selectedConflictCount_eq_card (E : Finset (I × I)) (ω : I → Bool) :
    selectedConflictCount E ω =
      ((E.filter fun e => e.1 ∈ selectedSet ω ∧ e.2 ∈ selectedSet ω).card : ℝ) := by
  classical
  unfold selectedConflictCount
  have heq (e : I × I) : selectionCoin (ω e.1) * selectionCoin (ω e.2) =
      if e.1 ∈ selectedSet ω ∧ e.2 ∈ selectedSet ω then (1 : ℝ) else 0 := by
    simp only [selectedSet, mem_filter, mem_univ, true_and]
    cases h₁ : ω e.1 <;> cases h₂ : ω e.2 <;> simp [selectionCoin, h₁, h₂]
  simp_rw [heq]
  exact sum_boole _ _

/-- A finite-set version of the probabilistic selection theorem. -/
theorem exists_simultaneous_selection_finset (p : unitInterval) (Good : Q → Finset I)
    (E : Finset (I × I)) (hE : ∀ e ∈ E, e.1 ≠ e.2)
    {m S T : ℝ} (hgood : ∀ q, m ≤ (Good q).card) (hS : 0 < S) (hT : 0 < T)
    (hpotential : (p : ℝ) * Fintype.card I / S +
      (p : ℝ) ^ 2 * E.card / T +
      Fintype.card Q * Real.exp (-selectionDecay * (p : ℝ) * m) < 1) :
    ∃ A : Finset I, (A.card : ℝ) < S ∧
      ((E.filter fun e => e.1 ∈ A ∧ e.2 ∈ A).card : ℝ) < T ∧
      ∀ q, (p : ℝ) * m / 2 < ((Good q ∩ A).card : ℝ) := by
  classical
  obtain ⟨ω, hω, hEω, hq⟩ := exists_simultaneous_selection p Good E hE hgood hS hT hpotential
  refine ⟨selectedSet ω, ?_, ?_, ?_⟩
  · simpa only [selectedCount_eq_card, univ_inter] using hω
  · simpa only [selectedConflictCount_eq_card] using hEω
  · intro q
    simpa only [selectedCount_eq_card] using hq q

/-- Delete the first endpoint of each selected conflict.  The deletion cost
is at most the number of selected conflicts, even when conflicts overlap. -/
theorem exists_conflict_free_subselection (A : Finset I) (E : Finset (I × I)) :
    ∃ B : Finset I, B ⊆ A ∧
      (A \ B).card ≤ (E.filter fun e => e.1 ∈ A ∧ e.2 ∈ A).card ∧
      ∀ e ∈ E, ¬(e.1 ∈ B ∧ e.2 ∈ B) := by
  classical
  let F := E.filter fun e => e.1 ∈ A ∧ e.2 ∈ A
  let R := F.image Prod.fst
  let B := A \ R
  have hBA : B ⊆ A := sdiff_subset
  have hrem : A \ B ⊆ R := by
    intro i hi
    have hiA := (mem_sdiff.mp hi).1
    by_contra hiR
    exact (mem_sdiff.mp hi).2 (mem_sdiff.mpr ⟨hiA, hiR⟩)
  refine ⟨B, hBA, (card_le_card hrem).trans (card_image_le), ?_⟩
  intro e he heB
  have heF : e ∈ F := mem_filter.mpr ⟨he, hBA heB.1, hBA heB.2⟩
  have heR : e.1 ∈ R := mem_image.mpr ⟨e, heF, rfl⟩
  exact (mem_sdiff.mp heB.1).2 heR

theorem inter_card_le_subselection_add (U A B : Finset I) :
    (U ∩ A).card ≤ (U ∩ B).card + (A \ B).card := by
  have hsub : U ∩ A ⊆ (U ∩ B) ∪ (A \ B) := by
    intro i hi
    by_cases hiB : i ∈ B
    · exact mem_union_left _ (mem_inter.mpr ⟨(mem_inter.mp hi).1, hiB⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨(mem_inter.mp hi).2, hiB⟩)
  exact (card_le_card hsub).trans (card_union_le _ _)

/-- A small conflict-free family meeting every prescribed family of good
candidates.  Every hypothesis is an explicit finite cardinal or scalar
inequality. -/
theorem exists_conflict_free_selection (p : unitInterval) (Good : Q → Finset I)
    (E : Finset (I × I)) (hE : ∀ e ∈ E, e.1 ≠ e.2)
    {m S T : ℝ} (hgood : ∀ q, m ≤ (Good q).card) (hS : 0 < S) (hT : 0 < T)
    (hpotential : (p : ℝ) * Fintype.card I / S +
      (p : ℝ) ^ 2 * E.card / T +
      Fintype.card Q * Real.exp (-selectionDecay * (p : ℝ) * m) < 1) :
    ∃ B : Finset I, (B.card : ℝ) < S ∧
      (∀ e ∈ E, ¬(e.1 ∈ B ∧ e.2 ∈ B)) ∧
      ∀ q, (p : ℝ) * m / 2 - T < ((Good q ∩ B).card : ℝ) := by
  obtain ⟨A, hA, hEA, hgoodA⟩ :=
    exists_simultaneous_selection_finset p Good E hE hgood hS hT hpotential
  obtain ⟨B, hBA, hdel, hfree⟩ := exists_conflict_free_subselection A E
  have hdelR : ((A \ B).card : ℝ) < T := lt_of_le_of_lt (by exact_mod_cast hdel) hEA
  refine ⟨B, lt_of_le_of_lt (by exact_mod_cast card_le_card hBA) hA, hfree, ?_⟩
  intro q
  have hcount : ((Good q ∩ A).card : ℝ) ≤
      ((Good q ∩ B).card : ℝ) + ((A \ B).card : ℝ) := by
    exact_mod_cast inter_card_le_subselection_add (Good q) A B
  have hh := hgoodA q
  linarith

end DensityHS.Rainbow
