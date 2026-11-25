module

public import DensityHS.Stability.KernelRounding
public import Mathlib.Analysis.Real.Sqrt

/-!
# Finite edit rounding with prescribed integer part sizes

Author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS.Stability

open MeasureTheory Finset Fintype Graphon Regularity
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

theorem sum_abs_le_sqrt_card_mul_sum_sq (d : I → ℝ) :
    (∑ i, |d i|) ≤ Real.sqrt ((Fintype.card I : ℝ)*∑ i, (d i)^2) := by
  apply Real.le_sqrt_of_sq_le
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset I)
    (fun _ => (1 : ℝ)) (fun i => |d i|)
  simpa only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,sq_abs] using h

/-- Correct the random part sizes while preserving the quantitative edit
bound. The prescribed target sizes need only have the correct total. -/
theorem exists_adjusted_template_of_rounding
    (G : SimpleGraph V) (A : I → I → ℝ) (hsymm : ∀ i j, A i j=A j i)
    (f : V → I) (q : I → ℕ) (hq : ∑ i, q i=Fintype.card V)
    (m : I → ℝ) {S b : ℝ}
    (hsize : ∑ i, |(q i : ℝ)-m i| ≤ b)
    (hround : 2*(editDistance G (templateGraph A hsymm f) : ℝ)+
      (∑ i, ((fiberCount f i : ℝ)-m i)^2) ≤ S) :
    ∃ g : V → I, (∀ i, fiberCount g i=q i) ∧
      (editDistance G (templateGraph A hsymm g) : ℝ) ≤
        S/2+(Fintype.card V : ℝ)*(Real.sqrt ((Fintype.card I : ℝ)*S)+b) := by
  obtain ⟨g,hg,hmove⟩ := exists_adjustment_to_sizes f q hq
  have hsq0 : 0 ≤ ∑ i, ((fiberCount f i : ℝ)-m i)^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hsq : (∑ i, ((fiberCount f i : ℝ)-m i)^2) ≤ S := by
    have he0 : (0 : ℝ) ≤ editDistance G (templateGraph A hsymm f) := Nat.cast_nonneg _
    linarith
  have hdist : (editDistance G (templateGraph A hsymm f) : ℝ) ≤ S/2 := by linarith
  have hsum : (∑ i, |(fiberCount f i : ℝ)-m i|) ≤ Real.sqrt ((Fintype.card I : ℝ)*S) :=
    (sum_abs_le_sqrt_card_mul_sum_sq (fun i => (fiberCount f i : ℝ)-m i)).trans
      (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg _)))
  have hmove' : ((Finset.univ.filter (fun v => f v≠g v)).card : ℝ) ≤
      Real.sqrt ((Fintype.card I : ℝ)*S)+b := by
    apply hmove.trans
    calc
      _ ≤ ∑ i, (|(fiberCount f i : ℝ)-m i|+|(q i : ℝ)-m i|) := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [abs_sub_comm (m i) (q i : ℝ)] using
          abs_sub_le (fiberCount f i : ℝ) (m i) (q i : ℝ)
      _ ≤ _ := by rw [Finset.sum_add_distrib]; exact add_le_add hsum hsize
  have hchange : (editDistance (templateGraph A hsymm f) (templateGraph A hsymm g) : ℝ) ≤
      (Fintype.card V : ℝ)*(Finset.univ.filter (fun v => f v≠g v)).card := by
    exact_mod_cast templateGraph_edits_le_changed A hsymm f g
  have htri : (editDistance G (templateGraph A hsymm g) : ℝ) ≤
      (editDistance G (templateGraph A hsymm f) : ℝ)+
        (editDistance (templateGraph A hsymm f) (templateGraph A hsymm g) : ℝ) := by
    exact_mod_cast editDistance_triangle G (templateGraph A hsymm f) (templateGraph A hsymm g)
  exact ⟨g,hg,htri.trans (add_le_add hdist
    (hchange.trans (mul_le_mul_of_nonneg_left hmove' (Nat.cast_nonneg _))))⟩

theorem exists_kernel_rounding_prescribed_sizes
    {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace V] [MeasurableSingletonClass V] [Nonempty V]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (vl : Ω → V) (hv : Measurable vl)
    (hmass : ∀ v, μ.real {x | vl x=v}=1/(Fintype.card V : ℝ))
    (bl : Ω → I) (hb : Measurable bl)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : I → I → ℝ) (hsymm : ∀ i j, A i j=A j i) (hA : ∀ i j, A i j=0 ∨ A i j=1)
    (W U : Kernel Ω)
    (hW : ∀ x y, W x y=indicatorMatrix G (vl x) (vl y))
    (hU : ∀ x y, U x y=A (bl x) (bl y))
    (q : I → ℕ) (hq : ∑ i, q i=Fintype.card V) {b : ℝ}
    (hsize : ∑ i, |(q i : ℝ)-(Fintype.card V : ℝ)*μ.real {x | bl x=i}| ≤ b) :
    ∃ g : V → I, (∀ i, fiberCount g i=q i) ∧
      (editDistance G (templateGraph A hsymm g) : ℝ) ≤
        ((Fintype.card V : ℝ)^2*kernelL1Distance μ W U+Fintype.card V)/2+
          (Fintype.card V : ℝ)*(Real.sqrt ((Fintype.card I : ℝ)*
            ((Fintype.card V : ℝ)^2*kernelL1Distance μ W U+Fintype.card V))+b) := by
  obtain ⟨f,hf⟩ := exists_kernel_rounding μ vl hv hmass bl hb G A hsymm hA W U hW hU
  exact exists_adjusted_template_of_rounding G A hsymm f q hq
    (fun i => (Fintype.card V : ℝ)*μ.real {x | bl x=i}) hsize hf

/-- Uniform scalar choices for the quantitative edit-rounding estimate. -/
theorem exists_rounding_error_parameters (M : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ s : ℝ, 0 ≤ s → s ≤ δ → ∀ m : ℝ, 0 ≤ m → m ≤ M →
        ((n : ℝ)^2*s+n)/2+(n : ℝ)*(Real.sqrt (m*((n : ℝ)^2*s+n))+M) < ε*(n : ℝ)^2 := by
  let δ : ℝ := min (ε/8) (ε^2/(128*((M : ℝ)+1)))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδ1 : δ ≤ ε/8 := min_le_left _ _
  have hδ2 : 2*(M : ℝ)*δ ≤ (ε/8)^2 := by
    have hh := min_le_right (ε/8) (ε^2/(128*((M : ℝ)+1)))
    change δ ≤ _ at hh
    have hm : 0 < (M : ℝ)+1 := by positivity
    have hp := (le_div_iff₀ (show 0 < 128*((M : ℝ)+1) by positivity)).mp hh
    have hδ0 := hδ.le
    nlinarith
  obtain ⟨N,hN⟩ := exists_nat_gt (max (1/δ) (8*(M : ℝ)/ε))
  refine ⟨δ,hδ,N,?_⟩
  intro n hn s hs hsδ m hm hmM
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hbig1 : 1/δ < (n : ℝ) := (le_max_left _ _).trans_lt (hN.trans_le hNn)
  have hbig2 : 8*(M : ℝ)/ε < (n : ℝ) := (le_max_right _ _).trans_lt (hN.trans_le hNn)
  have hn0 : 0 < (n : ℝ) := (one_div_pos.mpr hδ).trans hbig1
  have hsmalln : (n : ℝ) ≤ δ*(n : ℝ)^2 := by
    have h := (div_lt_iff₀ hδ).mp hbig1
    nlinarith
  have hMn : (M : ℝ) ≤ ε*(n : ℝ)/8 := by
    have h := (div_lt_iff₀ hε).mp hbig2
    linarith
  let S : ℝ := (n : ℝ)^2*s+n
  have hS0 : 0 ≤ S := by dsimp [S]; positivity
  have hS : S ≤ 2*δ*(n : ℝ)^2 := by
    have h := mul_le_mul_of_nonneg_left hsδ (sq_nonneg (n : ℝ))
    dsimp [S]
    nlinarith
  have hsqrt : Real.sqrt (m*S) ≤ ε*(n : ℝ)/8 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    calc
      m*S ≤ (M : ℝ)*S := mul_le_mul_of_nonneg_right hmM hS0
      _ ≤ (M : ℝ)*(2*δ*(n : ℝ)^2) := mul_le_mul_of_nonneg_left hS (Nat.cast_nonneg _)
      _ = (2*(M : ℝ)*δ)*(n : ℝ)^2 := by ring
      _ ≤ (ε/8)^2*(n : ℝ)^2 := mul_le_mul_of_nonneg_right hδ2 (sq_nonneg _)
      _ = _ := by ring
  have hSε : S ≤ ε/4*(n : ℝ)^2 := by
    calc
      S ≤ 2*δ*(n : ℝ)^2 := hS
      _ ≤ 2*(ε/8)*(n : ℝ)^2 := by gcongr
      _ = _ := by ring
  have hroot := mul_le_mul_of_nonneg_left (add_le_add hsqrt hMn) hn0.le
  have hpos := mul_pos hε (sq_pos_of_pos hn0)
  change S/2+(n : ℝ)*(Real.sqrt (m*S)+M) < ε*(n : ℝ)^2
  nlinarith

end DensityHS.Stability
