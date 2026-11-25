module

public import DensityHS.Rainbow.PairOrientation
public import DensityHS.Rainbow.AbsorberParameters

/-!
# Degree margins for simultaneous pair orientation

A fixed positive margin in every expected out-degree yields one orientation
meeting all target degrees once the number of clusters is large enough.

Formalization author and maintainer: Xizhi Liu.
-/

@[expose] public section

open Finset Filter
open scoped BigOperators Topology

universe u

namespace DensityHS.Rainbow

theorem one_sub_exp_neg_lower {t : ℝ} (ht : 0 ≤ t) :
    t / (1 + t) ≤ 1 - Real.exp (-t) := by
  have hden : 0 < 1 + t := by linarith
  have he := Real.add_one_le_exp t
  have hrec : Real.exp (-t) ≤ 1 / (1 + t) := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le hden (by linarith)
  have heq : t / (1 + t) = 1 - 1 / (1 + t) := by field_simp; ring
  rw [heq]
  linarith

theorem exists_orientation_exponent {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hδ : 0 < δ) : ∃ t c : ℝ, 0 < t ∧ 0 < c ∧
      t * ρ - (1 - Real.exp (-t)) * (ρ + δ) ≤ -c := by
  let t := δ / 2
  let c := t ^ 2 / (1 + t)
  have ht : 0 < t := by dsimp [t]; positivity
  have hden : 0 < 1 + t := by linarith
  have hc : 0 < c := by dsimp [c]; positivity
  have hcEq : c * (1 + t) = t ^ 2 := by
    dsimp [c]
    exact div_mul_cancel₀ _ hden.ne'
  have hfrac := one_sub_exp_neg_lower ht.le
  have hmul := mul_le_mul_of_nonneg_right hfrac (show 0 ≤ ρ + δ by linarith)
  have hρsq := mul_le_mul_of_nonneg_right hρ1 (sq_nonneg t)
  have hfracEq : (t / (1 + t) * (ρ + δ)) * (1 + t) = t * (ρ + δ) := by
    field_simp
  have htδ : δ = 2 * t := by dsimp [t]; ring
  have hbound : t * ρ + c ≤ t / (1 + t) * (ρ + δ) := by
    rw [htδ]
    apply (mul_le_mul_iff_left₀ hden).mp
    rw [htδ] at hfracEq
    nlinarith
  exact ⟨t, c, ht, hc, by linarith⟩

theorem exists_pairOrientation_minDegree_threshold {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ (I : Type u) [Fintype I] [LinearOrder I],
      N ≤ Fintype.card I →
      ∀ (p : I × I → unitInterval) (L R : I × I → Bool → ℝ),
      (∀ e b, L e b = 0 ∨ L e b = 1) →
      (∀ e b, R e b = 0 ∨ R e b = 1) →
      (∀ e, ¬e.1 < e.2 → ∀ b, L e b = 0 ∧ R e b = 0) →
      (∀ i, (ρ + δ) * Fintype.card I ≤
        (∑ j, binaryMean (p (i, j)) (L (i, j))) +
          ∑ j, binaryMean (p (j, i)) (R (j, i))) →
      ∃ ω : I × I → Bool, ∀ i,
        ρ * Fintype.card I < ((pairOrientation L R ω).outDegree i : ℝ) := by
  obtain ⟨t, c, ht, hc, hgap⟩ := exists_orientation_exponent hρ hρ1 hδ
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) * Real.exp (-c * n)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one, Function.comp_def] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 c hc).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)))
  refine ⟨N, ?_⟩
  intro I _ _ hn p L R hL hR hzero hm
  apply exists_pairOrientation_degrees p L R hL hR hzero
    (fun _ => (ρ + δ) * Fintype.card I) (fun _ => ρ * Fintype.card I) ht hm
  have hexponent : t * (ρ * Fintype.card I) -
      (1 - Real.exp (-t)) * ((ρ + δ) * Fintype.card I) ≤ -c * Fintype.card I := by
    simpa only [sub_mul, mul_assoc] using
      mul_le_mul_of_nonneg_right hgap (show (0 : ℝ) ≤ Fintype.card I by positivity)
  calc
    _ = (Fintype.card I : ℝ) * Real.exp (t * (ρ * Fintype.card I) -
        (1 - Real.exp (-t)) * ((ρ + δ) * Fintype.card I)) := by
      simp only [sum_const, card_univ, nsmul_eq_mul]
    _ ≤ (Fintype.card I : ℝ) * Real.exp (-c * Fintype.card I) := by gcongr
    _ < 1 := hN _ hn

end DensityHS.Rainbow
