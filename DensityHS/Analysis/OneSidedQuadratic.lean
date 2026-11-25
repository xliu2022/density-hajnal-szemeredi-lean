module

public import Mathlib.Tactic

/-!
# One-sided coefficients of a touching quadratic

Author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS.Analysis

theorem local_right_linear_nonpos {a b δ : ℝ} (hδ : 0 < δ)
    (h : ∀ t : ℝ, 0 < t → t < δ → a * t + b * t ^ 2 ≤ 0) : a ≤ 0 := by
  by_contra ha
  have hap : 0 < a := lt_of_not_ge ha
  let t := min (δ / 2) (a / (2 * (|b| + 1)))
  have ht : 0 < t := lt_min (by positivity) (div_pos hap (by positivity))
  have htδ : t < δ := (min_le_left _ _).trans_lt (by linarith)
  have hta : 2 * t * (|b| + 1) ≤ a := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * (|b| + 1))).mp
      (min_le_right (δ / 2) (a / (2 * (|b| + 1))))
    dsimp [t]
    nlinarith
  have hbt : -(|b| * t) ≤ b * t := by
    have hh := mul_le_mul_of_nonneg_right (neg_abs_le b) ht.le
    simpa only [neg_mul] using hh
  have hpoly := h t ht htδ
  have hmul : t * (a + b * t) ≤ 0 := by nlinarith only [hpoly]
  have hlin := nonpos_of_mul_nonpos_right hmul ht
  nlinarith

theorem local_left_linear_nonneg {a b δ : ℝ} (hδ : 0 < δ)
    (h : ∀ t : ℝ, -δ < t → t < 0 → a * t + b * t ^ 2 ≤ 0) : 0 ≤ a := by
  have hh : -a ≤ 0 := local_right_linear_nonpos (a := -a) (b := b) hδ (by
    intro t ht htδ
    have hneg := h (-t) (by linarith) (by linarith)
    nlinarith only [hneg])
  linarith

theorem local_nonpositive_side_quadratic {a q k δ : ℝ} (hδ : 0 < δ)
    (h : ∀ t : ℝ, |t| < δ → t * a ≤ 0 →
      ((q - k * a ^ 2) / 2) * t ^ 2 ≤ 0) : q ≤ k * a ^ 2 := by
  have ht : |δ / 2| < δ := by rw [abs_of_pos (by positivity)]; linarith
  have htneg : |-(δ / 2)| < δ := by simpa only [abs_neg] using ht
  have hs : 0 < (δ / 2) ^ 2 := sq_pos_of_pos (by positivity)
  by_cases ha : 0 ≤ a
  · have hp := h (-(δ / 2)) htneg (mul_nonpos_of_nonpos_of_nonneg (by linarith) ha)
    have hq : (q - k * a ^ 2) / 2 ≤ 0 := nonpos_of_mul_nonpos_left hp (by simpa using hs)
    linarith
  · have hp := h (δ / 2) ht (mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_not_ge ha))
    have hq := nonpos_of_mul_nonpos_left hp hs
    linarith

theorem local_nonnegative_side_quadratic {a q k δ : ℝ} (hδ : 0 < δ)
    (h : ∀ t : ℝ, |t| < δ → 0 ≤ t * a →
      ((q - k * a ^ 2) / 2) * t ^ 2 ≤ 0) : q ≤ k * a ^ 2 := by
  apply local_nonpositive_side_quadratic hδ
  intro t ht hta
  have hp := h (-t) (by simpa only [abs_neg] using ht) (by nlinarith)
  simpa only [neg_sq] using hp

end DensityHS.Analysis

