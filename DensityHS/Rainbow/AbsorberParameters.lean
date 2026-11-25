module

public import DensityHS.Rainbow.AbsorberSelection
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Quantitative selection parameters for absorbing sets

A polynomial supply of labelled candidates and a polynomial overlap estimate
are sufficient for a small absorbing set.  This file verifies the numerical
choice of the Bernoulli probability and the uniform exponential estimate.

Formalization author and maintainer: Xizhi Liu.
-/

@[expose] public section

open Filter
open scoped Topology

namespace DensityHS.Rainbow

theorem scaled_probability_mass {a : ℕ} (ha : 0 < a) {n : ℝ} (hn : 0 < n)
    (b : ℝ) : b / n ^ (a - 1) * n ^ a = b * n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
  simp only [Nat.add_sub_cancel, Nat.succ_eq_add_one, pow_succ]
  field_simp

theorem scaled_probability_conflicts {a : ℕ} (ha : 0 < a) {n : ℝ} (hn : 0 < n)
    (b : ℝ) : (b / n ^ (a - 1)) ^ 2 * (a : ℝ) ^ 2 * n ^ (2 * a - 1) =
      b ^ 2 * (a : ℝ) ^ 2 * n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
  rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
  simp only [Nat.add_sub_cancel, Nat.succ_eq_add_one]
  rw [pow_succ n (2 * k), mul_comm 2 k, pow_mul]
  field_simp
  <;> ring

theorem exists_selection_parameters_of_scale {a r : ℕ} (ha : 0 < a) (hr : 0 < r)
    {η b ζ : ℝ} (hη : 0 < η) (hb : 0 < b) (hb1 : b ≤ 1)
    (hbη : 64 * (a : ℝ) ^ 2 * b ≤ η) (hbζ : 4 * (a : ℝ) * b ≤ ζ) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∃ p : unitInterval, ∃ L : ℕ, ∃ S T : ℝ,
        0 < S ∧ 0 < T ∧ (a : ℝ) * S ≤ ζ * n ∧ γ * n ≤ (r * L : ℕ) ∧
        (L : ℝ) ≤ (p : ℝ) * (η * (n : ℝ) ^ a) / 2 - T ∧
        (p : ℝ) * (n : ℝ) ^ a / S +
          (p : ℝ) ^ 2 * (a : ℝ) ^ 2 * (n : ℝ) ^ (2 * a - 1) / T +
          (n : ℝ) ^ r * Real.exp (-selectionDecay * (p : ℝ) * (η * (n : ℝ) ^ a)) < 1 := by
  have hc : 0 < selectionDecay * b * η := mul_pos (mul_pos selectionDecay_pos hb) hη
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ r *
      Real.exp (-(selectionDecay * b * η) * n)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast, Function.comp_def] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (r : ℝ)
        (selectionDecay * b * η) hc).comp tendsto_natCast_atTop_atTop
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
    (hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num)))
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (16 / (η * b))
  refine ⟨η * b / 16, by positivity, max N₀ (N₁ + 1), by omega, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < n := by linarith
  have hηbn : 16 < η * b * n := by
    have hnn : (N₁ : ℝ) ≤ n := by exact_mod_cast (show N₁ ≤ n by omega)
    exact (div_lt_iff₀ (by positivity : 0 < η * b)).mp (hN₁.trans_le hnn) |>.trans_eq (by ring)
  let p : unitInterval := ⟨b / (n : ℝ) ^ (a - 1),
    div_nonneg hb.le (by positivity), (div_le_one (by positivity)).mpr
      (hb1.trans (one_le_pow₀ hnR))⟩
  let S : ℝ := 4 * b * n
  let T : ℝ := η * b * n / 8
  let L : ℕ := ⌊T⌋₊
  have hS : 0 < S := by dsimp [S]; positivity
  have hT : 0 < T := by dsimp [T]; positivity
  have hpm : (p : ℝ) * (η * (n : ℝ) ^ a) = η * b * n := by
    calc
      _ = η * ((b / (n : ℝ) ^ (a - 1)) * (n : ℝ) ^ a) := by dsimp [p]; ring
      _ = _ := by rw [scaled_probability_mass ha hnpos]; ring
  have hfloor : (L : ℝ) ≤ T := Nat.floor_le hT.le
  have hfloorlow : T < (L : ℝ) + 1 := Nat.lt_floor_add_one T
  have hcapacity : η * b / 16 * n ≤ (r * L : ℕ) := by
    have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have hmult := mul_le_mul_of_nonneg_right hrR (show (0 : ℝ) ≤ L by positivity)
    push_cast
    dsimp [T] at hfloorlow
    nlinarith
  have hsize : (a : ℝ) * S ≤ ζ * n := by
    simpa only [S, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_right hbζ hnpos.le
  have hL : (L : ℝ) ≤ (p : ℝ) * (η * (n : ℝ) ^ a) / 2 - T := by
    rw [hpm]
    dsimp [T] at *
    linarith
  have hfirst : (p : ℝ) * (n : ℝ) ^ a / S = 1 / 4 := by
    rw [show (p : ℝ) = b / (n : ℝ) ^ (a - 1) by rfl,
      scaled_probability_mass ha hnpos]
    dsimp [S]
    field_simp
    <;> ring
  have hsecond : (p : ℝ) ^ 2 * (a : ℝ) ^ 2 * (n : ℝ) ^ (2 * a - 1) / T ≤ 1 / 8 := by
    rw [show (p : ℝ) = b / (n : ℝ) ^ (a - 1) by rfl,
      scaled_probability_conflicts ha hnpos]
    apply (div_le_iff₀ hT).mpr
    dsimp [T]
    have hh := mul_le_mul_of_nonneg_right hbη (show 0 ≤ b * n by positivity)
    nlinarith
  have hthird : (n : ℝ) ^ r *
      Real.exp (-selectionDecay * (p : ℝ) * (η * (n : ℝ) ^ a)) < 1 / 4 := by
    have hexp : -selectionDecay * (p : ℝ) * (η * (n : ℝ) ^ a) =
        -(selectionDecay * b * η) * n := by
      calc
        _ = -selectionDecay * ((p : ℝ) * (η * (n : ℝ) ^ a)) := by ring
        _ = _ := by rw [hpm]; ring
    rw [hexp]
    exact hN₀ n (by omega)
  refine ⟨p, L, S, T, hS, hT, hsize, hcapacity, hL, ?_⟩
  linarith

theorem exists_selection_parameters {a r : ℕ} (ha : 0 < a) (hr : 0 < r)
    {η ζ : ℝ} (hη : 0 < η) (hζ : 0 < ζ) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∃ p : unitInterval, ∃ L : ℕ, ∃ S T : ℝ,
        0 < S ∧ 0 < T ∧ (a : ℝ) * S ≤ ζ * n ∧ γ * n ≤ (r * L : ℕ) ∧
        (L : ℝ) ≤ (p : ℝ) * (η * (n : ℝ) ^ a) / 2 - T ∧
        (p : ℝ) * (n : ℝ) ^ a / S +
          (p : ℝ) ^ 2 * (a : ℝ) ^ 2 * (n : ℝ) ^ (2 * a - 1) / T +
          (n : ℝ) ^ r * Real.exp (-selectionDecay * (p : ℝ) * (η * (n : ℝ) ^ a)) < 1 := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  let b := min 1 (min (η / (64 * (a : ℝ) ^ 2)) (ζ / (4 * (a : ℝ))))
  have hb : 0 < b := by dsimp [b]; positivity
  have hb1 : b ≤ 1 := min_le_left _ _
  have hbη : 64 * (a : ℝ) ^ 2 * b ≤ η := by
    have hh : b ≤ η / (64 * (a : ℝ) ^ 2) :=
      (min_le_right _ _).trans (min_le_left _ _)
    simpa only [mul_comm b] using (le_div_iff₀ (by positivity)).mp hh
  have hbζ : 4 * (a : ℝ) * b ≤ ζ := by
    have hh : b ≤ ζ / (4 * (a : ℝ)) :=
      (min_le_right _ _).trans (min_le_right _ _)
    simpa only [mul_comm b] using (le_div_iff₀ (by positivity)).mp hh
  exact exists_selection_parameters_of_scale ha hr hη hb hb1 hbη hbζ

end DensityHS.Rainbow
