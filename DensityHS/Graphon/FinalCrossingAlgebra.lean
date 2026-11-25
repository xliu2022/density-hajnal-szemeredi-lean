module

public import DensityHS.Graphon.PhaseMajorants

/-!
# Strict slopes and the shifted-neighbor contradiction at the final crossing

Author and maintainer: Xizhi Liu.

The degree and residual identities use the actual final branch polynomial.
The residual is strictly negative throughout the open admissible interval
whenever the multiplier is strictly below the final-branch derivative.
-/

@[expose] public section

namespace DensityHS.Graphon

open Set Filter
open scoped Topology

theorem twoBranch_slopes_strict_of_curvature_lt {r : ℕ}
    {x mL mR kL kR : ℝ} {F G : ℝ → ℝ}
    (hbranches : ∀ᶠ y in 𝓝 x,
      (y ≤ x → Phi r y = F y) ∧ (x ≤ y → Phi r y = G y))
    (hlower : ∀ᶠ y in 𝓝 x, G y ≤ Phi r y)
    (hF : ∀ y, F y = F x + mL * (y - x) + (kL / 2) * (y - x)^2)
    (hG : ∀ y, G y = G x + mR * (y - x) + (kR / 2) * (y - x)^2)
    (hk : kL < kR) : mL < mR := by
  have hle := twoBranch_slopes_ordered hbranches hlower hF hG
  apply lt_of_le_of_ne hle
  intro hm
  obtain ⟨δ, hδ, hloc⟩ := Metric.eventually_nhds_iff.mp (hbranches.and hlower)
  have hcenter := (hloc (show dist x x < δ by simpa using hδ)).1
  have hFG : F x = G x := (hcenter.1 le_rfl).symm.trans (hcenter.2 le_rfl)
  have hnear := hloc (show dist (x - δ / 2) x < δ by
    rw [Real.dist_eq]
    have hneg : x - δ / 2 - x < 0 := by linarith
    rw [abs_of_neg hneg]
    linarith)
  have hdom : G (x - δ / 2) ≤ F (x - δ / 2) := by
    simpa only [hnear.1.1 (by linarith : x - δ / 2 ≤ x)] using hnear.2
  rw [hF, hG, hFG, hm] at hdom
  have hq : 0 < (x - δ / 2 - x)^2 := sq_pos_of_ne_zero (by linarith)
  have hp := mul_pos (sub_pos.mpr hk) hq
  nlinarith

theorem RCrossing_slopes_strict {r : ℕ} (hr : 3 ≤ r) :
    ((r : ℝ) - 1) * (1 - ((r : ℝ) - 1) * RCrossing r) <
      (r : ℝ) * (1 - ((r : ℝ) - 1) * (1 - r * RCrossing r)) := by
  have hF := B_quadratic_expansion r (r - 1) (RCrossing r)
  have hG := R_quadratic_expansion r (RCrossing r)
  have hbranches := RCrossing_eventually_branches hr
  have hlower : ∀ᶠ y in 𝓝 (RCrossing r), R r y ≤ Phi r y := by
    have hnear : ∀ᶠ y in 𝓝 (RCrossing r),
        y ∈ Ioo (((r : ℝ) - 2) / ((r : ℝ) * ((r : ℝ) - 1))) (1 / (r : ℝ)) :=
      isOpen_Ioo.mem_nhds ⟨RCrossing_gt_left_endpoint hr, RCrossing_lt_right_endpoint hr⟩
    exact hnear.mono (fun y hy => R_le_Phi hr ⟨hy.1.le, hy.2.le⟩)
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hden : (r : ℝ) - (r - 1 : ℕ) = 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
    ring
  have hcurv : -((r - 1 : ℕ) : ℝ)^2 / ((r : ℝ) - (r - 1 : ℕ)) <
      (r : ℝ)^2 * ((r : ℝ) - 1) := by
    rw [hden, div_one]
    have hp : 0 < (r : ℝ)^2 * ((r : ℝ) - 1) :=
      mul_pos (sq_pos_of_pos (by linarith)) (by linarith)
    have hn := sq_nonneg ((r - 1 : ℕ) : ℝ)
    linarith
  have h := twoBranch_slopes_strict_of_curvature_lt hbranches hlower hF hG hcurv
  rw [hden, div_one, Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one] at h
  exact h

theorem RCrossing_ordinary_slope_nonneg {r : ℕ} (hr : 3 ≤ r) :
    0 ≤ ((r : ℝ) - 1) * (1 - ((r : ℝ) - 1) * RCrossing r) := by
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hrp : (0 : ℝ) < r := by linarith
  have hx0 : 0 < RCrossing r :=
    (by positivity : 0 < 1 / ((r : ℝ) + 1)).trans (RCrossing_gt_reciprocal_succ hr)
  have hxr := (lt_div_iff₀ hrp).mp (RCrossing_lt_right_endpoint hr)
  exact mul_nonneg (by linarith) (by nlinarith)

theorem R_shifted_degree_identities {r : ℕ} (hr : 0 < r) (x θ : ℝ) :
    let ell := 1 - (r : ℝ) * x
    let mR := (r : ℝ) * (1 - ((r : ℝ) - 1) * ell)
    let t := (mR - θ) * ell / r
    2 * R r x - θ * x = ((r : ℝ) - 2) * ell + (mR - θ) * x ∧
      1 - (2 * R r x - θ * x + θ / r) = ell + t := by
  dsimp only
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  constructor
  · unfold R
    ring
  · unfold R
    field_simp
    <;> ring

theorem R_shifted_residual_negative {r : ℕ} (hr : 3 ≤ r) {x θ : ℝ}
    (hx0 : ((r : ℝ) - 2) / ((r : ℝ) * ((r : ℝ) - 1)) < x)
    (hx1 : x < 1 / (r : ℝ))
    (hθ : θ < (r : ℝ) * (1 - ((r : ℝ) - 1) * (1 - r * x))) :
    let ell := 1 - (r : ℝ) * x
    let mR := (r : ℝ) * (1 - ((r : ℝ) - 1) * ell)
    let t := (mR - θ) * ell / r
    0 < t ∧ ∀ n : ℝ, 0 ≤ n → n ≤ (r : ℝ) - 2 →
      ((r : ℝ) - 2) * ell - (2 * R r x - θ * x) + t * n < 0 := by
  dsimp only
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hrp : (0 : ℝ) < r := by linarith
  have hden : 0 < (r : ℝ) * ((r : ℝ) - 1) := mul_pos hrp (by linarith)
  have hxbound := (div_lt_iff₀ hden).mp hx0
  have hxupper := (lt_div_iff₀ hrp).mp hx1
  have hell : 0 < 1 - (r : ℝ) * x := by nlinarith
  have hgap : 0 < (r : ℝ) * (1 - ((r : ℝ) - 1) * (1 - r * x)) - θ := sub_pos.mpr hθ
  refine ⟨div_pos (mul_pos hgap hell) hrp, ?_⟩
  intro n _ hn
  have hmul := mul_le_mul_of_nonneg_left hn hell.le
  have hnum : (1 - (r : ℝ) * x) * n < (r : ℝ) * x := by nlinarith
  have hsmall : -x + (1 - (r : ℝ) * x) * n / r < 0 := by
    have h : (1 - (r : ℝ) * x) * n / r < x :=
      (div_lt_iff₀ hrp).mpr (by nlinarith [hnum])
    linarith
  have hdegree := (R_shifted_degree_identities (by omega : 0 < r) x θ).1
  rw [hdegree]
  have hfactor :
      ((r : ℝ) - 2) * (1 - r * x) -
        (((r : ℝ) - 2) * (1 - r * x) +
          ((r : ℝ) * (1 - ((r : ℝ) - 1) * (1 - r * x)) - θ) * x) +
        (((r : ℝ) * (1 - ((r : ℝ) - 1) * (1 - r * x)) - θ) * (1 - r * x) / r) * n =
      ((r : ℝ) * (1 - ((r : ℝ) - 1) * (1 - r * x)) - θ) *
        (-x + (1 - (r : ℝ) * x) * n / r) := by ring
  rw [hfactor]
  exact mul_neg_of_pos_of_neg hgap hsmall

theorem RCrossing_shifted_residual_negative {r : ℕ} (hr : 3 ≤ r) {θ : ℝ}
    (hθ : θ < (r : ℝ) * (1 - ((r : ℝ) - 1) * (1 - r * RCrossing r))) :
    let x := RCrossing r
    let ell := 1 - (r : ℝ) * x
    let mR := (r : ℝ) * (1 - ((r : ℝ) - 1) * ell)
    let t := (mR - θ) * ell / r
    0 < t ∧ ∀ n : ℝ, 0 ≤ n → n ≤ (r : ℝ) - 2 →
      ((r : ℝ) - 2) * ell - (2 * R r x - θ * x) + t * n < 0 :=
  R_shifted_residual_negative hr (RCrossing_gt_left_endpoint hr)
    (RCrossing_lt_right_endpoint hr) hθ

end DensityHS.Graphon
