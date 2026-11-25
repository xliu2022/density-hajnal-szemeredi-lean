module

public import DensityHS.Graphon.BranchVariation
public import DensityHS.Basic.PhaseActive

/-!
# The strict terminal degree gap

Author and maintainer: Xizhi Liu.

The terminal crossing already lies strictly beyond the threshold needed by
the robust-cover argument. Thus the gap persists at the transition itself,
not only inside the open terminal phase.
-/

@[expose] public section

namespace DensityHS.Graphon

open Set Filter
open scoped Topology

theorem RZeroCrossing_lt_gap_threshold {r : ℕ} (hr : 3 ≤ r) :
    RZeroCrossing r < 1 / ((r : ℝ) ^ 2 - r + 1) := by
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hb : 0 < (r : ℝ) ^ 2 - r + 1 := by nlinarith [sq_nonneg ((r : ℝ) - 1)]
  have ha : 0 < ((r : ℝ) - 1) * ((r : ℝ) ^ 2 + r - 1) :=
    mul_pos (by linarith) (by nlinarith [sq_nonneg (r : ℝ)])
  have hdisc : 0 < (r : ℝ) ^ 2 - 3 * r + 3 := by nlinarith [sq_nonneg ((r : ℝ) - 2)]
  have hs : 0 < (r : ℝ) * Real.sqrt ((r : ℝ) ^ 2 - 3 * r + 3) :=
    mul_pos (by linarith) (Real.sqrt_pos.mpr hdisc)
  have hroot := RZeroCrossing_pos hr
  have hnum : 0 < (r : ℝ) ^ 2 - r + 1 -
      r * Real.sqrt ((r : ℝ) ^ 2 - 3 * r + 3) := ((div_pos_iff.mp hroot).resolve_right
    (fun h => (not_lt_of_gt ha) h.2)).1
  have hid := RCrossing_discriminant hr
  unfold RZeroCrossing
  apply (div_lt_div_iff₀ ha hb).mpr
  nlinarith [mul_pos hs hnum]

/-- The terminal degree gap is positive throughout the active closed
terminal interval, including its left transition. -/
theorem R_degree_gap_pos {r : ℕ} (hr : 3 ≤ r) {x : ℝ} (hx : RCrossing r ≤ x) :
    0 < (r : ℝ) ^ 2 * x - ((r : ℝ) - 1 + ((r : ℝ) - 1) * x) := by
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hb : 0 < (r : ℝ) ^ 2 - r + 1 := by nlinarith [sq_nonneg ((r : ℝ) - 1)]
  have hell : 1 - (r : ℝ) * x ≤ RZeroCrossing r := by
    unfold RCrossing at hx
    have h := (div_le_iff₀ hr0).mp hx
    nlinarith
  have hsmall := hell.trans_lt (RZeroCrossing_lt_gap_threshold hr)
  have hmul := (lt_div_iff₀ hb).mp hsmall
  have hprod : 0 < (r : ℝ) *
      ((r : ℝ) ^ 2 * x - ((r : ℝ) - 1 + ((r : ℝ) - 1) * x)) := by
    nlinarith
  exact (mul_pos_iff.mp hprod).resolve_right (fun h => (not_lt_of_gt hr0) h.1) |>.2

theorem R_slope_nonneg {r : ℕ} (hr : 3 ≤ r) {x : ℝ}
    (hxl : RCrossing r ≤ x) (hxu : x ≤ 1 / (r : ℝ)) :
    0 ≤ (r : ℝ) * (1 - ((r : ℝ) - 1) * (1 - r * x)) := by
  have hdom := RDomain_of_after_crossing hr hxl hxu
  have hell := ell_mem_R_interval hr hdom
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hm : 0 < (r : ℝ) - 1 := by linarith
  have h := (le_div_iff₀ hm).mp hell.2
  apply mul_nonneg (Nat.cast_nonneg _)
  nlinarith

theorem R_interior_local_majorant {r : ℕ} (hr : 3 ≤ r) {x : ℝ}
    (hxl : RCrossing r < x) (hxu : x < 1 / (r : ℝ)) :
    HasLocalQuadraticMajorant r x
      ((r : ℝ) * (1 - ((r : ℝ) - 1) * (1 - r * x)))
      ((r : ℝ) ^ 2 * ((r : ℝ) - 1)) := by
  apply R_local_majorant
  filter_upwards [isOpen_Ioo.mem_nhds
    (show x ∈ Ioo (RCrossing r) (1 / (r : ℝ)) from ⟨hxl, hxu⟩)] with y hy
  exact Phi_eq_R_after_crossing hr hy.1.le hy.2.le

end DensityHS.Graphon
