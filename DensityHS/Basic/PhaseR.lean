module

public import DensityHS.Basic.PhaseDiagram
public import DensityHS.Rainbow.Branch

/-!
# The unique active terminal crossing

The smaller zero-set root is inside the restricted `R` domain. The larger
root is outside that domain and cannot create an active intersection.

Author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS

noncomputable def RZeroCrossing (r : ℕ) : ℝ :=
  ((r : ℝ) ^ 2 - r + 1 - r * Real.sqrt ((r : ℝ) ^ 2 - 3 * r + 3)) /
    (((r : ℝ) - 1) * ((r : ℝ) ^ 2 + r - 1))

noncomputable def RUpperZeroCrossing (r : ℕ) : ℝ :=
  ((r : ℝ) ^ 2 - r + 1 + r * Real.sqrt ((r : ℝ) ^ 2 - 3 * r + 3)) /
    (((r : ℝ) - 1) * ((r : ℝ) ^ 2 + r - 1))

noncomputable def RCrossing (r : ℕ) : ℝ := (1 - RZeroCrossing r) / r

noncomputable def RCrossingPolynomial (r : ℕ) (ell : ℝ) : ℝ :=
  ((r : ℝ) - 1) * ((r : ℝ) ^ 2 + r - 1) * ell ^ 2 -
    2 * ((r : ℝ) ^ 2 - r + 1) * ell + 1

theorem RCrossing_discriminant {r : ℕ} (hr : 3 ≤ r) :
    ((r : ℝ) ^ 2 - r + 1) ^ 2 -
      (r * Real.sqrt ((r : ℝ) ^ 2 - 3 * r + 3)) ^ 2 =
        ((r : ℝ) - 1) * ((r : ℝ) ^ 2 + r - 1) := by
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hdis : 0 ≤ (r : ℝ) ^ 2 - 3 * r + 3 := by nlinarith [sq_nonneg ((r : ℝ) - 2)]
  rw [mul_pow, Real.sq_sqrt hdis]
  ring

theorem quadratic_root_factor (a b c ell : ℝ) (ha : a ≠ 0) :
    a * ((b - c) / a - ell) * ((b + c) / a - ell) =
      a * ell ^ 2 - 2 * b * ell + (b ^ 2 - c ^ 2) / a := by
  field_simp
  <;> ring

theorem RCrossingPolynomial_factor {r : ℕ} (hr : 3 ≤ r) (ell : ℝ) :
    RCrossingPolynomial r ell =
      (((r : ℝ) - 1) * ((r : ℝ) ^ 2 + r - 1)) *
        (RZeroCrossing r - ell) * (RUpperZeroCrossing r - ell) := by
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have ha : 0 < ((r : ℝ) - 1) * ((r : ℝ) ^ 2 + r - 1) :=
    mul_pos (by linarith) (by nlinarith [sq_nonneg (r : ℝ)])
  have hid := RCrossing_discriminant hr
  symm
  calc
    _ = (((r : ℝ) - 1) * ((r : ℝ) ^ 2 + r - 1)) * ell ^ 2 -
        2 * ((r : ℝ) ^ 2 - r + 1) * ell +
        (((r : ℝ) ^ 2 - r + 1) ^ 2 -
          (r * Real.sqrt ((r : ℝ) ^ 2 - 3 * r + 3)) ^ 2) /
            (((r : ℝ) - 1) * ((r : ℝ) ^ 2 + r - 1)) := by
      exact quadratic_root_factor _ _ _ _ (ne_of_gt ha)
    _ = RCrossingPolynomial r ell := by
      rw [hid, div_self (ne_of_gt ha)]
      rfl

theorem RZeroCrossing_pos {r : ℕ} (hr : 3 ≤ r) : 0 < RZeroCrossing r := by
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hs0 := Real.sqrt_nonneg ((r : ℝ) ^ 2 - 3 * r + 3)
  have ha : 0 < ((r : ℝ) - 1) * ((r : ℝ) ^ 2 + r - 1) :=
    mul_pos (by linarith) (by nlinarith [sq_nonneg (r : ℝ)])
  have hb : 0 < (r : ℝ) ^ 2 - r + 1 := by nlinarith [sq_nonneg ((r : ℝ) - 1)]
  have hid := RCrossing_discriminant hr
  have hrt : 0 ≤ (r : ℝ) * Real.sqrt ((r : ℝ) ^ 2 - 3 * r + 3) :=
    mul_nonneg (by linarith) hs0
  have hnum : 0 < (r : ℝ) ^ 2 - r + 1 - r * Real.sqrt ((r : ℝ) ^ 2 - 3 * r + 3) := by
    nlinarith
  exact div_pos hnum ha

theorem RZeroCrossing_lt_domain_end {r : ℕ} (hr : 3 ≤ r) :
    RZeroCrossing r < 1 / ((r : ℝ) - 1) := by
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hrm : 0 < (r : ℝ) - 1 := by linarith
  have ha : 0 < ((r : ℝ) - 1) * ((r : ℝ) ^ 2 + r - 1) :=
    mul_pos hrm (by nlinarith [sq_nonneg (r : ℝ)])
  have hs0 := Real.sqrt_nonneg ((r : ℝ) ^ 2 - 3 * r + 3)
  have hrt : 0 ≤ (r : ℝ) * Real.sqrt ((r : ℝ) ^ 2 - 3 * r + 3) :=
    mul_nonneg (by linarith) hs0
  unfold RZeroCrossing
  apply (div_lt_div_iff₀ ha hrm).mpr
  have hprod := mul_nonneg hrm.le hrt
  nlinarith [sq_pos_of_pos hrm]

theorem RUpperZeroCrossing_gt_domain_end {r : ℕ} (hr : 3 ≤ r) :
    1 / ((r : ℝ) - 1) < RUpperZeroCrossing r := by
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hrm : 0 < (r : ℝ) - 1 := by linarith
  have ha : 0 < ((r : ℝ) - 1) * ((r : ℝ) ^ 2 + r - 1) :=
    mul_pos hrm (by nlinarith [sq_nonneg (r : ℝ)])
  have hdis : 0 ≤ (r : ℝ) ^ 2 - 3 * r + 3 := by nlinarith [sq_nonneg ((r : ℝ) - 2)]
  have hs0 := Real.sqrt_nonneg ((r : ℝ) ^ 2 - 3 * r + 3)
  have hid : (r * Real.sqrt ((r : ℝ) ^ 2 - 3 * r + 3)) ^ 2 -
      (2 * ((r : ℝ) - 1)) ^ 2 = ((r : ℝ) - 2) ^ 2 * ((r : ℝ) ^ 2 + r - 1) := by
    rw [mul_pow, Real.sq_sqrt hdis]
    ring
  have hprod : 0 < ((r : ℝ) - 2) ^ 2 * ((r : ℝ) ^ 2 + r - 1) :=
    mul_pos (sq_pos_of_pos (by linarith)) (by nlinarith [sq_nonneg (r : ℝ)])
  have hrt : 0 ≤ (r : ℝ) * Real.sqrt ((r : ℝ) ^ 2 - 3 * r + 3) :=
    mul_nonneg (by linarith) hs0
  have hstrong : 2 * ((r : ℝ) - 1) < r * Real.sqrt ((r : ℝ) ^ 2 - 3 * r + 3) := by
    nlinarith
  unfold RUpperZeroCrossing
  apply (div_lt_div_iff₀ hrm ha).mpr
  have hmul := mul_pos hrm (sub_pos.mpr hstrong)
  nlinarith

theorem RCrossing_lt_right_endpoint {r : ℕ} (hr : 3 ≤ r) :
    RCrossing r < 1 / (r : ℝ) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  unfold RCrossing
  exact div_lt_div_of_pos_right (by linarith [RZeroCrossing_pos hr]) hrR

theorem RCrossing_gt_left_endpoint {r : ℕ} (hr : 3 ≤ r) :
    ((r : ℝ) - 2) / ((r : ℝ) * ((r : ℝ) - 1)) < RCrossing r := by
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (r : ℝ) ≠ 0 := by linarith
  have hr1 : (r : ℝ) - 1 ≠ 0 := by linarith
  calc
    _ = (1 - 1 / ((r : ℝ) - 1)) / r := by field_simp; ring
    _ < RCrossing r := div_lt_div_of_pos_right
      (by linarith [RZeroCrossing_lt_domain_end hr]) (by linarith)

theorem R_sub_B_last {r : ℕ} (hr : 3 ≤ r) (x : ℝ) :
    R r x - B r (r - 1) x = RCrossingPolynomial r (1 - (r : ℝ) * x) / (2 * (r : ℝ) ^ 2) := by
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  unfold R B RCrossingPolynomial
  rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
  have hden : (r : ℝ) - ((r : ℝ) - 1) = 1 := by ring
  rw [hden]
  field_simp
  <;> ring

theorem ell_mem_R_interval {r : ℕ} (hr : 3 ≤ r) {x : ℝ} (hx : RDomain r x) :
    0 ≤ 1 - (r : ℝ) * x ∧ 1 - (r : ℝ) * x ≤ 1 / ((r : ℝ) - 1) := by
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hr1 : (0 : ℝ) < (r : ℝ) - 1 := by linarith
  have hu := (le_div_iff₀ hr0).mp hx.2
  have hl := (div_le_iff₀ (mul_pos hr0 hr1)).mp hx.1
  refine ⟨by nlinarith, (le_div_iff₀ hr1).mpr ?_⟩
  nlinarith

/-- On its restricted domain, `R` overtakes the last ordinary branch at
exactly the smaller quadratic root. -/
theorem B_last_le_R_iff {r : ℕ} (hr : 3 ≤ r) {x : ℝ} (hx : RDomain r x) :
    B r (r - 1) x ≤ R r x ↔ RCrossing r ≤ x := by
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have ha : 0 < ((r : ℝ) - 1) * ((r : ℝ) ^ 2 + r - 1) :=
    mul_pos (by linarith) (by nlinarith [sq_nonneg (r : ℝ)])
  have hell := ell_mem_R_interval hr hx
  have hplus : 0 < RUpperZeroCrossing r - (1 - (r : ℝ) * x) := by
    linarith [RUpperZeroCrossing_gt_domain_end hr]
  rw [← sub_nonneg, R_sub_B_last hr, le_div_iff₀ (by positivity : 0 < 2 * (r : ℝ) ^ 2),
    zero_mul, RCrossingPolynomial_factor hr, mul_assoc,
    mul_nonneg_iff_of_pos_left ha, mul_nonneg_iff_of_pos_right hplus, sub_nonneg]
  unfold RCrossing
  rw [div_le_iff₀ hr0]
  constructor <;> intro h <;> nlinarith

theorem B_last_lt_R_iff {r : ℕ} (hr : 3 ≤ r) {x : ℝ} (hx : RDomain r x) :
    B r (r - 1) x < R r x ↔ RCrossing r < x := by
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have ha : 0 < ((r : ℝ) - 1) * ((r : ℝ) ^ 2 + r - 1) :=
    mul_pos (by linarith) (by nlinarith [sq_nonneg (r : ℝ)])
  have hell := ell_mem_R_interval hr hx
  have hplus : 0 < RUpperZeroCrossing r - (1 - (r : ℝ) * x) := by
    linarith [RUpperZeroCrossing_gt_domain_end hr]
  rw [← sub_pos, R_sub_B_last hr, lt_div_iff₀ (by positivity : 0 < 2 * (r : ℝ) ^ 2),
    zero_mul, RCrossingPolynomial_factor hr, mul_assoc,
    mul_pos_iff_of_pos_left ha, mul_pos_iff_of_pos_right hplus, sub_pos]
  unfold RCrossing
  rw [div_lt_iff₀ hr0]
  constructor <;> intro h <;> nlinarith

theorem R_le_B_last_iff {r : ℕ} (hr : 3 ≤ r) {x : ℝ} (hx : RDomain r x) :
    R r x ≤ B r (r - 1) x ↔ x ≤ RCrossing r := by
  rw [← not_lt, B_last_lt_R_iff hr hx, not_lt]

theorem R_eq_B_last_iff {r : ℕ} (hr : 3 ≤ r) {x : ℝ} (hx : RDomain r x) :
    R r x = B r (r - 1) x ↔ x = RCrossing r := by
  rw [le_antisymm_iff, R_le_B_last_iff hr hx, B_last_le_R_iff hr hx]
  exact ⟨fun h => le_antisymm h.1 h.2, fun h => by simp [h]⟩

theorem reciprocal_succ_mem_RDomain {r : ℕ} (hr : 3 ≤ r) :
    RDomain r (1 / ((r : ℝ) + 1)) := by
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hr1 : (0 : ℝ) < (r : ℝ) - 1 := by linarith
  constructor
  · apply (div_le_div_iff₀ (mul_pos hr0 hr1) (by linarith : 0 < (r : ℝ) + 1)).mpr
    nlinarith
  · exact one_div_le_one_div_of_le hr0 (by linarith)

/-- The terminal crossing occurs strictly after `1/(r+1)`, and hence after
the last adjacent ordinary crossing. -/
theorem RCrossing_gt_reciprocal_succ {r : ℕ} (hr : 3 ≤ r) :
    1 / ((r : ℝ) + 1) < RCrossing r := by
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hgap : 0 < B r (r - 1) (1 / ((r : ℝ) + 1)) - R r (1 / ((r : ℝ) + 1)) := by
    rw [B_last_sub_R (by omega), rainbowBranchGap_left hrR]
    exact div_pos (by linarith) (mul_pos (by norm_num) (sq_pos_of_pos (by linarith)))
  apply lt_of_not_ge
  intro h
  have hle := (B_last_le_R_iff hr (reciprocal_succ_mem_RDomain hr)).mpr h
  linarith

theorem AEnd_le_reciprocal_succ {r : ℕ} (hr : 3 ≤ r) :
    AEnd r ≤ 1 / ((r : ℝ) + 1) := by
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  unfold AEnd
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

theorem AEnd_lt_RCrossing {r : ℕ} (hr : 3 ≤ r) : AEnd r < RCrossing r :=
  (AEnd_le_reciprocal_succ hr).trans_lt (RCrossing_gt_reciprocal_succ hr)

theorem last_BCrossing_eq {r : ℕ} (hr : 3 ≤ r) :
    BCrossing r (r - 2) (r - 1) = 1 / ((r : ℝ) + Real.sqrt 2) := by
  unfold BCrossing
  rw [Nat.cast_sub (by omega : 2 ≤ r), Nat.cast_sub (by omega : 1 ≤ r)]
  norm_num

/-- The last ordinary crossing is strictly before the terminal `R` crossing. -/
theorem last_BCrossing_lt_RCrossing {r : ℕ} (hr : 3 ≤ r) :
    BCrossing r (r - 2) (r - 1) < RCrossing r := by
  apply lt_trans _ (RCrossing_gt_reciprocal_succ hr)
  rw [last_BCrossing_eq hr]
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hs : 1 < Real.sqrt 2 := by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]
  apply (div_lt_div_iff₀ (by positivity : 0 < (r : ℝ) + Real.sqrt 2)
    (by linarith : 0 < (r : ℝ) + 1)).mpr
  linarith

/-- Every point after the terminal crossing is in the restricted `R` domain. -/
theorem RDomain_of_after_crossing {r : ℕ} (hr : 3 ≤ r) {x : ℝ}
    (hxl : RCrossing r ≤ x) (hxu : x ≤ 1 / (r : ℝ)) : RDomain r x :=
  ⟨(RCrossing_gt_left_endpoint hr).le.trans hxl, hxu⟩

end DensityHS
