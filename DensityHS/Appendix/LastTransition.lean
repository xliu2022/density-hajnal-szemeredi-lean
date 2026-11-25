module

public import DensityHS.Basic.PhaseActive

/-!
# The last adjacent transition in clique sizes at least five

The constants are written with `x = 1 / (d + 2 + sqrt 2)`, algebraically equal
to the paper's `omega * b`. This avoids unnecessary rationalizations.

Author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS.Appendix

noncomputable def lastX (d : ℝ) : ℝ := 1 / (d + 2 + Real.sqrt 2)
noncomputable def lastB (d : ℝ) : ℝ := (1 + Real.sqrt 2) * lastX d
noncomputable def lastL₀ (d : ℝ) : ℝ := (1 + Real.sqrt 2 / 2) * lastX d
noncomputable def lastEll (d : ℝ) : ℝ := Real.sqrt 2 * lastX d
noncomputable def lastF (d : ℝ) : ℝ := (1 - (lastB d) ^ 2) / 2
noncomputable def lastTheta (d L : ℝ) : ℝ := (L - (lastB d) ^ 2) / lastX d
noncomputable def lastA (d L : ℝ) : ℝ := L * (L - lastEll d) / lastTheta d L

noncomputable def lastP (d y : ℝ) : ℝ := d * y - d ^ 2 * y ^ 2 / 2
noncomputable def lastR (d y : ℝ) : ℝ :=
  1 / 2 - (1 - (d + 1) * y) + d / 2 * (1 - (d + 1) * y) ^ 2

noncomputable def lastCP (d L : ℝ) : ℝ := d ^ 2 * lastX d - d * (1 - L) + lastTheta d L / 2
noncomputable def lastCR (d L : ℝ) : ℝ :=
  (d + 1) * (d * (lastB d - L) - (1 - L)) + lastTheta d L / 2
noncomputable def lastK (d : ℝ) : ℝ := d * (d + 1) ^ 2 / 2
noncomputable def lastH (d L : ℝ) : ℝ :=
  (d - 3) * L + 2 - (d + 1) * lastB d
noncomputable def lastBracket (d L : ℝ) : ℝ :=
  d * lastB d - 1 + (4 - d) / 2 * L - (d + 1) / 2 * lastEll d

theorem last_sqrt_bounds : (1 : ℝ) < Real.sqrt 2 ∧ Real.sqrt 2 < 3 / 2 ∧ (Real.sqrt 2) ^ 2 = 2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  exact ⟨by nlinarith, by nlinarith, hs⟩

theorem lastX_pos {d : ℝ} (hd : 3 ≤ d) : 0 < lastX d := by
  unfold lastX
  exact div_pos (by norm_num) (by nlinarith [last_sqrt_bounds.1])

theorem lastX_identity {d : ℝ} (hd : 3 ≤ d) : (d + 2 + Real.sqrt 2) * lastX d = 1 := by
  have hden : d + 2 + Real.sqrt 2 ≠ 0 := by nlinarith [last_sqrt_bounds.1]
  simp [lastX, hden]

theorem one_sub_lastB {d : ℝ} (hd : 3 ≤ d) : 1 - lastB d = (d + 1) * lastX d := by
  have hx := lastX_identity hd
  unfold lastB
  nlinarith

theorem last_endpoints {d : ℝ} (hd : 3 ≤ d) :
    0 < lastEll d ∧ lastEll d < lastL₀ d ∧ lastL₀ d < lastB d ∧ lastB d < 1 := by
  have hx := lastX_pos hd
  have hs := last_sqrt_bounds
  have hgap : lastB d - lastL₀ d = Real.sqrt 2 * lastX d / 2 := by
    unfold lastB lastL₀
    ring
  have hlow : lastL₀ d - lastEll d = (1 - Real.sqrt 2 / 2) * lastX d := by
    unfold lastL₀ lastEll
    ring
  have hgap0 := mul_pos (by linarith : 0 < Real.sqrt 2) hx
  have hlow0 := mul_pos (by linarith : 0 < 1 - Real.sqrt 2 / 2) hx
  have h1 := one_sub_lastB hd
  have hright := mul_pos (by linarith : 0 < d + 1) hx
  exact ⟨mul_pos (by linarith) hx, by linarith, by linarith, by linarith⟩

/-- The stationarity parameter lies strictly between the two endpoint slopes. -/
theorem lastTheta_minus_low {d : ℝ} (hd : 3 ≤ d) (L : ℝ) :
    lastTheta d L - d * L = (2 + Real.sqrt 2) * (L - lastL₀ d) := by
  have hx := lastX_identity hd
  have hx0 := lastX_pos hd
  have hxl := congrArg (fun z : ℝ => L * z) hx
  have hsx := congrArg (fun z : ℝ => (lastX d) ^ 2 * z) last_sqrt_bounds.2.2
  unfold lastTheta lastB lastL₀
  field_simp [ne_of_gt hx0]
  <;> nlinarith

theorem lastTheta_below_high {d : ℝ} (hd : 3 ≤ d) (L : ℝ) :
    (d + 1) * L - lastTheta d L = (1 + Real.sqrt 2) * (lastB d - L) := by
  have hx := lastX_identity hd
  have hx0 := lastX_pos hd
  have hxl := congrArg (fun z : ℝ => L * z) hx
  have hxb := congrArg (fun z : ℝ => lastB d * z) hx
  unfold lastTheta lastB at *
  field_simp [ne_of_gt hx0]
  <;> nlinarith

theorem last_low_identity {d : ℝ} (hd : 3 ≤ d) : 2 * lastL₀ d = 1 - d * lastX d := by
  have hx := lastX_identity hd
  unfold lastL₀
  nlinarith

theorem lastB_sq {d : ℝ} : (lastB d) ^ 2 = 2 * (lastL₀ d) ^ 2 := by
  have hsx := congrArg (fun z : ℝ => (lastX d) ^ 2 * z) last_sqrt_bounds.2.2
  unfold lastB lastL₀
  nlinarith

theorem lastF_identity {d : ℝ} (hd : 3 ≤ d) :
    lastF d = d * lastX d - d ^ 2 * (lastX d) ^ 2 / 2 + (lastL₀ d) ^ 2 := by
  have hl := last_low_identity hd
  have hsq := congrArg (fun z : ℝ => z ^ 2) hl
  unfold lastF
  rw [lastB_sq]
  nlinarith

theorem lastTheta_range {d L : ℝ} (hd : 3 ≤ d)
    (hL0 : lastL₀ d < L) (hL1 : L < lastB d) :
    0 < L ∧ L < 1 ∧ lastEll d < L ∧ 0 < lastTheta d L ∧
      d * L < lastTheta d L ∧ lastTheta d L < (d + 1) * L := by
  have he := last_endpoints hd
  have hs := last_sqrt_bounds
  have hlow := lastTheta_minus_low hd L
  have hhigh := lastTheta_below_high hd L
  have hlo := mul_pos (by linarith : 0 < 2 + Real.sqrt 2) (sub_pos.mpr hL0)
  have hhi := mul_pos (by linarith : 0 < 1 + Real.sqrt 2) (sub_pos.mpr hL1)
  have hLp : 0 < L := he.1.trans (he.2.1.trans hL0)
  have hdL := mul_pos (by linarith : 0 < d) hLp
  exact ⟨hLp, hL1.trans he.2.2.2, he.2.1.trans hL0,
    by linarith, by linarith, by linarith⟩

theorem lastCP_at_lastB {d : ℝ} (hd : 3 ≤ d) :
    lastCP d (lastB d) = (1 - d + (d + 1) * Real.sqrt 2) * lastX d / 2 := by
  have hθ := lastTheta_below_high hd (lastB d)
  have hx := lastX_identity hd
  have hxd := congrArg (fun z : ℝ => d * z) hx
  unfold lastCP lastB at *
  nlinarith

theorem lastCP_gap_pos {d L : ℝ} (hd : 3 ≤ d) (hL1 : L < lastB d) :
    lastCP d L < Real.sqrt 2 * d * (L - lastL₀ d) := by
  have hs := last_sqrt_bounds
  have hx := lastX_pos hd
  have hθL := lastTheta_minus_low hd L
  have hθB := lastTheta_minus_low hd (lastB d)
  have hdiff : lastCP d L - lastCP d (lastB d) =
      (d + (d + 2 + Real.sqrt 2) / 2) * (L - lastB d) := by
    unfold lastCP
    nlinarith
  have hgap : lastB d - lastL₀ d = Real.sqrt 2 * lastX d / 2 := by
    unfold lastB lastL₀
    ring
  have hsdx := congrArg (fun z : ℝ => d * lastX d * z) hs.2.2
  have hendpoint : 0 < Real.sqrt 2 * d * (lastB d - lastL₀ d) - lastCP d (lastB d) := by
    rw [hgap, lastCP_at_lastB hd]
    have hnum : 0 < (3 - Real.sqrt 2) * d - 1 - Real.sqrt 2 := by
      have hm := mul_nonneg (by linarith : 0 ≤ 3 - Real.sqrt 2) (sub_nonneg.mpr hd)
      nlinarith
    have hpos := mul_pos hnum hx
    nlinarith
  have hslope : Real.sqrt 2 * d - (d + (d + 2 + Real.sqrt 2) / 2) < 0 := by
    have hm := mul_neg_of_neg_of_pos (by linarith : Real.sqrt 2 - 3 / 2 < 0) (by linarith : 0 < d)
    nlinarith
  have hmul := mul_nonneg_of_nonpos_of_nonpos hslope.le (sub_neg.mpr hL1).le
  nlinarith

theorem lastP_scaled (d x a L : ℝ) (hL : 1 - L ≠ 0) :
    (1 - L) ^ 2 * lastP d ((x - a) / (1 - L)) =
      d * (x - a) * (1 - L) - d ^ 2 * (x - a) ^ 2 / 2 := by
  unfold lastP
  field_simp
  <;> ring

theorem lastP_gap_identity {d L a : ℝ} (hd : 3 ≤ d) (hL : 1 - L ≠ 0) :
    L * (1 - L) + (1 - L) ^ 2 * lastP d ((lastX d - a) / (1 - L)) +
      lastTheta d L * a / 2 - lastF d =
        -(L - lastL₀ d) ^ 2 + lastCP d L * a - d ^ 2 * a ^ 2 / 2 := by
  rw [lastP_scaled _ _ _ _ hL, lastF_identity hd]
  have hl := congrArg (fun z : ℝ => L * z) (last_low_identity hd)
  unfold lastCP
  nlinarith

/-- The ordinary last branch is strictly below the transition value for all
nonnegative defects throughout the strict multiplier interval. -/
theorem lastP_transition_strict {d L a : ℝ} (hd : 3 ≤ d)
    (hL0 : lastL₀ d < L) (hL1 : L < lastB d) (ha : 0 ≤ a) :
    L * (1 - L) + (1 - L) ^ 2 * lastP d ((lastX d - a) / (1 - L)) +
      lastTheta d L * a / 2 < lastF d := by
  have hL := (lastTheta_range hd hL0 hL1).2.1
  have hgap := lastP_gap_identity (a := a) hd (by linarith : 1 - L ≠ 0)
  have hC := lastCP_gap_pos hd hL1
  have hs := last_sqrt_bounds.2.2
  have hsT := congrArg (fun z : ℝ => (L - lastL₀ d) ^ 2 * z) hs
  have hT : 0 < L - lastL₀ d := sub_pos.mpr hL0
  by_cases ha0 : a = 0
  · rw [ha0] at hgap ⊢
    nlinarith [sq_pos_of_pos hT]
  · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hCa := mul_lt_mul_of_pos_right hC ha'
    have hsq := sq_nonneg (Real.sqrt 2 * (L - lastL₀ d) - d * a)
    nlinarith

theorem lastH_at_low {d : ℝ} (hd : 3 ≤ d) :
    lastH d (lastL₀ d) = (4 * d - (d + 1) * Real.sqrt 2) * lastX d / 2 := by
  have hx := lastX_identity hd
  unfold lastH lastL₀ lastB
  nlinarith

theorem lastH_pos {d L : ℝ} (hd : 3 ≤ d) (hL0 : lastL₀ d < L) : 0 < lastH d L := by
  have hs := last_sqrt_bounds
  have hx := lastX_pos hd
  have hnum : 0 < 4 * d - (d + 1) * Real.sqrt 2 := by
    have hprod := mul_pos (by linarith : 0 < d + 1) (by linarith : 0 < 2 - Real.sqrt 2)
    nlinarith
  have hlow : 0 < lastH d (lastL₀ d) := by
    rw [lastH_at_low hd]
    exact div_pos (mul_pos hnum hx) (by norm_num)
  have hprod := mul_nonneg (sub_nonneg.mpr hd) (sub_pos.mpr hL0).le
  unfold lastH at *
  nlinarith

theorem lastBracket_at_low {d : ℝ} (hd : 3 ≤ d) :
    lastBracket d (lastL₀ d) = ((d - 2) * Real.sqrt 2 - 2 * d) * lastX d / 4 := by
  have hx := lastX_identity hd
  unfold lastBracket lastB lastEll lastL₀
  nlinarith

theorem lastBracket_at_high {d : ℝ} (hd : 3 ≤ d) :
    lastBracket d (lastB d) = (Real.sqrt 2 - d) * lastX d / 2 := by
  have hx := lastX_identity hd
  unfold lastBracket lastB lastEll
  nlinarith

theorem lastBracket_neg {d L : ℝ} (hd : 3 ≤ d)
    (hL0 : lastL₀ d < L) (hL1 : L < lastB d) : lastBracket d L < 0 := by
  have hs := last_sqrt_bounds
  have hx := lastX_pos hd
  have hlow : lastBracket d (lastL₀ d) < 0 := by
    rw [lastBracket_at_low hd]
    have hnum : (d - 2) * Real.sqrt 2 - 2 * d < 0 := by
      have hprod := mul_pos (by linarith : 0 < d - 2) (by linarith : 0 < 2 - Real.sqrt 2)
      nlinarith
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hnum hx) (by norm_num)
  have hhigh : lastBracket d (lastB d) < 0 := by
    rw [lastBracket_at_high hd]
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) hx) (by norm_num)
  by_cases hcoef : 0 ≤ (4 - d) / 2
  · have hprod := mul_nonneg hcoef (sub_pos.mpr hL1).le
    unfold lastBracket at *
    nlinarith
  · have hprod := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hcoef) (sub_pos.mpr hL0).le
    unfold lastBracket at *
    nlinarith

theorem lastA_le_simple {d L : ℝ} (hd : 3 ≤ d)
    (hL0 : lastL₀ d < L) (hL1 : L < lastB d) :
    lastA d L ≤ (L - lastEll d) / d := by
  have h := lastTheta_range hd hL0 hL1
  unfold lastA
  apply (div_le_div_iff₀ h.2.2.2.1 (by linarith : 0 < d)).mpr
  have hprod := mul_nonneg (sub_nonneg.mpr h.2.2.2.2.1.le) (sub_pos.mpr h.2.2.1).le
  nlinarith

theorem lastR_coefficient_neg {d L : ℝ} (hd : 3 ≤ d)
    (hL0 : lastL₀ d < L) (hL1 : L < lastB d) :
    lastCR d L + lastK d * lastA d L < 0 := by
  have h := lastTheta_range hd hL0 hL1
  have hA := lastA_le_simple hd hL0 hL1
  have hK : 0 ≤ lastK d := by unfold lastK; positivity
  have hKA := mul_le_mul_of_nonneg_left hA hK
  have hcancel : lastK d * ((L - lastEll d) / d) =
      (d + 1) ^ 2 / 2 * (L - lastEll d) := by
    unfold lastK
    field_simp
  rw [hcancel] at hKA
  have hupper : lastCR d L + lastK d * lastA d L ≤ (d + 1) * lastBracket d L := by
    unfold lastCR lastBracket
    have hθ := h.2.2.2.2.2
    nlinarith
  exact hupper.trans_lt (mul_neg_of_pos_of_neg (by linarith) (lastBracket_neg hd hL0 hL1))

theorem lastR_gap_identity {d L a : ℝ} (hd : 3 ≤ d) (hL : 1 - L ≠ 0) :
    L * (1 - L) + (1 - L) ^ 2 * lastR d ((lastX d - a) / (1 - L)) +
      lastTheta d L * a / 2 - lastF d =
        (L - lastB d) * lastH d L / 2 + lastCR d L * a + lastK d * a ^ 2 := by
  have hd1 : d + 1 ≠ 0 := by linarith
  have hx : lastX d = (1 - lastB d) / (d + 1) := by
    apply (eq_div_iff hd1).mpr
    nlinarith [one_sub_lastB hd]
  unfold lastR lastF lastH lastCR lastK
  rw [hx]
  field_simp
  <;> ring

/-- The terminal branch is strictly below the transition value on the full
allowed defect interval. -/
theorem lastR_transition_strict {d L a : ℝ} (hd : 3 ≤ d)
    (hL0 : lastL₀ d < L) (hL1 : L < lastB d) (ha : 0 ≤ a) (haA : a ≤ lastA d L) :
    L * (1 - L) + (1 - L) ^ 2 * lastR d ((lastX d - a) / (1 - L)) +
      lastTheta d L * a / 2 < lastF d := by
  have hL := (lastTheta_range hd hL0 hL1).2.1
  have hgap := lastR_gap_identity (a := a) hd (by linarith : 1 - L ≠ 0)
  have hH := lastH_pos hd hL0
  have hG0 : (L - lastB d) * lastH d L / 2 < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (sub_neg.mpr hL1) hH) (by norm_num)
  have hK : 0 ≤ lastK d := by unfold lastK; positivity
  have hC := lastR_coefficient_neg hd hL0 hL1
  have hKa := mul_le_mul_of_nonneg_left haA hK
  have hfac : lastCR d L + lastK d * a ≤ 0 := by linarith
  have hprod := mul_nonpos_of_nonneg_of_nonpos ha hfac
  nlinarith

theorem range_square_identity (x b ell q L : ℝ) (hx : x ≠ 0)
    (hlinear : (1 + ell - 2 * b) * x = q * (1 - b) ^ 2) :
    (L - b ^ 2) - L * (L - ell) - q * ((L - b ^ 2) / x) * (1 - L) =
      (q / x - 1) * (L - b) ^ 2 := by
  have hmul := congrArg (fun z : ℝ => L * z) hlinear
  field_simp
  <;> nlinarith

theorem lastX_le_range_lower {d : ℝ} (hd : 3 ≤ d) : lastX d ≤ d / (d + 1) ^ 2 := by
  have hs := last_sqrt_bounds
  have hden : 0 < d + 2 + Real.sqrt 2 := by linarith
  have hdp : 0 < d + 1 := by linarith
  unfold lastX
  apply (div_le_div_iff₀ hden (sq_pos_of_pos hdp)).mpr
  have hprod := mul_pos (by linarith : 0 < d) (by linarith : 0 < Real.sqrt 2 - 1)
  nlinarith

theorem last_range_lower_identity {d L : ℝ} (hd : 3 ≤ d)
    (hL0 : lastL₀ d < L) (hL1 : L < lastB d) :
    lastTheta d L * (lastX d - lastA d L - d / (d + 1) ^ 2 * (1 - L)) =
      (d / (d + 1) ^ 2 / lastX d - 1) * (L - lastB d) ^ 2 := by
  have hx := lastX_identity hd
  have hx0 := lastX_pos hd
  have hθ := (lastTheta_range hd hL0 hL1).2.2.2.1
  have hd1 : d + 1 ≠ 0 := by linarith
  have hlinear0 : 1 + lastEll d - 2 * lastB d = d * lastX d := by
    unfold lastEll lastB
    nlinarith
  have hlinear : (1 + lastEll d - 2 * lastB d) * lastX d =
      (d / (d + 1) ^ 2) * (1 - lastB d) ^ 2 := by
    rw [hlinear0, one_sub_lastB hd]
    field_simp
  have hθA : lastTheta d L * lastA d L = L * (L - lastEll d) := by
    unfold lastA
    field_simp
  have hθx : lastTheta d L * lastX d = L - (lastB d) ^ 2 := by
    unfold lastTheta
    field_simp
  calc
    _ = (L - (lastB d) ^ 2) - L * (L - lastEll d) -
        (d / (d + 1) ^ 2) * ((L - (lastB d) ^ 2) / lastX d) * (1 - L) := by
      rw [mul_sub, mul_sub, hθx, hθA]
      unfold lastTheta
      ring
    _ = _ := range_square_identity _ _ _ _ _ (ne_of_gt hx0) hlinear

/-- The full feasible defect interval stays beyond the last ordinary
transition for the smaller clique size. -/
theorem last_inner_parameter_range {d L a : ℝ} (hd : 3 ≤ d)
    (hL0 : lastL₀ d < L) (hL1 : L < lastB d) (ha : 0 ≤ a) (haA : a ≤ lastA d L) :
    d / (d + 1) ^ 2 ≤ (lastX d - a) / (1 - L) ∧
      (lastX d - a) / (1 - L) ≤ 1 / (d + 1) := by
  have h := lastTheta_range hd hL0 hL1
  have hmass : 0 < 1 - L := sub_pos.mpr h.2.1
  have hθ : 0 < lastTheta d L := h.2.2.2.1
  have hx := lastX_pos hd
  have hk : 0 ≤ d / (d + 1) ^ 2 / lastX d - 1 := by
    have hh := (one_le_div hx).mpr (lastX_le_range_lower hd)
    linarith
  have hbound : 0 ≤ lastTheta d L *
      (lastX d - lastA d L - d / (d + 1) ^ 2 * (1 - L)) := by
    rw [last_range_lower_identity hd hL0 hL1]
    exact mul_nonneg hk (sq_nonneg _)
  have hmon := mul_nonneg hθ.le (sub_nonneg.mpr haA)
  have hnew : 0 ≤ lastTheta d L * (lastX d - a - d / (d + 1) ^ 2 * (1 - L)) := by
    nlinarith
  have hnum := nonneg_of_mul_nonneg_right hnew hθ
  refine ⟨(le_div_iff₀ hmass).mpr (by linarith), ?_⟩
  apply (div_le_div_iff₀ hmass (by linarith : 0 < d + 1)).mpr
  have hb := one_sub_lastB hd
  have hprod := mul_nonneg (by linarith : 0 ≤ d + 1) ha
  nlinarith


/-- The lower endpoint of the feasible inner parameter interval lies strictly
past both the exceptional domain and the last ordinary crossing. -/
theorem last_range_lower_comparisons {d : ℝ} (hd : 3 ≤ d) :
    1 / (2 * d) < d / (d + 1) ^ 2 ∧
    1 / (d + 1 + Real.sqrt 2) < d / (d + 1) ^ 2 ∧
    (d - 1) / ((d + 1) * d) ≤ d / (d + 1) ^ 2 := by
  have hd0 : 0 < d := by linarith
  have hd1 : 0 < d + 1 := by linarith
  have hs := last_sqrt_bounds
  have hs43 : (4 : ℝ) / 3 < Real.sqrt 2 := by nlinarith
  have hsden : 0 < d + 1 + Real.sqrt 2 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · apply (div_lt_div_iff₀ (mul_pos (by norm_num) hd0) (sq_pos_of_pos hd1)).mpr
    have hprod := mul_nonneg (by linarith : 0 ≤ d - 3) (by linarith : 0 ≤ d + 1)
    nlinarith
  · apply (div_lt_div_iff₀ hsden (sq_pos_of_pos hd1)).mpr
    have hprod := mul_pos hd0 (by linarith : 0 < Real.sqrt 2 - 4 / 3)
    nlinarith
  · apply (div_le_div_iff₀ (mul_pos hd1 hd0) (sq_pos_of_pos hd1)).mpr
    nlinarith

/-- On the entire feasible inner interval, the full smaller-size envelope
is exactly the maximum of the last ordinary branch and the rigid branch. -/
theorem last_inner_Phi {d : ℕ} (hd : 3 ≤ d) {y : ℝ}
    (hylo : (d : ℝ) / ((d : ℝ) + 1) ^ 2 ≤ y)
    (hyhi : y ≤ 1 / ((d : ℝ) + 1)) :
    Phi (d + 1) y = max (lastP (d : ℝ) y) (lastR (d : ℝ) y) := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hcomp := last_range_lower_comparisons hdR
  have hy0 : 0 ≤ y := le_trans (by positivity) hylo
  have hA : AEnd (d + 1) < y := by
    simp only [AEnd, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    exact hcomp.1.trans_le hylo
  have hB : BCrossing (d + 1) ((d + 1) - 2) ((d + 1) - 1) ≤ y := by
    rw [last_BCrossing_eq (by omega : 3 ≤ d + 1)]
    simp only [Nat.cast_add, Nat.cast_one]
    exact hcomp.2.1.le.trans hylo
  have hR : RDomain (d + 1) y := by
    unfold RDomain
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    refine ⟨?_, hyhi⟩
    convert hcomp.2.2.trans hylo using 1 <;> ring
  have hPhi := Phi_eq_max_last_R (by omega : 3 ≤ d + 1)
    (x := y) ⟨hy0, by simpa using hyhi⟩ hA hB hR
  rw [hPhi]
  congr 1
  · unfold B lastP
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, add_sub_cancel_left, div_one]
    ring
  · unfold R lastR
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]

theorem lastF_le_Phi {d : ℕ} (hd : 3 ≤ d) :
    lastF (d : ℝ) ≤ Phi (d + 2) (lastX (d : ℝ)) := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hB : B (d + 2) (d + 1) (lastX (d : ℝ)) = lastF (d : ℝ) := by
    have hrel := one_sub_lastB hdR
    unfold B lastF
    simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
    rw [show (d : ℝ) + 2 - ((d : ℝ) + 1) = 1 by ring, div_one]
    rw [show 1 - ((d : ℝ) + 1) * lastX (d : ℝ) = lastB (d : ℝ) by linarith]
  rw [← hB]
  exact B_le_Phi (by omega) (by omega) (by omega) _

/-- The complete strict last-transition estimate for every clique size at
least five, including the entire feasible defect interval and the actual
restricted envelope on both sides. This is Proposition `last-general-transition`
with `d = r - 2`. -/
theorem last_general_transition_estimate {d : ℕ} (hd : 3 ≤ d) {L a : ℝ}
    (hL0 : lastL₀ (d : ℝ) < L) (hL1 : L < lastB (d : ℝ))
    (ha : 0 ≤ a) (haA : a ≤ lastA (d : ℝ) L) :
    L * (1 - L) + (1 - L) ^ 2 *
        Phi (d + 1) ((lastX (d : ℝ) - a) / (1 - L)) +
        lastTheta (d : ℝ) L * a / 2 < Phi (d + 2) (lastX (d : ℝ)) := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hyrange := last_inner_parameter_range hdR hL0 hL1 ha haA
  rw [last_inner_Phi hd hyrange.1 hyrange.2]
  apply lt_of_lt_of_le _ (lastF_le_Phi hd)
  by_cases hPR : lastP (d : ℝ) ((lastX (d : ℝ) - a) / (1 - L)) ≤
      lastR (d : ℝ) ((lastX (d : ℝ) - a) / (1 - L))
  · rw [max_eq_right hPR]
    exact lastR_transition_strict hdR hL0 hL1 ha haA
  · rw [max_eq_left (le_of_not_ge hPR)]
    exact lastP_transition_strict hdR hL0 hL1 ha


/-- Agreement with the paper's parameterization `b = 1/(1+(d+1)omega)`. -/
theorem lastB_paper_formula {d : ℝ} (hd : 3 ≤ d) :
    lastB d = 1 / (1 + (d + 1) * (Real.sqrt 2 - 1)) := by
  have hs := last_sqrt_bounds
  have hden : 0 < 1 + (d + 1) * (Real.sqrt 2 - 1) := by
    have hh := mul_pos (by linarith : 0 < d + 1) (by linarith : 0 < Real.sqrt 2 - 1)
    linarith
  apply (eq_div_iff (ne_of_gt hden)).mpr
  have hx := lastX_identity hd
  have hsq := congrArg (fun z : ℝ => ((d + 1) * lastX d) * z) hs.2.2
  unfold lastB
  nlinarith

theorem lastX_paper_formula (d : ℝ) :
    lastX d = (Real.sqrt 2 - 1) * lastB d := by
  have hsq := congrArg (fun z : ℝ => lastX d * z) last_sqrt_bounds.2.2
  unfold lastB
  nlinarith

theorem lastL₀_paper_formula (d : ℝ) :
    lastL₀ d = lastB d / Real.sqrt 2 := by
  have hs := last_sqrt_bounds
  apply (eq_div_iff (by linarith : Real.sqrt 2 ≠ 0)).mpr
  have hsq := congrArg (fun z : ℝ => lastX d * z) hs.2.2
  unfold lastL₀ lastB
  nlinarith

theorem lastEll_paper_formula (d : ℝ) :
    lastEll d = (2 - Real.sqrt 2) * lastB d := by
  have hsq := congrArg (fun z : ℝ => lastX d * z) last_sqrt_bounds.2.2
  unfold lastEll lastB
  nlinarith

/-- The same estimate indexed directly by the clique size `r ≥ 5`. -/
theorem last_transition_estimate {r : ℕ} (hr : 5 ≤ r) {L a : ℝ}
    (hL0 : lastL₀ ((r - 2 : ℕ) : ℝ) < L)
    (hL1 : L < lastB ((r - 2 : ℕ) : ℝ))
    (ha : 0 ≤ a) (haA : a ≤ lastA ((r - 2 : ℕ) : ℝ) L) :
    L * (1 - L) + (1 - L) ^ 2 *
        Phi (r - 1) ((lastX ((r - 2 : ℕ) : ℝ) - a) / (1 - L)) +
        lastTheta ((r - 2 : ℕ) : ℝ) L * a / 2 <
      Phi r (lastX ((r - 2 : ℕ) : ℝ)) := by
  have h := last_general_transition_estimate (by omega : 3 ≤ r - 2) hL0 hL1 ha haA
  simpa only [show r - 2 + 1 = r - 1 by omega, show r - 2 + 2 = r by omega] using h

end DensityHS.Appendix
