module

public import DensityHS.Appendix.R4Certificates

/-!
# The full strict transition estimate at `B₄,₂ = B₄,₃`

Author and maintainer: Xizhi Liu.

All branches of the rank-three envelope are handled on their actual feasible
domains.  The proof uses the exact range and Bernstein certificates established
in `R4Certificates`.
-/

@[expose] public section

namespace DensityHS.Appendix

noncomputable def r4Recursion (f : ℝ → ℝ) (L a : ℝ) : ℝ :=
  L * (1 - L) + (1 - L) ^ 2 * f ((r4X - a) / (1 - L)) + r4Theta L * a / 2

theorem r4_recursion_mono {f g : ℝ → ℝ} {L a : ℝ}
    (h : f ((r4X - a) / (1 - L)) ≤ g ((r4X - a) / (1 - L))) :
    r4Recursion f L a ≤ r4Recursion g L a := by
  unfold r4Recursion
  linarith [mul_le_mul_of_nonneg_left h (sq_nonneg (1 - L))]

theorem r4_B_evaluation {L : ℝ} (hL : 1 - L ≠ 0) (a : ℝ) :
    r4Recursion (B 3 2) L a = L * (1 - L) +
      2 * (1 - L) * (r4X - a) - 2 * (r4X - a) ^ 2 + r4Theta L * a / 2 := by
  unfold r4Recursion B
  norm_num
  field_simp
  <;> ring

theorem r4_B_gap_identity {L : ℝ} (hL : 1 - L ≠ 0) (a : ℝ) :
    r4Recursion (B 3 2) L a - r4F = r4BGap L a := by
  rw [r4_B_evaluation hL]
  unfold r4BGap r4C r4X r4F r4L2
  ring_nf
  rw [r4S_sq]
  ring

theorem r4_B_recursion_lt {L a : ℝ} (hL2 : r4L2 < L) (hL3 : L < r4L3)
    (ha : 0 ≤ a) : r4Recursion (B 3 2) L a < r4F := by
  have h := r4_B_gap_identity (r4_lambda_pos hL3).ne' a
  linarith [r4_B_gap_neg hL2 hL3 ha]

noncomputable def r4QuarterDefect (L : ℝ) : ℝ := r4X - (1 - L) / 4

theorem r4_quarter_defect_pos {L : ℝ} (hL : r4L2 < L) :
    0 < r4QuarterDefect L := by
  have hid : r4QuarterDefect L = (L - r4L2) / 4 + (5 - 3 * r4S) / 56 := by
    unfold r4QuarterDefect r4X r4L2
    ring
  rw [hid]
  linarith [r4S_bounds.2]

theorem r4_quarter_value {L : ℝ} (hL : 1 - L ≠ 0) :
    (r4X - r4QuarterDefect L) / (1 - L) = 1 / 4 := by
  unfold r4QuarterDefect
  field_simp
  <;> ring

theorem r4_R_evaluation {L : ℝ} (hL : 1 - L ≠ 0) (a : ℝ) :
    r4Recursion (R 3) L a = L * (1 - L) + (1 - L) ^ 2 / 2 -
      3 * (1 - L) * (r4X - a) + 9 * (r4X - a) ^ 2 + r4Theta L * a / 2 := by
  unfold r4Recursion R
  norm_num
  field_simp
  <;> ring

theorem r4_R_zero_identity {L : ℝ} (hL : 1 - L ≠ 0) :
    r4Recursion (R 3) L 0 - r4F =
      -((22 - 9 * r4S) / 14 - L) * (r4L3 - L) / 2 := by
  rw [r4_R_evaluation hL]
  unfold r4X r4F r4L3
  ring_nf
  rw [r4S_sq]
  ring

theorem r4_R_zero_lt {L : ℝ} (hL : L < r4L3) :
    r4Recursion (R 3) L 0 < r4F := by
  have hfirst : 0 < (22 - 9 * r4S) / 14 - L := by
    have hbase : r4L3 < (22 - 9 * r4S) / 14 := by
      unfold r4L3
      linarith [r4S_bounds.2]
    linarith
  have hprod : 0 < ((22 - 9 * r4S) / 14 - L) * (r4L3 - L) / 2 :=
    div_pos (mul_pos hfirst (sub_pos.mpr hL)) (by norm_num)
  have hid := r4_R_zero_identity (r4_lambda_pos hL).ne'
  linarith

theorem r4_R_quadratic {L : ℝ} (hL : 1 - L ≠ 0) (a : ℝ) :
    r4Recursion (R 3) L a - r4F =
      9 * a ^ 2 + (3 * (1 - L) - 18 * r4X + r4Theta L / 2) * a +
        (r4Recursion (R 3) L 0 - r4F) := by
  rw [r4_R_evaluation hL, r4_R_evaluation hL]
  ring

/-- A convex quadratic below zero at both ends is strictly below zero on
the whole interval. -/
theorem convex_quadratic_neg {Q R S a b : ℝ}
    (hQ : 0 ≤ Q) (hb : 0 < b) (ha : 0 ≤ a) (hab : a ≤ b)
    (h0 : S < 0) (h1 : Q * b ^ 2 + R * b + S < 0) :
    Q * a ^ 2 + R * a + S < 0 := by
  by_cases ha0 : a = 0
  · simpa [ha0] using h0
  have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hp0 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hab) h0.le
  have hp1 := mul_neg_of_pos_of_neg hapos h1
  have hp2 : 0 ≤ Q * a * b * (b - a) := by positivity
  have hproduct : b * (Q * a ^ 2 + R * a + S) < 0 := by
    nlinarith only [hp0, hp1, hp2]
  exact (mul_lt_mul_iff_right₀ hb).mp (by simpa using hproduct)

theorem R_three_le_B_two {y : ℝ} (hy : 2 / 9 ≤ y) (hyq : y ≤ 1 / 4) :
    R 3 y ≤ B 3 2 y := by
  unfold R B
  norm_num
  have hy0 : 0 ≤ y := by linarith
  nlinarith [mul_nonneg hy0 (sub_nonneg.mpr hyq)]

theorem r4_R_recursion_lt {L a : ℝ} (hL2 : r4L2 < L) (hL3 : L < r4L3)
    (ha : 0 ≤ a) (hy : 2 / 9 ≤ (r4X - a) / (1 - L)) :
    r4Recursion (R 3) L a < r4F := by
  have hlam := r4_lambda_pos hL3
  by_cases hyq : (r4X - a) / (1 - L) ≤ 1 / 4
  · exact (r4_recursion_mono (R_three_le_B_two hy hyq)).trans_lt
      (r4_B_recursion_lt hL2 hL3 ha)
  have hab : a ≤ r4QuarterDefect L := by
    have h := (lt_div_iff₀ hlam).mp (lt_of_not_ge hyq)
    unfold r4QuarterDefect
    linarith
  have hzero := r4_R_zero_lt hL3
  have hquarter : r4Recursion (R 3) L (r4QuarterDefect L) < r4F := by
    apply (r4_recursion_mono (f := R 3) (g := B 3 2) ?_).trans_lt
      (r4_B_recursion_lt hL2 hL3 (r4_quarter_defect_pos hL2).le)
    rw [r4_quarter_value hlam.ne']
    norm_num [R, B]
  have hquad := convex_quadratic_neg (by norm_num : (0 : ℝ) ≤ 9)
    (r4_quarter_defect_pos hL2) ha hab
    (show r4Recursion (R 3) L 0 - r4F < 0 by linarith)
    (show 9 * (r4QuarterDefect L) ^ 2 +
      (3 * (1 - L) - 18 * r4X + r4Theta L / 2) * r4QuarterDefect L +
        (r4Recursion (R 3) L 0 - r4F) < 0 by
      rw [← r4_R_quadratic hlam.ne']
      linarith)
  rw [← r4_R_quadratic hlam.ne'] at hquad
  linarith

theorem r4_chord_recursion {L : ℝ} (hL : 1 - L ≠ 0) (a : ℝ) :
    r4Chord L a =
      r4Recursion (fun y => 5 / 36 + (17 / 18) * y) L a - r4F := by
  unfold r4Chord r4Recursion
  field_simp
  <;> ring

theorem r4_chord_quarter_neg {L : ℝ} (hL2 : r4L2 < L) (hL3 : L < r4L3) :
    r4Chord L (r4QuarterDefect L) < 0 := by
  have hlam := r4_lambda_pos hL3
  have heq : r4Chord L (r4QuarterDefect L) =
      r4Recursion (B 3 2) L (r4QuarterDefect L) - r4F := by
    rw [r4_chord_recursion hlam.ne']
    unfold r4Recursion
    rw [r4_quarter_value hlam.ne']
    norm_num [B]
  rw [heq]
  linarith [r4_B_recursion_lt hL2 hL3 (r4_quarter_defect_pos hL2).le]

theorem r4_chord_affine (L a b : ℝ) :
    r4Chord L a - r4Chord L b =
      (r4Theta L / 2 - (17 / 18) * (1 - L)) * (a - b) := by
  unfold r4Chord
  ring

theorem r4_chord_neg {L a : ℝ} (hL2 : r4L2 < L) (hL3 : L < r4L3)
    (ha : r4QuarterDefect L ≤ a) (hcap : a ≤ r4Cap L) :
    r4Chord L a < 0 := by
  by_cases hc : 0 ≤ r4Theta L / 2 - (17 / 18) * (1 - L)
  · have hp := mul_nonpos_of_nonneg_of_nonpos hc (sub_nonpos.mpr hcap)
    have hid := r4_chord_affine L a (r4Cap L)
    linarith [r4_chord_cap_neg hL2 hL3]
  · have hp := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hc) (sub_nonneg.mpr ha)
    have hid := r4_chord_affine L a (r4QuarterDefect L)
    linarith [r4_chord_quarter_neg hL2 hL3]

theorem A_three_le_chord {y : ℝ} (hy : 2 / 9 ≤ y) (hyq : y ≤ 1 / 4) :
    A 3 y ≤ 5 / 36 + (17 / 18) * y := by
  unfold A
  norm_num
  nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - 4 * y)
    (by linarith : 0 ≤ 9 * y - 2)]

theorem r4_A_recursion_lt {L a : ℝ} (hL2 : r4L2 < L) (hL3 : L < r4L3)
    (hcap : a ≤ r4Cap L) (hy : 2 / 9 ≤ (r4X - a) / (1 - L))
    (hyq : (r4X - a) / (1 - L) ≤ 1 / 4) :
    r4Recursion (A 3) L a < r4F := by
  have hlam := r4_lambda_pos hL3
  have ha : r4QuarterDefect L ≤ a := by
    have h := (div_le_iff₀ hlam).mp hyq
    unfold r4QuarterDefect
    linarith
  have hc := r4_chord_neg hL2 hL3 ha hcap
  rw [r4_chord_recursion hlam.ne'] at hc
  have hm := r4_recursion_mono (f := A 3) (g := fun y => 5 / 36 + (17 / 18) * y)
    (L := L) (a := a) (A_three_le_chord hy hyq)
  linarith

theorem B_three_one_le_A {y : ℝ} (hy : 2 / 9 ≤ y) :
    B 3 1 y ≤ A 3 y := by
  unfold B A
  norm_num
  have hy0 : 0 ≤ y := by linarith
  nlinarith [mul_nonneg hy0 (by linarith : 0 ≤ 9 * y - 2)]

theorem B_three_one_le_two {y : ℝ} (hyq : 1 / 4 ≤ y) (hy : y ≤ 1 / 3) :
    B 3 1 y ≤ B 3 2 y := by
  unfold B
  norm_num
  nlinarith [mul_nonneg (sub_nonneg.mpr hyq) (sub_nonneg.mpr hy)]

theorem r4_B_one_recursion_lt {L a : ℝ} (hL2 : r4L2 < L) (hL3 : L < r4L3)
    (ha : 0 ≤ a) (hcap : a ≤ r4Cap L)
    (hy : 2 / 9 ≤ (r4X - a) / (1 - L))
    (hy3 : (r4X - a) / (1 - L) ≤ 1 / 3) :
    r4Recursion (B 3 1) L a < r4F := by
  by_cases hyq : (r4X - a) / (1 - L) ≤ 1 / 4
  · exact (r4_recursion_mono (B_three_one_le_A hy)).trans_lt
      (r4_A_recursion_lt hL2 hL3 hcap hy hyq)
  · exact (r4_recursion_mono (B_three_one_le_two (le_of_not_ge hyq) hy3)).trans_lt
      (r4_B_recursion_lt hL2 hL3 ha)

/-- The exact all-parameter strict estimate at the rank-four transition.
The envelope is evaluated on its genuine branch domains. -/
theorem r4_transition_estimate {L a : ℝ} (hL2 : r4L2 < L) (hL3 : L < r4L3)
    (ha : 0 ≤ a) (hcap : a ≤ r4Cap L) :
    L * (1 - L) + (1 - L) ^ 2 * Phi 3 ((r4X - a) / (1 - L)) +
      r4Theta L * a / 2 < r4F := by
  have hy := r4_y_range hL2 hL3 ha hcap
  have hbranch := Phi_mem_branchValues (by norm_num : 3 ≤ 3)
    ((r4X - a) / (1 - L))
  rcases hbranch with ⟨i, hi, hi3, heq⟩ | ⟨hdom, heq⟩ | ⟨_, heq⟩
  · have hi12 : i = 1 ∨ i = 2 := by omega
    rcases hi12 with rfl | rfl
    · rw [heq]
      exact r4_B_one_recursion_lt hL2 hL3 ha hcap hy.1.le hy.2.le
    · rw [heq]
      exact r4_B_recursion_lt hL2 hL3 ha
  · have hyq : (r4X - a) / (1 - L) ≤ 1 / 4 := by
      have h := hdom.2
      norm_num at h
      exact h
    rw [heq]
    exact r4_A_recursion_lt hL2 hL3 hcap hy.1.le hyq
  · rw [heq]
    exact r4_R_recursion_lt hL2 hL3 ha hy.1.le

end DensityHS.Appendix
