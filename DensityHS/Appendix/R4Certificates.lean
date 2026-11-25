module

public import DensityHS.Basic.Envelope
public import Mathlib.Tactic

/-!
# Polynomial certificates for the clique-size-four transition

Author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS.Appendix

noncomputable def r4S : ℝ := Real.sqrt 2
noncomputable def r4X : ℝ := (4 - r4S) / 14
noncomputable def r4F : ℝ := 3 * (29 - 2 * r4S) / 196
noncomputable def r4Delta : ℝ := (11 + 6 * r4S) / 98
noncomputable def r4Ell : ℝ := (2 * r4S - 1) / 7
noncomputable def r4L2 : ℝ := (3 + r4S) / 14
noncomputable def r4L3 : ℝ := (2 + 3 * r4S) / 14
noncomputable def r4Theta (L : ℝ) : ℝ := (L - r4Delta) / r4X
noncomputable def r4Cap (L : ℝ) : ℝ := L * (L - r4Ell) / r4Theta L
noncomputable def r4L (z : ℝ) : ℝ := r4L2 + z * (r4L3 - r4L2)

theorem r4S_sq : r4S ^ 2 = 2 := Real.sq_sqrt (by norm_num)
theorem r4S_cube : r4S ^ 3 = 2 * r4S := by rw [pow_succ, r4S_sq]
theorem r4S_four : r4S ^ 4 = 4 := by
  calc
    r4S ^ 4 = (r4S ^ 2) ^ 2 := by ring
    _ = 4 := by rw [r4S_sq]; norm_num
theorem r4S_five : r4S ^ 5 = 4 * r4S := by rw [pow_succ, r4S_four]

theorem r4S_bounds : 4 / 3 < r4S ∧ r4S < 3 / 2 := by
  have hs0 : 0 ≤ r4S := Real.sqrt_nonneg 2
  have hs2 := r4S_sq
  constructor <;> nlinarith

theorem r4X_pos : 0 < r4X := by
  unfold r4X
  linarith [r4S_bounds.2]

theorem r4_span_pos : 0 < r4L3 - r4L2 := by
  unfold r4L3 r4L2
  linarith [r4S_bounds.1]

theorem r4Theta_linear (L : ℝ) : r4Theta L = (4 + r4S) * (L - r4Delta) := by
  unfold r4Theta r4X
  have hne : 4 - r4S ≠ 0 := by linarith [r4S_bounds.2]
  field_simp
  ring_nf
  rw [r4S_sq]
  ring

theorem r4Theta_pos {L : ℝ} (hL : r4L2 < L) : 0 < r4Theta L := by
  rw [r4Theta_linear]
  have hbase : r4Delta < r4L2 := by
    unfold r4Delta r4L2
    linarith [r4S_bounds.1]
  exact mul_pos (by linarith [r4S_bounds.1]) (sub_pos.mpr (hbase.trans hL))

theorem r4_lambda_pos {L : ℝ} (hL : L < r4L3) : 0 < 1 - L := by
  have hupper : r4L3 < 1 := by unfold r4L3; linarith [r4S_bounds.2]
  linarith

theorem r4_parameter {L : ℝ} (hL2 : r4L2 < L) (hL3 : L < r4L3) :
    ∃ z : ℝ, 0 < z ∧ z < 1 ∧ L = r4L z := by
  let z := (L - r4L2) / (r4L3 - r4L2)
  refine ⟨z, div_pos (sub_pos.mpr hL2) r4_span_pos, ?_, ?_⟩
  · exact (div_lt_one r4_span_pos).mpr (by linarith)
  · unfold r4L
    have hmul : z * (r4L3 - r4L2) = L - r4L2 :=
      div_mul_cancel₀ _ r4_span_pos.ne'
    linarith

theorem r4_range_certificate (z : ℝ) :
    r4Theta (r4L z) * (r4X - 2 * (1 - r4L z) / 9) -
      r4L z * (r4L z - r4Ell) = (22 * r4S - 25) * (z - 1) ^ 2 / 1764 := by
  rw [r4Theta_linear]
  unfold r4L r4X r4Delta r4Ell r4L2 r4L3
  ring_nf
  simp only [r4S_sq, r4S_cube, r4S_four, r4S_five]
  ring

theorem r4_y_range {L a : ℝ} (hL2 : r4L2 < L) (hL3 : L < r4L3)
    (ha : 0 ≤ a) (hcap : a ≤ r4Cap L) :
    2 / 9 < (r4X - a) / (1 - L) ∧ (r4X - a) / (1 - L) < 1 / 3 := by
  have hθ := r4Theta_pos hL2
  have hlam := r4_lambda_pos hL3
  obtain ⟨z, hz0, hz1, hLz⟩ := r4_parameter hL2 hL3
  have hcert := r4_range_certificate z
  rw [← hLz] at hcert
  have hpositive : 0 < (22 * r4S - 25) * (z - 1) ^ 2 / 1764 := by
    apply div_pos
    · exact mul_pos (by linarith [r4S_bounds.1])
        (sq_pos_of_ne_zero (by linarith))
    · norm_num
  have hcapid : r4Theta L * r4Cap L = L * (L - r4Ell) := by
    unfold r4Cap
    exact mul_div_cancel₀ _ hθ.ne'
  have hbound : r4Cap L < r4X - 2 * (1 - L) / 9 := by
    apply (mul_lt_mul_iff_right₀ hθ).mp
    rw [hcapid]
    linarith
  have hxL : 3 * r4X = 1 - r4L3 := by unfold r4X r4L3; ring
  constructor
  · apply (lt_div_iff₀ hlam).mpr
    linarith
  · apply (div_lt_iff₀ hlam).mpr
    linarith

noncomputable def r4C (L : ℝ) : ℝ := 4 * r4X - 2 * (1 - L) + r4Theta L / 2
noncomputable def r4BGap (L a : ℝ) : ℝ :=
  -(L - r4L2) ^ 2 + r4C L * a - 2 * a ^ 2

theorem r4_coefficient_certificate (L : ℝ) :
    2 * r4S * (L - r4L2) - r4C L =
      (26 - 17 * r4S) / 28 + (r4L3 - L) * (4 - 3 * r4S / 2) := by
  unfold r4C
  rw [r4Theta_linear]
  unfold r4X r4Delta r4L2 r4L3
  ring_nf
  rw [r4S_sq]
  ring

theorem r4_B_gap_neg {L a : ℝ} (hL2 : r4L2 < L) (hL3 : L < r4L3)
    (ha : 0 ≤ a) : r4BGap L a < 0 := by
  have hcoeff : r4C L < 2 * r4S * (L - r4L2) := by
    have hid := r4_coefficient_certificate L
    have h0 : 0 < (26 - 17 * r4S) / 28 := by linarith [r4S_bounds.2]
    have h1 : 0 < (r4L3 - L) * (4 - 3 * r4S / 2) :=
      mul_pos (sub_pos.mpr hL3) (by linarith [r4S_bounds.2])
    linarith
  by_cases hC : r4C L ≤ 0
  · have hprod := mul_nonpos_of_nonpos_of_nonneg hC ha
    unfold r4BGap
    nlinarith [sq_pos_of_pos (sub_pos.mpr hL2), sq_nonneg a]
  · have hCpos : 0 < r4C L := lt_of_not_ge hC
    have hupperpos : 0 < 2 * r4S * (L - r4L2) :=
      hCpos.trans hcoeff
    have hsquare : (r4C L) ^ 2 < (2 * r4S * (L - r4L2)) ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr hcoeff) (add_pos hupperpos hCpos)]
    have hid : (2 * r4S * (L - r4L2)) ^ 2 = 8 * (L - r4L2) ^ 2 := by
      rw [mul_pow, mul_pow, r4S_sq]
      ring
    rw [hid] at hsquare
    unfold r4BGap
    nlinarith [sq_nonneg (4 * a - r4C L)]

/-- The affine chord majorant for the exceptional branch. -/
noncomputable def r4Chord (L a : ℝ) : ℝ :=
  L * (1 - L) + (5 / 36) * (1 - L) ^ 2 +
    (17 / 18) * (1 - L) * (r4X - a) + r4Theta L * a / 2 - r4F

noncomputable def r4Bernstein (z : ℝ) : ℝ :=
  ((610 - 331 * r4S) / 24696) * (1 - z) ^ 3 +
  3 * ((4502 - 1451 * r4S) / 296352) * z * (1 - z) ^ 2 +
  3 * ((249 * r4S - 205) / 18522) * z ^ 2 * (1 - z) +
  ((697 * r4S - 870) / 16464) * z ^ 3

theorem r4_Bernstein_pos {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    0 < r4Bernstein z := by
  have h0 : 0 < (610 - 331 * r4S) / 24696 := by linarith [r4S_bounds.2]
  have h1 : 0 < (4502 - 1451 * r4S) / 296352 := by linarith [r4S_bounds.2]
  have h2 : 0 < (249 * r4S - 205) / 18522 := by linarith [r4S_bounds.1]
  have h3 : 0 < (697 * r4S - 870) / 16464 := by linarith [r4S_bounds.1]
  have hz : 0 < 1 - z := sub_pos.mpr hz1
  unfold r4Bernstein
  positivity

theorem r4_chord_polynomial_certificate (z : ℝ) :
    r4Theta (r4L z) *
      (r4L z * (1 - r4L z) + (5 / 36) * (1 - r4L z) ^ 2 +
        (17 / 18) * (1 - r4L z) * r4X - r4F) +
      (r4Theta (r4L z) / 2 - (17 / 18) * (1 - r4L z)) *
        (r4L z * (r4L z - r4Ell)) = -r4Bernstein z := by
  rw [r4Theta_linear]
  unfold r4L r4X r4F r4Delta r4Ell r4L2 r4L3 r4Bernstein
  ring_nf
  simp only [r4S_sq, r4S_cube, r4S_four, r4S_five]
  ring

theorem r4_chord_cap_neg {L : ℝ} (hL2 : r4L2 < L) (hL3 : L < r4L3) :
    r4Chord L (r4Cap L) < 0 := by
  have hθ := r4Theta_pos hL2
  have hcapid : r4Theta L * r4Cap L = L * (L - r4Ell) := by
    unfold r4Cap
    exact mul_div_cancel₀ _ hθ.ne'
  obtain ⟨z, hz0, hz1, hLz⟩ := r4_parameter hL2 hL3
  have hcert := r4_chord_polynomial_certificate z
  rw [← hLz] at hcert
  have hid : r4Theta L * r4Chord L (r4Cap L) = -r4Bernstein z := by
    calc
      _ = r4Theta L *
          (L * (1 - L) + (5 / 36) * (1 - L) ^ 2 + (17 / 18) * (1 - L) * r4X - r4F) +
          (r4Theta L / 2 - (17 / 18) * (1 - L)) * (r4Theta L * r4Cap L) := by
        unfold r4Chord
        ring
      _ = _ := by rw [hcapid]; exact hcert
  apply (mul_lt_mul_iff_right₀ hθ).mp
  simpa only [mul_zero, hid] using neg_neg_of_pos (r4_Bernstein_pos hz0 hz1)

end DensityHS.Appendix
