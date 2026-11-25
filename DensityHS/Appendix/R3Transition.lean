module

public import DensityHS.Basic.Envelope
public import Mathlib.Tactic

/-!
# The strict scalar transition estimate at `B₃,₁ = A₃`

Author and maintainer: Xizhi Liu.

Both matching-envelope branches are bounded on the entire permitted interval.
For the concave branch, dropping its negative square gives a direct positive
polynomial certificate, avoiding a stationary-point case split.
-/

@[expose] public section

namespace DensityHS.Appendix

noncomputable def r3Cap (u : ℝ) : ℝ := (u + 1) ^ 2 / (9 * (9 * u + 14))

noncomputable def r3StarGap (u a : ℝ) : ℝ :=
  -u ^ 2 / 324 + ((13 * u - 14) / 72) * a - a ^ 2 / 2

noncomputable def r3CliqueGap (u a : ℝ) : ℝ :=
  -(2 - u) ^ 2 / 324 + ((9 * u - 50) / 72) * a + 2 * a ^ 2

theorem r3_star_linear_gap {u : ℝ} (hu : 0 < u) :
    u ^ 2 / 324 - ((13 * u - 14) / 72) * r3Cap u =
      (5 * u ^ 3 + 16 * u ^ 2 + 15 * u + 14) / (648 * (9 * u + 14)) := by
  have hden : 9 * u + 14 ≠ 0 := by positivity
  unfold r3Cap
  field_simp
  <;> ring

theorem r3_star_gap_neg {u a : ℝ} (hu : 0 < u) (ha : 0 ≤ a)
    (hcap : a ≤ r3Cap u) : r3StarGap u a < 0 := by
  have hlinear : ((13 * u - 14) / 72) * r3Cap u < u ^ 2 / 324 := by
    have hid := r3_star_linear_gap hu
    have hp : 0 < (5 * u ^ 3 + 16 * u ^ 2 + 15 * u + 14) /
        (648 * (9 * u + 14)) := by positivity
    linarith
  by_cases hb : 0 ≤ (13 * u - 14) / 72
  · have hmul := mul_le_mul_of_nonneg_left hcap hb
    unfold r3StarGap
    nlinarith [sq_nonneg a]
  · have hmul := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hb) ha
    unfold r3StarGap
    nlinarith [sq_pos_of_pos hu, sq_nonneg a]

theorem r3_cap_le_ninth {u : ℝ} (hu : 0 < u) (hu2 : u < 2) :
    r3Cap u ≤ 1 / 9 := by
  have hden : 0 < 9 * (9 * u + 14) := by positivity
  unfold r3Cap
  apply (div_le_iff₀ hden).mpr
  nlinarith [mul_nonneg hu.le (sub_nonneg.mpr hu2.le)]

theorem r3_clique_gap_neg {u a : ℝ} (hu : 0 < u) (hu2 : u < 2)
    (ha : 0 ≤ a) (hcap : a ≤ r3Cap u) : r3CliqueGap u a < 0 := by
  have ha9 : a ≤ 1 / 9 := hcap.trans (r3_cap_le_ninth hu hu2)
  have hcoef : (9 * u - 50) / 72 + 2 * a ≤ 0 := by linarith
  have hmul := mul_nonpos_of_nonneg_of_nonpos ha hcoef
  unfold r3CliqueGap
  nlinarith [sq_pos_of_pos (sub_pos.mpr hu2)]

/-- The exact strict inequality in the manuscript's clique-size-three
transition proposition, for every admissible interior multiplier and defect. -/
theorem r3_transition_estimate {u a : ℝ} (hu : 0 < u) (hu2 : u < 2)
    (ha : 0 ≤ a) (hcap : a ≤ (u + 1) ^ 2 / (9 * (9 * u + 14))) :
    let L := (u + 7) / 18
    let θ := (9 * u + 14) / 36
    L * (1 - L) + (1 - L) ^ 2 * Phi2 ((2 / 9 - a) / (1 - L)) + θ * a / 2 <
      113 / 324 := by
  let L := (u + 7) / 18
  let θ := (9 * u + 14) / 36
  let y := (2 / 9 - a) / (1 - L)
  have hL : 1 - L ≠ 0 := by dsimp [L]; linarith
  have hstarid : L * (1 - L) + (1 - L) ^ 2 * (y - y ^ 2 / 2) + θ * a / 2 -
      113 / 324 = r3StarGap u a := by
    dsimp only [y]
    field_simp [hL]
    <;> dsimp [L, θ, r3StarGap]
    <;> ring
  have hcliqueid : L * (1 - L) + (1 - L) ^ 2 * (2 * y ^ 2) + θ * a / 2 -
      113 / 324 = r3CliqueGap u a := by
    dsimp only [y]
    field_simp [hL]
    <;> dsimp [L, θ, r3CliqueGap]
    <;> ring
  have hstar : L * (1 - L) + (1 - L) ^ 2 * (y - y ^ 2 / 2) + θ * a / 2 <
      113 / 324 := by linarith [r3_star_gap_neg hu ha hcap]
  have hclique : L * (1 - L) + (1 - L) ^ 2 * (2 * y ^ 2) + θ * a / 2 <
      113 / 324 := by linarith [r3_clique_gap_neg hu hu2 ha hcap]
  change L * (1 - L) + (1 - L) ^ 2 * Phi2 y + θ * a / 2 < 113 / 324
  rw [Phi2, mul_max_of_nonneg _ _ (sq_nonneg (1 - L)), add_max, max_add]
  exact max_lt hstar hclique

end DensityHS.Appendix
