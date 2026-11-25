module

public import DensityHS.Basic.Envelope

/-!
# The branch relevant to the rainbow threshold

Author and maintainer: Xizhi Liu.

This file proves the exact envelope identity on the interval used by the
directed reduction. It does not assume a phase diagram or a rainbow tiling
theorem.
-/

@[expose] public section

namespace DensityHS

theorem B_last_sub_B {s i : ℕ} (hs : 2 ≤ s) (hi : i < s) (x : ℝ) :
    B s (s - 1) x - B s i x =
      ((s : ℝ) - i - 1) / 2 *
        (x ^ 2 - (1 - (s : ℝ) * x) ^ 2 / ((s : ℝ) - i)) := by
  have hsi : (s : ℝ) - i ≠ 0 := by
    have h : (i : ℝ) < s := by exact_mod_cast hi
    linarith
  simp only [B, Nat.cast_sub (by omega : 1 ≤ s), Nat.cast_one]
  field_simp
  <;> ring

theorem B_le_last_on_upper_interval {s i : ℕ} (hs : 3 ≤ s) (hi : i < s)
    {x : ℝ} (hxl : 1 / ((s : ℝ) + 1) ≤ x) (hxu : x ≤ 1 / (s : ℝ)) :
    B s i x ≤ B s (s - 1) x := by
  have hsR : (3 : ℝ) ≤ s := by exact_mod_cast hs
  have hs0 : (0 : ℝ) < s := by linarith
  have hx0 : 0 ≤ x := (by positivity : 0 ≤ 1 / ((s : ℝ) + 1)).trans hxl
  have hsmall : 0 ≤ 1 - (s : ℝ) * x := by
    have h := (le_div_iff₀ hs0).mp hxu
    nlinarith
  have hlarge : 1 - (s : ℝ) * x ≤ x := by
    have h := (div_le_iff₀ (by linarith : 0 < (s : ℝ) + 1)).mp hxl
    nlinarith
  have hj : (1 : ℝ) ≤ (s : ℝ) - i := by
    have h : (i : ℝ) + 1 ≤ s := by exact_mod_cast (Nat.succ_le_of_lt hi)
    linarith
  have hsq : (1 - (s : ℝ) * x) ^ 2 ≤ x ^ 2 := by nlinarith
  have hmul := mul_nonneg (by linarith : 0 ≤ (s : ℝ) - i - 1) (sq_nonneg x)
  have hd : (1 - (s : ℝ) * x) ^ 2 / ((s : ℝ) - i) ≤ x ^ 2 :=
    (div_le_iff₀ (by linarith : 0 < (s : ℝ) - i)).mpr (by nlinarith)
  have hdiff : 0 ≤ B s (s - 1) x - B s i x := by
    rw [B_last_sub_B (by omega) hi]
    exact mul_nonneg (by positivity) (sub_nonneg.mpr hd)
  linarith

/-- A concave quadratic is nonnegative between two nonnegative endpoints. -/
theorem concave_quadratic_nonneg_between {a b x c₀ c₁ c₂ : ℝ}
    (hab : a < b) (hax : a ≤ x) (hxb : x ≤ b) (hc₂ : 0 ≤ c₂)
    (ha : 0 ≤ c₀ + c₁ * a - c₂ * a ^ 2)
    (hb : 0 ≤ c₀ + c₁ * b - c₂ * b ^ 2) :
    0 ≤ c₀ + c₁ * x - c₂ * x ^ 2 := by
  have hprod := mul_nonneg (mul_nonneg hc₂ (sub_nonneg.mpr hax)) (sub_nonneg.mpr hxb)
  have hleft := mul_nonneg (sub_nonneg.mpr hxb) ha
  have hright := mul_nonneg (sub_nonneg.mpr hax) hb
  have hid : (b - a) * (c₀ + c₁ * x - c₂ * x ^ 2) =
      (b - x) * (c₀ + c₁ * a - c₂ * a ^ 2) +
      (x - a) * (c₀ + c₁ * b - c₂ * b ^ 2) +
      (b - a) * (c₂ * (x - a) * (b - x)) := by ring
  have hm := mul_nonneg (sub_pos.mpr hab).le hprod
  have hwhole : 0 ≤ (b - a) * (c₀ + c₁ * x - c₂ * x ^ 2) := by linarith
  exact (mul_nonneg_iff_of_pos_left (sub_pos.mpr hab)).mp hwhole

noncomputable def rainbowBranchGap (s x : ℝ) : ℝ :=
  -(s - 2) / 2 + (s ^ 2 - s - 1) * x - (s - 1) * (s ^ 2 + s - 1) / 2 * x ^ 2

theorem B_last_sub_R {s : ℕ} (hs : 2 ≤ s) (x : ℝ) :
    B s (s - 1) x - R s x = rainbowBranchGap s x := by
  simp only [B, R, rainbowBranchGap, Nat.cast_sub (by omega : 1 ≤ s), Nat.cast_one]
  have hden : (s : ℝ) - ((s : ℝ) - 1) = 1 := by ring
  rw [hden]
  ring

theorem rainbowBranchGap_left {s : ℝ} (hs : 3 ≤ s) :
    rainbowBranchGap s (1 / (s + 1)) = (s - 1) / (2 * (s + 1) ^ 2) := by
  unfold rainbowBranchGap
  field_simp
  <;> ring

theorem rainbowBranchGap_right {s : ℝ} (hs : 3 ≤ s) :
    rainbowBranchGap s (2 / (2 * s + 1)) = 3 * (s - 2) / (2 * (2 * s + 1) ^ 2) := by
  unfold rainbowBranchGap
  field_simp
  <;> ring

theorem R_le_B_last_on_rainbow_interval {s : ℕ} (hs : 3 ≤ s) {x : ℝ}
    (hxl : 1 / ((s : ℝ) + 1) ≤ x) (hxu : x ≤ 2 / (2 * (s : ℝ) + 1)) :
    R s x ≤ B s (s - 1) x := by
  have hsR : (3 : ℝ) ≤ s := by exact_mod_cast hs
  have hab : 1 / ((s : ℝ) + 1) < 2 / (2 * (s : ℝ) + 1) := by
    apply (div_lt_div_iff₀ (by linarith : 0 < (s : ℝ) + 1)
      (by linarith : 0 < 2 * (s : ℝ) + 1)).mpr
    linarith
  have ha : 0 ≤ rainbowBranchGap s (1 / ((s : ℝ) + 1)) := by
    rw [rainbowBranchGap_left hsR]
    exact div_nonneg (by linarith) (by positivity)
  have hb : 0 ≤ rainbowBranchGap s (2 / (2 * (s : ℝ) + 1)) := by
    rw [rainbowBranchGap_right hsR]
    exact div_nonneg (mul_nonneg (by norm_num) (by linarith)) (by positivity)
  have hgap : 0 ≤ rainbowBranchGap s x := by
    unfold rainbowBranchGap at ha hb ⊢
    apply concave_quadratic_nonneg_between hab hxl hxu _ ha hb
    exact div_nonneg (mul_nonneg (by linarith) (by nlinarith)) (by norm_num)
  rw [← B_last_sub_R (by omega) x] at hgap
  linarith

/-- Lemma `rainbow-branch`, first in its exact interval form. -/
theorem Phi_eq_B_last_on_rainbow_interval {s : ℕ} (hs : 3 ≤ s) {x : ℝ}
    (hxl : 1 / ((s : ℝ) + 1) ≤ x) (hxu : x ≤ 2 / (2 * (s : ℝ) + 1)) :
    Phi s x = B s (s - 1) x := by
  have hsR : (3 : ℝ) ≤ s := by exact_mod_cast hs
  have hx0 : 0 < x := (by positivity : 0 < 1 / ((s : ℝ) + 1)).trans_le hxl
  have hxr : x ≤ 1 / (s : ℝ) := by
    apply hxu.trans
    apply (div_le_div_iff₀ (by linarith : 0 < 2 * (s : ℝ) + 1)
      (by linarith : 0 < (s : ℝ))).mpr
    linarith
  apply le_antisymm
  · apply Phi_le hs
    · intro i _ hir
      exact B_le_last_on_upper_interval hs hir hxl hxr
    · intro hA
      have h1 := (div_le_iff₀ (by linarith : 0 < (s : ℝ) + 1)).mp hxl
      have h2 := (le_div_iff₀ (by linarith : 0 < 2 * ((s : ℝ) - 1))).mp hA.2
      have hsle : (s : ℝ) ≤ 3 := by nlinarith
      have hse : s = 3 := by exact_mod_cast (le_antisymm hsle hsR)
      subst s
      have hx : x = 1 / 4 := by norm_num at h1 h2; linarith
      subst x
      norm_num [A, B]
    · intro _
      exact R_le_B_last_on_rainbow_interval hs hxl hxu
  · exact B_le_Phi hs (by omega) (by omega) x

/-- The exact threshold in the paper's rainbow corollary. -/
noncomputable def rainbowThreshold (r : ℕ) : ℝ :=
  (2 * ((r : ℝ) - 1) + Real.sqrt ((r : ℝ) ^ 2 + 4 * r - 8)) / (3 * r)

theorem rainbowThreshold_radical_sq {r : ℕ} (hr : 4 ≤ r) :
    Real.sqrt ((r : ℝ) ^ 2 + 4 * r - 8) ^ 2 = (r : ℝ) ^ 2 + 4 * r - 8 := by
  have hrR : (4 : ℝ) ≤ r := by exact_mod_cast hr
  apply Real.sq_sqrt
  nlinarith [sq_nonneg (r : ℝ)]

theorem rainbowThreshold_ge_baseline {r : ℕ} (hr : 4 ≤ r) :
    (2 * (r : ℝ) - 1) / (2 * r) ≤ rainbowThreshold r := by
  have hrR : (4 : ℝ) ≤ r := by exact_mod_cast hr
  have hsq := rainbowThreshold_radical_sq hr
  have hroot := Real.sqrt_nonneg ((r : ℝ) ^ 2 + 4 * r - 8)
  have hlo : (r : ℝ) + 1 / 2 ≤ Real.sqrt ((r : ℝ) ^ 2 + 4 * r - 8) := by
    nlinarith
  unfold rainbowThreshold
  apply (div_le_div_iff₀ (by linarith : 0 < 2 * (r : ℝ))
    (by linarith : 0 < 3 * (r : ℝ))).mpr
  nlinarith

theorem rainbowThreshold_pos {r : ℕ} (hr : 4 ≤ r) : 0 < rainbowThreshold r := by
  have hrR : (4 : ℝ) ≤ r := by exact_mod_cast hr
  exact (div_pos (by linarith : 0 < 2 * (r : ℝ) - 1)
    (by linarith : 0 < 2 * (r : ℝ))).trans_le (rainbowThreshold_ge_baseline hr)

theorem rainbowThreshold_lt_one {r : ℕ} (hr : 4 ≤ r) : rainbowThreshold r < 1 := by
  have hrR : (4 : ℝ) ≤ r := by exact_mod_cast hr
  have hsq := rainbowThreshold_radical_sq hr
  have hroot := Real.sqrt_nonneg ((r : ℝ) ^ 2 + 4 * r - 8)
  have hhi : Real.sqrt ((r : ℝ) ^ 2 + 4 * r - 8) < (r : ℝ) + 2 := by nlinarith
  unfold rainbowThreshold
  apply (div_lt_one (by linarith : 0 < 3 * (r : ℝ))).mpr
  linarith

theorem rainbowThreshold_quadratic {r : ℕ} (hr : 4 ≤ r) :
    3 * (r : ℝ) ^ 2 * rainbowThreshold r ^ 2 -
      4 * r * ((r : ℝ) - 1) * rainbowThreshold r + ((r : ℝ) - 2) ^ 2 = 0 := by
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  have hs := rainbowThreshold_radical_sq hr
  rw [show (r : ℝ) ^ 2 + 4 * r - 8 = (r : ℝ) * (r + 4) - 8 by ring] at hs
  unfold rainbowThreshold
  field_simp
  nlinarith

/-- The branch identity with the original rainbow parameter. -/
theorem rainbow_branch {r : ℕ} (hr : 4 ≤ r) {ρ : ℝ}
    (hlo : rainbowThreshold r ≤ ρ) (hhi : ρ ≤ 1) :
    Phi (r - 1) (1 / ((r : ℝ) * ρ)) =
      ((r : ℝ) - 2) / ((r : ℝ) * ρ) -
        ((r : ℝ) - 2) ^ 2 / (2 * (r : ℝ) ^ 2 * ρ ^ 2) := by
  have hrR : (4 : ℝ) ≤ r := by exact_mod_cast hr
  have hρ : 0 < ρ := (rainbowThreshold_pos hr).trans_le hlo
  have hrpos : (0 : ℝ) < r := by linarith
  have hprod : 0 < (r : ℝ) * ρ := mul_pos hrpos hρ
  have hbase := (rainbowThreshold_ge_baseline hr).trans hlo
  have hlow : 1 / (r : ℝ) ≤ 1 / ((r : ℝ) * ρ) :=
    one_div_le_one_div_of_le hprod (by nlinarith)
  have hupp : 1 / ((r : ℝ) * ρ) ≤ 2 / (2 * (r : ℝ) - 1) := by
    apply (div_le_div_iff₀ hprod (by linarith : 0 < 2 * (r : ℝ) - 1)).mpr
    have h := (div_le_iff₀ (by linarith : 0 < 2 * (r : ℝ))).mp hbase
    nlinarith
  have hcast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
  have henv := Phi_eq_B_last_on_rainbow_interval (by omega : 3 ≤ r - 1)
    (x := 1 / ((r : ℝ) * ρ))
    (by simpa only [hcast, sub_add_cancel] using hlow)
    (by rw [hcast]; convert hupp using 1 <;> ring)
  rw [henv]
  have hcast2 : ((r - 1 - 1 : ℕ) : ℝ) = (r : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 1 ≤ r - 1), hcast, Nat.cast_one]
    ring
  unfold B
  rw [hcast, hcast2]
  have hd : ((r : ℝ) - 1) - ((r : ℝ) - 2) = 1 := by ring
  rw [hd]
  field_simp
  <;> ring

/-- The exact equality producing the contradiction in the directed proof. -/
theorem rainbow_envelope_threshold {r : ℕ} (hr : 4 ≤ r) :
    Phi (r - 1) (1 / ((r : ℝ) * rainbowThreshold r)) =
      (3 * rainbowThreshold r - 2) / (2 * rainbowThreshold r) := by
  rw [rainbow_branch hr le_rfl (rainbowThreshold_lt_one hr).le]
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  have hρ0 : rainbowThreshold r ≠ 0 := ne_of_gt (rainbowThreshold_pos hr)
  have hquad := rainbowThreshold_quadratic hr
  field_simp
  nlinarith

theorem rainbowThreshold_gt_absorption {r : ℕ} (hr : 4 ≤ r) :
    1 - 1 / (2 * ((r : ℝ) - 1)) < rainbowThreshold r := by
  have hrR : (4 : ℝ) ≤ r := by exact_mod_cast hr
  have hbase := rainbowThreshold_ge_baseline hr
  have hid : (2 * (r : ℝ) - 1) / (2 * r) = 1 - 1 / (2 * r) := by
    field_simp
    <;> ring
  rw [hid] at hbase
  have hinv : 1 / (2 * (r : ℝ)) < 1 / (2 * ((r : ℝ) - 1)) := by
    apply (div_lt_div_iff₀ (by linarith : 0 < 2 * (r : ℝ))
      (by linarith : 0 < 2 * ((r : ℝ) - 1))).mpr
    linarith
  linarith

end DensityHS
