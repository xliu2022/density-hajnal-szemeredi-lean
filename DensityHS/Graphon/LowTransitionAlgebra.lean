module

public import DensityHS.Appendix.R3Transition
public import DensityHS.Appendix.R4Transition
public import DensityHS.Appendix.LastTransition
public import DensityHS.Graphon.BranchVariation

/-!
# Native parameters for the low and last transition estimates

Author and maintainer: Xizhi Liu.

The appendix estimates are connected to the actual crossing parameters,
ordinary-branch derivatives, and `L = 1 - 2 Phi + theta x`.  The defect cap
is derived from the mass inequality produced by nested peeling.
-/

@[expose] public section

namespace DensityHS.Graphon

open DensityHS.Appendix

theorem peel_length_ordinary_endpoint {r i : ℕ} (hir : i < r) (x : ℝ) :
    1 - 2 * B r i x + ((i : ℝ) * (1 - i * x) / ((r : ℝ) - i)) * x =
      (1 - i * x) / ((r : ℝ) - i) := by
  have hden : (r : ℝ) - i ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (Nat.ne_of_gt hir))
  unfold B
  field_simp
  <;> ring

theorem nested_defect_cap {L θ ell a q z : ℝ} (hθ : 0 < θ)
    (hell : ell ≤ L) (hq0 : 0 ≤ q) (hqL : q ≤ L) (hz : ell ≤ z)
    (hdefect : θ * a ≤ q * (L - z)) : a ≤ L * (L - ell) / θ := by
  apply (le_div_iff₀ hθ).mpr
  have h₁ := mul_nonneg hq0 (sub_nonneg.mpr hz)
  have h₂ := mul_nonneg (sub_nonneg.mpr hqL) (sub_nonneg.mpr hell)
  nlinarith

theorem r3_transition_value : Phi 3 (2 / 9) = 113 / 324 := by
  rw [Phi_eq_B_one_before_A (by norm_num : 3 ≤ 3) (by norm_num)
    (by norm_num [AStart])]
  norm_num [B]

theorem r3_transition_native_bounds {L θ : ℝ}
    (hL : L = 1 - 2 * Phi 3 (2 / 9) + θ * (2 / 9))
    (hθ0 : 7 / 18 < θ) (hθ1 : θ < 8 / 9) :
    0 < θ ∧ L < θ ∧ 7 / 18 < L ∧ L < 1 / 2 := by
  rw [r3_transition_value] at hL
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The rank-three appendix estimate in the native multiplier variables. -/
theorem r3_native_transition_estimate {L θ a : ℝ}
    (hL : L = 1 - 2 * Phi 3 (2 / 9) + θ * (2 / 9))
    (hθ0 : 7 / 18 < θ) (hθ1 : θ < 8 / 9) (ha : 0 ≤ a)
    (hcap : a ≤ (L - 1 / 3) ^ 2 / θ) :
    L * (1 - L) + (1 - L) ^ 2 * Phi 2 ((2 / 9 - a) / (1 - L)) + θ * a / 2 <
      Phi 3 (2 / 9) := by
  have hb := r3_transition_native_bounds hL hθ0 hθ1
  let u := 18 * L - 7
  have hu0 : 0 < u := by dsimp [u]; linarith
  have hu2 : u < 2 := by dsimp [u]; linarith
  have hLu : L = (u + 7) / 18 := by dsimp [u]; ring
  have hθu : θ = (9 * u + 14) / 36 := by
    rw [r3_transition_value] at hL
    dsimp [u]
    linarith
  have hcapeq : (L - 1 / 3) ^ 2 / θ = (u + 1) ^ 2 / (9 * (9 * u + 14)) := by
    rw [hLu, hθu]
    field_simp
    <;> ring
  have h := r3_transition_estimate hu0 hu2 ha (hcapeq ▸ hcap)
  dsimp only at h
  rw [← hLu, ← hθu] at h
  simpa only [Phi_two, r3_transition_value] using h

theorem last_crossing_Phi {r : ℕ} (hr : 4 ≤ r) :
    Phi r (BCrossing r (r - 2) (r - 1)) = B r (r - 1) (BCrossing r (r - 2) (r - 1)) := by
  have hr3 : 3 ≤ r := by omega
  have hx0 := BCrossing_pos (r := r) (i := r - 2) (j := r - 1) (by omega)
  have hx1 := BCrossing_lt_right_endpoint (by omega : r - 2 < r) (by omega : r - 1 < r)
  have hA : AEnd r ≤ BCrossing r (r - 2) (r - 1) := by
    rw [last_BCrossing_eq hr3]
    unfold AEnd
    apply one_div_le_one_div_of_le
      (by have hrR : (4 : ℝ) ≤ r := by exact_mod_cast hr
          nlinarith [Real.sqrt_nonneg (2 : ℝ)])
    have hrR : (4 : ℝ) ≤ r := by exact_mod_cast hr
    nlinarith [last_sqrt_bounds.2.1]
  symm
  apply (B_active_iff_intervals hr3 (by omega) (by omega) ⟨hx0.le, hx1.le⟩).mpr
  refine ⟨⟨?_, ?_⟩, Or.inr hA, (last_BCrossing_lt_RCrossing hr3).le⟩
  · intro _
    simpa only [show r - 1 - 1 = r - 2 by omega] using
      (le_rfl : BCrossing r (r - 2) (r - 1) ≤ BCrossing r (r - 2) (r - 1))
  · intro h
    omega

/-- Exact conversion from native crossing data to the last-transition
appendix parameters.  It includes rank four, where `d = 2`. -/
theorem last_transition_native_parameters {r : ℕ} (hr : 4 ≤ r) {L θ : ℝ}
    (hL : L = 1 - 2 * Phi r (BCrossing r (r - 2) (r - 1)) +
      θ * BCrossing r (r - 2) (r - 1))
    (hθ0 : ((r - 2 : ℕ) : ℝ) * (1 - (r - 2 : ℕ) * BCrossing r (r - 2) (r - 1)) /
      ((r : ℝ) - (r - 2 : ℕ)) < θ)
    (hθ1 : θ < ((r - 1 : ℕ) : ℝ) * (1 - (r - 1 : ℕ) * BCrossing r (r - 2) (r - 1)) /
      ((r : ℝ) - (r - 1 : ℕ))) :
    BCrossing r (r - 2) (r - 1) = lastX ((r - 2 : ℕ) : ℝ) ∧
    lastL₀ ((r - 2 : ℕ) : ℝ) < L ∧ L < lastB ((r - 2 : ℕ) : ℝ) ∧
    θ = lastTheta ((r - 2 : ℕ) : ℝ) L ∧
    1 - r * BCrossing r (r - 2) (r - 1) = lastEll ((r - 2 : ℕ) : ℝ) := by
  let x := BCrossing r (r - 2) (r - 1)
  have hxpos : 0 < x := BCrossing_pos (by omega)
  have hrR : (4 : ℝ) ≤ r := by exact_mod_cast hr
  have hcast2 : ((r - 2 : ℕ) : ℝ) = (r : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ r)]
    norm_num
  have hcast1 : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ r)]
    norm_num
  have hden2 : (r : ℝ) - (r - 2 : ℕ) = 2 := by rw [hcast2]; ring
  have hden1 : (r : ℝ) - (r - 1 : ℕ) = 1 := by rw [hcast1]; ring
  have hxeq : x = lastX ((r - 2 : ℕ) : ℝ) := by
    dsimp [x]
    rw [last_BCrossing_eq (by omega : 3 ≤ r)]
    unfold lastX
    rw [hcast2]
    congr 1
    ring
  have hxm : ((r : ℝ) + Real.sqrt 2) * x = 1 := by
    dsimp [x]
    rw [last_BCrossing_eq (by omega : 3 ≤ r)]
    exact mul_one_div_cancel (by nlinarith [last_sqrt_bounds.1] : (r : ℝ) + Real.sqrt 2 ≠ 0)
  have hsmall : (1 - ((r - 2 : ℕ) : ℝ) * x) / ((r : ℝ) - (r - 2 : ℕ)) =
      lastL₀ ((r - 2 : ℕ) : ℝ) := by
    unfold lastL₀
    rw [← hxeq, hden2, hcast2]
    nlinarith
  have hbig : 1 - ((r - 1 : ℕ) : ℝ) * x = lastB ((r - 2 : ℕ) : ℝ) := by
    unfold lastB
    rw [← hxeq, hcast1]
    nlinarith
  have hPhi := last_crossing_Phi hr
  have hPhiSmall : Phi r x = B r (r - 2) x := by
    rw [hPhi]
    symm
    exact (B_eq_B_iff_crossing (by omega : r - 2 < r - 1) (by omega : r - 1 < r)
      hxpos.le (BCrossing_lt_right_endpoint (by omega : r - 2 < r) (by omega : r - 1 < r)).le).mpr rfl
  have hlow := peel_length_ordinary_endpoint (by omega : r - 2 < r) x
  have hhigh := peel_length_ordinary_endpoint (by omega : r - 1 < r) x
  rw [← hPhiSmall, hsmall] at hlow
  rw [← hPhi, hden1, div_one, hbig] at hhigh
  have hδ : 1 - 2 * Phi r x = (lastB ((r - 2 : ℕ) : ℝ)) ^ 2 := by
    rw [hPhi]
    unfold B
    rw [hden1, div_one, hbig]
    ring
  have hL0 : lastL₀ ((r - 2 : ℕ) : ℝ) < L := by
    have hp := mul_pos (sub_pos.mpr hθ0) hxpos
    change 0 < (θ - _) * x at hp
    nlinarith [hL, hlow]
  have hL1 : L < lastB ((r - 2 : ℕ) : ℝ) := by
    have hp := mul_pos (sub_pos.mpr hθ1) hxpos
    change 0 < (_ - θ) * x at hp
    rw [hden1, div_one] at hp
    nlinarith [hL, hhigh]
  refine ⟨hxeq, hL0, hL1, ?_, ?_⟩
  · unfold lastTheta
    rw [← hxeq]
    apply (eq_div_iff hxpos.ne').mpr
    nlinarith [hL, hδ]
  · unfold lastEll
    rw [← hxeq]
    nlinarith

theorem last_native_peel_bound {r : ℕ} (hr : 4 ≤ r) {L θ : ℝ}
    (hL : L = 1 - 2 * Phi r (BCrossing r (r - 2) (r - 1)) +
      θ * BCrossing r (r - 2) (r - 1))
    (hθ1 : θ < ((r - 1 : ℕ) : ℝ) * (1 - (r - 1 : ℕ) * BCrossing r (r - 2) (r - 1)) /
      ((r : ℝ) - (r - 1 : ℕ))) :
    L < 1 - ((r - 1 : ℕ) : ℝ) * BCrossing r (r - 2) (r - 1) ∧ L < 1 := by
  let x := BCrossing r (r - 2) (r - 1)
  have hx : 0 < x := BCrossing_pos (by omega)
  have hden : (r : ℝ) - (r - 1 : ℕ) = 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
    ring
  have he := peel_length_ordinary_endpoint (by omega : r - 1 < r) x
  rw [← last_crossing_Phi hr, hden, div_one] at he
  have hp := mul_pos (sub_pos.mpr hθ1) hx
  rw [hden, div_one] at hp
  have hlow : L < 1 - ((r - 1 : ℕ) : ℝ) * x := by nlinarith [hL, he]
  have hprod : 0 < ((r - 1 : ℕ) : ℝ) * x := mul_pos (by exact_mod_cast (show 0 < r - 1 by omega)) hx
  exact ⟨hlow, by linarith⟩

/-- The full last-transition inequality in native crossing and slope
variables; this applies to every clique size at least five. -/
theorem last_native_transition_estimate {r : ℕ} (hr : 5 ≤ r) {L θ a : ℝ}
    (hL : L = 1 - 2 * Phi r (BCrossing r (r - 2) (r - 1)) +
      θ * BCrossing r (r - 2) (r - 1))
    (hθ0 : ((r - 2 : ℕ) : ℝ) * (1 - (r - 2 : ℕ) * BCrossing r (r - 2) (r - 1)) /
      ((r : ℝ) - (r - 2 : ℕ)) < θ)
    (hθ1 : θ < ((r - 1 : ℕ) : ℝ) * (1 - (r - 1 : ℕ) * BCrossing r (r - 2) (r - 1)) /
      ((r : ℝ) - (r - 1 : ℕ))) (ha : 0 ≤ a)
    (hcap : a ≤ L * (L - (1 - r * BCrossing r (r - 2) (r - 1))) / θ) :
    L * (1 - L) + (1 - L) ^ 2 *
        Phi (r - 1) ((BCrossing r (r - 2) (r - 1) - a) / (1 - L)) + θ * a / 2 <
      Phi r (BCrossing r (r - 2) (r - 1)) := by
  obtain ⟨hx, hlow, hhigh, hθ, hell⟩ := last_transition_native_parameters (by omega : 4 ≤ r)
    hL hθ0 hθ1
  have hA : a ≤ lastA ((r - 2 : ℕ) : ℝ) L := by
    unfold lastA
    rw [← hθ, ← hell]
    exact hcap
  have h := last_transition_estimate hr hlow hhigh ha hA
  rwa [← hx, ← hθ] at h

theorem r4_last_constants :
    lastX 2 = r4X ∧ lastL₀ 2 = r4L2 ∧ lastB 2 = r4L3 ∧
      lastEll 2 = r4Ell ∧ (lastB 2) ^ 2 = r4Delta := by
  have hden : 4 + r4S ≠ 0 := by nlinarith [r4S_bounds.1]
  have hx : lastX 2 = r4X := by
    unfold lastX r4X
    norm_num only [show (2 : ℝ) + 2 = 4 by norm_num]
    change 1 / (4 + r4S) = (4 - r4S) / 14
    apply (div_eq_iff hden).2
    nlinarith [r4S_sq]
  have hlow : lastL₀ 2 = r4L2 := by
    unfold lastL₀
    rw [hx]
    unfold r4L2 r4X
    change (1 + r4S / 2) * ((4 - r4S) / 14) = (3 + r4S) / 14
    nlinarith [r4S_sq]
  have hhigh : lastB 2 = r4L3 := by
    unfold lastB
    rw [hx]
    unfold r4L3 r4X
    change (1 + r4S) * ((4 - r4S) / 14) = (2 + 3 * r4S) / 14
    nlinarith [r4S_sq]
  have hell : lastEll 2 = r4Ell := by
    unfold lastEll
    rw [hx]
    unfold r4Ell r4X
    change r4S * ((4 - r4S) / 14) = (2 * r4S - 1) / 7
    nlinarith [r4S_sq]
  refine ⟨hx, hlow, hhigh, hell, ?_⟩
  rw [hhigh]
  unfold r4L3 r4Delta
  nlinarith [r4S_sq]

theorem r4_transition_native_parameters {L θ : ℝ}
    (hL : L = 1 - 2 * Phi 4 (BCrossing 4 2 3) + θ * BCrossing 4 2 3)
    (hθ0 : 1 - 2 * BCrossing 4 2 3 < θ)
    (hθ1 : θ < 3 * (1 - 3 * BCrossing 4 2 3)) :
    BCrossing 4 2 3 = r4X ∧ r4L2 < L ∧ L < r4L3 ∧ θ = r4Theta L ∧
      1 - 4 * BCrossing 4 2 3 = r4Ell ∧ Phi 4 (BCrossing 4 2 3) = r4F := by
  have h0 : ((4 - 2 : ℕ) : ℝ) * (1 - (4 - 2 : ℕ) * BCrossing 4 (4 - 2) (4 - 1)) /
      ((4 : ℝ) - (4 - 2 : ℕ)) < θ := by norm_num; linarith
  have h1 : θ < ((4 - 1 : ℕ) : ℝ) * (1 - (4 - 1 : ℕ) * BCrossing 4 (4 - 2) (4 - 1)) /
      ((4 : ℝ) - (4 - 1 : ℕ)) := by norm_num; exact hθ1
  obtain ⟨hx, hlow, hhigh, hθ, hell⟩ :=
    last_transition_native_parameters (by norm_num : 4 ≤ 4) hL h0 h1
  change BCrossing 4 2 3 = lastX 2 at hx
  change lastL₀ 2 < L at hlow
  change L < lastB 2 at hhigh
  change θ = lastTheta 2 L at hθ
  change 1 - 4 * BCrossing 4 2 3 = lastEll 2 at hell
  obtain ⟨hx4, hlow4, hhigh4, hell4, hdelta⟩ := r4_last_constants
  have hθ4 : θ = r4Theta L := by
    rw [hθ]
    unfold lastTheta r4Theta
    rw [hdelta, hx4]
  refine ⟨hx.trans hx4, hlow4 ▸ hlow, hhigh4 ▸ hhigh, hθ4, hell.trans hell4, ?_⟩
  rw [last_crossing_Phi (by norm_num : 4 ≤ 4), hx, hx4]
  unfold B r4X r4F
  norm_num
  nlinarith [r4S_sq]

/-- The rank-four appendix inequality in native crossing and slope
variables. -/
theorem r4_native_transition_estimate {L θ a : ℝ}
    (hL : L = 1 - 2 * Phi 4 (BCrossing 4 2 3) + θ * BCrossing 4 2 3)
    (hθ0 : 1 - 2 * BCrossing 4 2 3 < θ)
    (hθ1 : θ < 3 * (1 - 3 * BCrossing 4 2 3)) (ha : 0 ≤ a)
    (hcap : a ≤ L * (L - (1 - 4 * BCrossing 4 2 3)) / θ) :
    L * (1 - L) + (1 - L) ^ 2 * Phi 3 ((BCrossing 4 2 3 - a) / (1 - L)) + θ * a / 2 <
      Phi 4 (BCrossing 4 2 3) := by
  obtain ⟨hx, hlow, hhigh, hθ, hell, hPhi⟩ := r4_transition_native_parameters hL hθ0 hθ1
  have hA : a ≤ r4Cap L := by
    unfold r4Cap
    rw [← hθ, ← hell]
    exact hcap
  have h := r4_transition_estimate hlow hhigh ha hA
  rwa [← hx, ← hθ, ← hPhi] at h

end DensityHS.Graphon
