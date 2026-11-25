module

public import DensityHS.Graphon.StrictTransitionReduction
public import DensityHS.Graphon.LowTransitionAlgebra
public import DensityHS.Weighted.PeelingEquality

/-!
# Strict multiplier exclusion at the early crossings

Author and maintainer: Xizhi Liu.

The actual uncrossed witness has zero defect cost at these crossings.
Its genuine lower-order cover recursion contradicts the proved strict
Bellman inequality. No structural or numerical certificate is assumed.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set

variable {Ω : Type*} [MeasurableSpace Ω]

namespace UncrossedPeelingWitness

theorem BA_transition_exclusion {r : ℕ} (hr : 4 ≤ r) {W : Kernel Ω}
    {c : Ω → ℝ} {L θ : ℝ}
    (T : UncrossedPeelingWitness r W c (AStart r) L θ)
    (hL : L = 1 - 2 * Phi r (AStart r) + θ * AStart r)
    (hθ0 : (1 - AStart r) / ((r : ℝ) - 1) < θ)
    (hθ1 : θ < 4 * AStart r) : False := by
  have hr3 : 3 ≤ r := by omega
  have hx0 := AStart_pos hr3
  have hx1 := (AStart_lt_AEnd hr3).trans_le (A_endpoint_le (by omega))
  have hPhiB := Phi_eq_B_one_before_A hr3 hx0.le le_rfl
  have hPhiA := Phi_eq_A_on_middle_interval hr3 le_rfl (AStart_lt_AEnd hr3).le
  have hlow := peel_length_ordinary_endpoint (by omega : 1 < r) (AStart r)
  simp only [Nat.cast_one, one_mul] at hlow
  rw [← hPhiB] at hlow
  have hhigh : 1 - 2 * Phi r (AStart r) + (4 * AStart r) * AStart r =
      1 / ((r : ℝ) - 1) := by
    rw [hPhiA]
    have hden : (r : ℝ) - 1 ≠ 0 := by
      have hrR : (4 : ℝ) ≤ r := by exact_mod_cast hr
      linarith
    unfold A
    field_simp
    <;> ring
  have hL0 : (1 - AStart r) / ((r : ℝ) - 1) < L := by
    nlinarith [mul_pos (sub_pos.mpr hθ0) hx0]
  have hL1 : L < 1 / ((r : ℝ) - 1) := by
    nlinarith [mul_pos (sub_pos.mpr hθ1) hx0]
  obtain ⟨_, hLt, hLx, hLell⟩ := BA_transition_peel_bounds hr hL0 hL1
  have hθ : 0 < θ := by
    have hp := B_peel_length_pos (i := 1) (by omega : 1 < r) hx0.le hx1
    simp only [Nat.cast_one, one_mul] at hp
    exact hp.trans hθ0
  have hle := T.universal_peel hr3 hθ hLt hLx
    (hLell.trans_le (T.zeroMass_lower (by omega) ⟨hx0.le, hx1.le⟩))
  have hstrict := BA_transition_universal_peel_strict hr hL0 hL1
  unfold peelValue at hstrict
  nlinarith

theorem BB_transition_exclusion {r i : ℕ} (hi : 2 ≤ i) (hir : i ≤ r - 3)
    {W : Kernel Ω} {c : Ω → ℝ} {x L θ : ℝ}
    (T : UncrossedPeelingWitness r W c x L θ)
    (hx : x ∈ Icc 0 (1 / (r : ℝ)))
    (hiPhi : B r i x = Phi r x) (hjPhi : B r (i + 1) x = Phi r x)
    (hL : L = 1 - 2 * Phi r x + θ * x)
    (hθ0 : (i : ℝ) * (1 - i * x) / ((r : ℝ) - i) < θ)
    (hθ1 : θ < ((i + 1 : ℕ) : ℝ) * (1 - (i + 1 : ℕ) * x) /
      ((r : ℝ) - (i + 1 : ℕ))) : False := by
  have hr : 3 ≤ r := by omega
  have hcross := (B_eq_B_iff_crossing (by omega : i < i + 1)
    (by omega : i + 1 < r) hx.1 hx.2).mp (hiPhi.trans hjPhi.symm)
  have hx0 : 0 < x := by rw [hcross]; exact BCrossing_pos (by omega)
  have hx1 : x < 1 / (r : ℝ) := by
    rw [hcross]
    exact BCrossing_lt_right_endpoint (by omega : i < r) (by omega : i + 1 < r)
  have hlow := peel_length_ordinary_endpoint (by omega : i < r) x
  have hhigh := peel_length_ordinary_endpoint (by omega : i + 1 < r) x
  rw [hiPhi] at hlow
  rw [hjPhi] at hhigh
  have hL0 : (1 - (i : ℝ) * x) / ((r : ℝ) - i) < L := by
    nlinarith [mul_pos (sub_pos.mpr hθ0) hx0]
  have hL1 : L < (1 - ((i + 1 : ℕ) : ℝ) * x) / ((r : ℝ) - (i + 1 : ℕ)) := by
    nlinarith [mul_pos (sub_pos.mpr hθ1) hx0]
  obtain ⟨_, hLt, hLx, hLell⟩ := BB_transition_peel_bounds hi hir hcross hL0 hL1
  have hθ : 0 < θ := by
    have hp := B_peel_length_pos (i := i) (by omega : i < r) hx0.le hx1
    have hiR : (0 : ℝ) < i := by exact_mod_cast (by omega : 0 < i)
    have hprod := mul_pos hiR hp
    rw [← mul_div_assoc] at hprod
    exact hprod.trans hθ0
  have hle := T.universal_peel hr hθ hLt hLx
    (hLell.trans_le (T.zeroMass_lower (by omega) hx))
  have hstrict := BB_transition_universal_peel_strict hi hir hx hiPhi hjPhi hL0 hL1
  unfold peelValue at hstrict
  nlinarith

end UncrossedPeelingWitness

end DensityHS.Graphon
