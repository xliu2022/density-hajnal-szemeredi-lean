module

public import DensityHS.Graphon.TransitionBranches

/-!
# The actual two-sided quadratic inputs at all phase crossings

Author and maintainer: Xizhi Liu.

These are consequences of the complete phase diagram. No local envelope
identity or slope-order assumption remains in the concrete crossing results.
-/

@[expose] public section

namespace DensityHS.Graphon

open Set Filter
open scoped Topology

theorem hasLocalTwoBranchMajorant_of_eventually_branches {r : ℕ}
    {x mL mR kL kR : ℝ} {F G : ℝ → ℝ}
    (hbranches : ∀ᶠ y in 𝓝 x,
      (y ≤ x → Phi r y = F y) ∧ (x ≤ y → Phi r y = G y))
    (hF : ∀ y, F y = F x + mL * (y - x) + (kL / 2) * (y - x)^2)
    (hG : ∀ y, G y = G x + mR * (y - x) + (kR / 2) * (y - x)^2) :
    HasLocalTwoBranchMajorant r x mL mR kL kR := by
  obtain ⟨δ, hδ, hloc⟩ := Metric.eventually_nhds_iff.mp hbranches
  have hcenter := hloc (show dist x x < δ by simpa using hδ)
  refine ⟨δ, hδ, ?_⟩
  intro y hy
  have hnear := hloc (show dist y x < δ by simpa only [Real.dist_eq] using hy)
  constructor
  · intro h
    rw [hnear.1 h, hcenter.1 le_rfl]
    exact (hF y).le
  · intro h
    rw [hnear.2 h, hcenter.2 le_rfl]
    exact (hG y).le

theorem twoBranch_slopes_ordered {r : ℕ}
    {x mL mR kL kR : ℝ} {F G : ℝ → ℝ}
    (hbranches : ∀ᶠ y in 𝓝 x,
      (y ≤ x → Phi r y = F y) ∧ (x ≤ y → Phi r y = G y))
    (hlower : ∀ᶠ y in 𝓝 x, G y ≤ Phi r y)
    (hF : ∀ y, F y = F x + mL * (y - x) + (kL / 2) * (y - x)^2)
    (hG : ∀ y, G y = G x + mR * (y - x) + (kR / 2) * (y - x)^2) : mL ≤ mR := by
  have he : ∀ᶠ y in 𝓝 x,
      ((y ≤ x → Phi r y = F y) ∧ (x ≤ y → Phi r y = G y)) ∧ G y ≤ Phi r y :=
    hbranches.and hlower
  obtain ⟨δ, hδ, hloc⟩ := Metric.eventually_nhds_iff.mp he
  have hcenter := (hloc (show dist x x < δ by simpa using hδ)).1
  have hFG : F x = G x := (hcenter.1 le_rfl).symm.trans (hcenter.2 le_rfl)
  have hp : ∀ t : ℝ, -δ < t → t < 0 →
      (mR - mL) * t + ((kR - kL) / 2) * t^2 ≤ 0 := by
    intro t ht ht0
    have hnear := hloc (show dist (x + t) x < δ by
      rw [Real.dist_eq, add_sub_cancel_left, abs_of_neg ht0]
      linarith)
    have hdom : G (x + t) ≤ F (x + t) := by
      simpa only [hnear.1.1 (by linarith : x + t ≤ x)] using hnear.2
    rw [hF, hG, hFG] at hdom
    simp only [add_sub_cancel_left] at hdom
    nlinarith
  have h := DensityHS.Analysis.local_left_linear_nonneg (a := mR - mL)
    (b := (kR - kL) / 2) hδ hp
  linarith

theorem AStart_twoBranch_majorant {r : ℕ} (hr : 3 ≤ r) :
    HasLocalTwoBranchMajorant r (AStart r)
      ((1 - AStart r) / ((r : ℝ) - 1)) (4 * AStart r)
      (-1 / ((r : ℝ) - 1)) 4 ∧
      (1 - AStart r) / ((r : ℝ) - 1) ≤ 4 * AStart r := by
  have hF : ∀ y, B r 1 y = B r 1 (AStart r) +
      ((1 - AStart r) / ((r : ℝ) - 1)) * (y - AStart r) +
        ((-1 / ((r : ℝ) - 1)) / 2) * (y - AStart r)^2 := by
    intro y
    simpa only [Nat.cast_one, one_mul, one_pow] using B_quadratic_expansion r 1 (AStart r) y
  have hG := A_quadratic_expansion r (AStart r)
  have hbranches := AStart_eventually_branches hr
  have hlower : ∀ᶠ y in 𝓝 (AStart r), A r y ≤ Phi r y := by
    have hnear : ∀ᶠ y in 𝓝 (AStart r), y ∈ Ioo 0 (AEnd r) :=
      isOpen_Ioo.mem_nhds ⟨AStart_pos hr, AStart_lt_AEnd hr⟩
    exact hnear.mono (fun y hy => A_le_Phi hr ⟨hy.1.le, hy.2.le⟩)
  exact ⟨hasLocalTwoBranchMajorant_of_eventually_branches hbranches hF hG,
    twoBranch_slopes_ordered hbranches hlower hF hG⟩

theorem AEnd_twoBranch_majorant {r : ℕ} (hr : 3 ≤ r) :
    HasLocalTwoBranchMajorant r (AEnd r) (4 * AEnd r)
      (2 * (1 - 2 * AEnd r) / ((r : ℝ) - 2))
      4 (-(2 : ℝ)^2 / ((r : ℝ) - 2)) ∧
      4 * AEnd r ≤ 2 * (1 - 2 * AEnd r) / ((r : ℝ) - 2) := by
  have hF := A_quadratic_expansion r (AEnd r)
  have hG := B_quadratic_expansion r 2 (AEnd r)
  have hbranches := AEnd_eventually_branches hr
  have hlower : ∀ᶠ y in 𝓝 (AEnd r), B r 2 y ≤ Phi r y :=
    Eventually.of_forall (fun y => B_le_Phi hr (by omega) (by omega) y)
  exact ⟨hasLocalTwoBranchMajorant_of_eventually_branches hbranches hF hG,
    twoBranch_slopes_ordered hbranches hlower hF hG⟩

theorem AEnd_slopes_equal {r : ℕ} (hr : 3 ≤ r) :
    4 * AEnd r = 2 * (1 - 2 * AEnd r) / ((r : ℝ) - 2) := by
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have h1 : (r : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (r : ℝ) - 2 ≠ 0 := by linarith
  unfold AEnd
  field_simp
  <;> ring

theorem ordinary_coactive_twoBranch_majorant {r i j : ℕ} (hr : 3 ≤ r)
    (hi : 1 ≤ i) (hij : i < j) (hjr : j < r) {x : ℝ}
    (hx : x ∈ Icc 0 (1 / (r : ℝ)))
    (hiPhi : B r i x = Phi r x) (hjPhi : B r j x = Phi r x) :
    HasLocalTwoBranchMajorant r x
      ((i : ℝ) * (1 - i * x) / ((r : ℝ) - i))
      ((j : ℝ) * (1 - j * x) / ((r : ℝ) - j))
      (-(i : ℝ)^2 / ((r : ℝ) - i)) (-(j : ℝ)^2 / ((r : ℝ) - j)) ∧
      (i : ℝ) * (1 - i * x) / ((r : ℝ) - i) ≤
        (j : ℝ) * (1 - j * x) / ((r : ℝ) - j) := by
  have hF := B_quadratic_expansion r i x
  have hG := B_quadratic_expansion r j x
  have hbranches := ordinary_coactive_eventually_branches hr hi hij hjr hx hiPhi hjPhi
  have hlower : ∀ᶠ y in 𝓝 x, B r j y ≤ Phi r y :=
    Eventually.of_forall (fun y => B_le_Phi hr (by omega) hjr y)
  exact ⟨hasLocalTwoBranchMajorant_of_eventually_branches hbranches hF hG,
    twoBranch_slopes_ordered hbranches hlower hF hG⟩

theorem RCrossing_twoBranch_majorant {r : ℕ} (hr : 3 ≤ r) :
    HasLocalTwoBranchMajorant r (RCrossing r)
      (((r - 1 : ℕ) : ℝ) * (1 - (r - 1 : ℕ) * RCrossing r) /
        ((r : ℝ) - (r - 1 : ℕ)))
      ((r : ℝ) * (1 - ((r : ℝ) - 1) * (1 - r * RCrossing r)))
      (-((r - 1 : ℕ) : ℝ)^2 / ((r : ℝ) - (r - 1 : ℕ)))
      ((r : ℝ)^2 * ((r : ℝ) - 1)) ∧
      (((r - 1 : ℕ) : ℝ) * (1 - (r - 1 : ℕ) * RCrossing r) /
        ((r : ℝ) - (r - 1 : ℕ))) ≤
      (r : ℝ) * (1 - ((r : ℝ) - 1) * (1 - r * RCrossing r)) := by
  have hF := B_quadratic_expansion r (r - 1) (RCrossing r)
  have hG := R_quadratic_expansion r (RCrossing r)
  have hbranches := RCrossing_eventually_branches hr
  have hlower : ∀ᶠ y in 𝓝 (RCrossing r), R r y ≤ Phi r y := by
    have hnear : ∀ᶠ y in 𝓝 (RCrossing r),
        y ∈ Ioo (((r : ℝ) - 2) / ((r : ℝ) * ((r : ℝ) - 1))) (1 / (r : ℝ)) :=
      isOpen_Ioo.mem_nhds ⟨RCrossing_gt_left_endpoint hr, RCrossing_lt_right_endpoint hr⟩
    exact hnear.mono (fun y hy => R_le_Phi hr ⟨hy.1.le, hy.2.le⟩)
  exact ⟨hasLocalTwoBranchMajorant_of_eventually_branches hbranches hF hG,
    twoBranch_slopes_ordered hbranches hlower hF hG⟩

theorem A_interior_local_majorant {r : ℕ} (hr : 3 ≤ r) {x : ℝ}
    (hx0 : AStart r < x) (hx1 : x < AEnd r) : HasLocalQuadraticMajorant r x (4 * x) 4 := by
  apply A_local_majorant
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ Ioo (AStart r) (AEnd r) :=
    isOpen_Ioo.mem_nhds ⟨hx0, hx1⟩
  exact hnear.mono (fun y hy => Phi_eq_A_on_middle_interval hr hy.1.le hy.2.le)

theorem R_interior_local_majorant {r : ℕ} (hr : 3 ≤ r) {x : ℝ}
    (hx0 : RCrossing r < x) (hx1 : x < 1 / (r : ℝ)) :
    HasLocalQuadraticMajorant r x
      ((r : ℝ) * (1 - ((r : ℝ) - 1) * (1 - r * x)))
      ((r : ℝ)^2 * ((r : ℝ) - 1)) := by
  apply R_local_majorant
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ Ioo (RCrossing r) (1 / (r : ℝ)) :=
    isOpen_Ioo.mem_nhds ⟨hx0, hx1⟩
  exact hnear.mono (fun y hy => Phi_eq_R_after_crossing hr hy.1.le hy.2.le)

end DensityHS.Graphon
