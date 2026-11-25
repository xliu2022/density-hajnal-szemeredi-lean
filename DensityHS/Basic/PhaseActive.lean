module

public import DensityHS.Basic.PhaseR

/-!
# The complete active-branch phase diagram

The restricted maximum is `B₁`, then `A`, then the ordered ordinary envelope,
then `R`. Exact active-branch equivalences below include all transition points
and the common construction at zero.

Author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS

theorem AStart_pos {r : ℕ} (hr : 3 ≤ r) : 0 < AStart r := by
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  exact div_pos (by norm_num) (by linarith)

theorem Phi_eq_B_one_before_A {r : ℕ} (hr : 3 ≤ r) {x : ℝ}
    (hx0 : 0 ≤ x) (hx : x ≤ AStart r) : Phi r x = B r 1 x := by
  have hmax := B_one_dominates_before_A hr hx0 hx
  apply le_antisymm
  · apply Phi_le hr
    · exact hmax
    · intro _
      exact (A_le_B_one_iff hr hx0).mpr hx
    · intro hR
      have hxR : x ≤ RCrossing r := hx.trans
        ((AStart_lt_AEnd hr).le.trans (AEnd_lt_RCrossing hr).le)
      exact ((R_le_B_last_iff hr hR).mpr hxR).trans (hmax _ (by omega) (by omega))
  · exact B_le_Phi hr le_rfl (by omega) x

theorem Phi_eq_A_on_middle_interval {r : ℕ} (hr : 3 ≤ r) {x : ℝ}
    (hxl : AStart r ≤ x) (hxu : x ≤ AEnd r) : Phi r x = A r x := by
  have hx0 : 0 ≤ x := (AStart_pos hr).le.trans hxl
  have hxA : ADomain r x := ⟨hx0, hxu⟩
  have hmax := A_dominates_on_middle_interval hr hxA hxl
  apply le_antisymm
  · apply Phi_le hr
    · exact hmax
    · intro _
      exact le_rfl
    · intro hR
      exact ((R_le_B_last_iff hr hR).mpr (hxu.trans (AEnd_lt_RCrossing hr).le)).trans
        (hmax _ (by omega) (by omega))
  · exact A_le_Phi hr hxA

theorem Phi_eq_BMaximum_on_middle_interval {r : ℕ} (hr : 3 ≤ r) {x : ℝ}
    (hxl : AEnd r ≤ x) (hxu : x ≤ RCrossing r) : Phi r x = BMaximum r x := by
  apply le_antisymm
  · apply Phi_le hr
    · intro i hi hir
      exact B_le_BMaximum (by omega) hi hir x
    · intro hA
      have heq : x = AEnd r := le_antisymm hA.2 hxl
      rw [heq, AEnd_tangent hr]
      exact B_le_BMaximum (by omega) (by omega) (by omega) _
    · intro hR
      exact ((R_le_B_last_iff hr hR).mpr hxu).trans
        (B_le_BMaximum (by omega) (by omega) (by omega) x)
  · exact BMaximum_le_Phi hr x

theorem Phi_eq_R_after_crossing {r : ℕ} (hr : 3 ≤ r) {x : ℝ}
    (hxl : RCrossing r ≤ x) (hxu : x ≤ 1 / (r : ℝ)) : Phi r x = R r x := by
  have hxR := RDomain_of_after_crossing hr hxl hxu
  have hrecip : 1 / ((r : ℝ) + 1) ≤ x := (RCrossing_gt_reciprocal_succ hr).le.trans hxl
  apply le_antisymm
  · apply Phi_le hr
    · intro i _ hir
      exact (B_le_last_on_upper_interval hr hir hrecip hxu).trans
        ((B_last_le_R_iff hr hxR).mpr hxl)
    · intro hA
      exact False.elim ((not_le_of_gt (AEnd_lt_RCrossing hr)) (hxl.trans hA.2))
    · intro _
      exact le_rfl
  · exact R_le_Phi hr hxR

/-- An explicit four-stage formula; the middle ordinary stage has the exact
adjacent-crossing characterization in `B_dominates_iff_crossing_interval`. -/
noncomputable def phaseFormula (r : ℕ) (x : ℝ) : ℝ :=
  if x ≤ AStart r then B r 1 x else
    if x ≤ AEnd r then A r x else
      if x ≤ RCrossing r then BMaximum r x else R r x

theorem Phi_eq_phaseFormula {r : ℕ} (hr : 3 ≤ r) {x : ℝ}
    (hx : x ∈ Set.Icc 0 (1 / (r : ℝ))) : Phi r x = phaseFormula r x := by
  unfold phaseFormula
  split_ifs with hA1 hA2 hR
  · exact Phi_eq_B_one_before_A hr hx.1 hA1
  · exact Phi_eq_A_on_middle_interval hr (le_of_not_ge hA1) hA2
  · exact Phi_eq_BMaximum_on_middle_interval hr (le_of_not_ge hA2) hR
  · exact Phi_eq_R_after_crossing hr (le_of_not_ge hR) hx.2

theorem A_strictly_dominates_interior {r : ℕ} (hr : 3 ≤ r) {x : ℝ}
    (hxl : AStart r < x) (hxu : x < AEnd r) :
    ∀ j, 1 ≤ j → j < r → B r j x < A r x := by
  have hx0 : 0 ≤ x := (AStart_pos hr).le.trans hxl.le
  have hxA : ADomain r x := ⟨hx0, hxu.le⟩
  intro j hj hjr
  by_cases hj1 : j = 1
  · subst j
    have hle := (B_one_le_A_iff hr hx0).mpr (Or.inr hxl.le)
    apply lt_of_le_of_ne hle
    intro heq
    rcases (A_eq_B_one_iff hr x).mp heq.symm with h | h
    · have hp := AStart_pos hr
      linarith
    · exact hxl.ne' h
  · have hlt : B r 2 x < A r x := by
      apply lt_of_le_of_ne (B_two_le_A hr x)
      intro heq
      exact hxu.ne ((A_eq_B_two_iff hr x).mp heq.symm)
    exact (B_le_B_two_on_ADomain hr (by omega) hjr hxA).trans_lt hlt

/-- Exact activity criterion for `A`, including its common zero construction. -/
theorem A_active_iff {r : ℕ} (hr : 3 ≤ r) {x : ℝ}
    (hx : x ∈ Set.Icc 0 (1 / (r : ℝ))) :
    (ADomain r x ∧ A r x = Phi r x) ↔
      x = 0 ∨ (AStart r ≤ x ∧ x ≤ AEnd r) := by
  constructor
  · rintro ⟨hA, heq⟩
    have hBA : B r 1 x ≤ A r x := heq ▸ B_le_Phi hr le_rfl (by omega) x
    rcases (B_one_le_A_iff hr hx.1).mp hBA with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hA.2⟩
  · rintro (rfl | ⟨hxl, hxu⟩)
    · refine ⟨⟨le_rfl, A_endpoint_nonneg (by omega)⟩, ?_⟩
      rw [Phi_eq_B_one_before_A hr le_rfl (AStart_pos hr).le]
      exact (A_eq_B_one_iff hr 0).mpr (Or.inl rfl)
    · exact ⟨⟨hx.1, hxu⟩, (Phi_eq_A_on_middle_interval hr hxl hxu).symm⟩

/-- Exact activity criterion for `R` on the full admissible interval. -/
theorem R_active_iff {r : ℕ} (hr : 3 ≤ r) {x : ℝ}
    (hx : x ∈ Set.Icc 0 (1 / (r : ℝ))) :
    (RDomain r x ∧ R r x = Phi r x) ↔ RCrossing r ≤ x := by
  constructor
  · rintro ⟨hR, heq⟩
    apply (B_last_le_R_iff hr hR).mp
    rw [heq]
    exact B_le_Phi hr (by omega) (by omega) x
  · intro h
    exact ⟨RDomain_of_after_crossing hr h hx.2, (Phi_eq_R_after_crossing hr h hx.2).symm⟩

/-- Ordinary activity is precisely ordinary maximality, outside the strict
`A` interval and before the terminal crossing. -/
theorem B_active_iff {r i : ℕ} (hr : 3 ≤ r) (hi : 1 ≤ i) (hir : i < r) {x : ℝ}
    (hx : x ∈ Set.Icc 0 (1 / (r : ℝ))) :
    B r i x = Phi r x ↔
      (∀ j, 1 ≤ j → j < r → B r j x ≤ B r i x) ∧
      (x ≤ AStart r ∨ AEnd r ≤ x) ∧ x ≤ RCrossing r := by
  constructor
  · intro heq
    refine ⟨?_, ?_, ?_⟩
    · intro j hj hjr
      rw [heq]
      exact B_le_Phi hr hj hjr x
    · by_contra h
      push_neg at h
      have hlt := A_strictly_dominates_interior hr h.1 h.2 i hi hir
      have hAle := A_le_Phi hr (show ADomain r x from ⟨hx.1, h.2.le⟩)
      rw [← heq] at hAle
      exact not_lt_of_ge hAle hlt
    · by_contra h
      have hxc : RCrossing r < x := lt_of_not_ge h
      have hR := RDomain_of_after_crossing hr hxc.le hx.2
      have hRgt := (B_last_lt_R_iff hr hR).mpr hxc
      have hBi := B_le_last_on_upper_interval hr hir
        ((RCrossing_gt_reciprocal_succ hr).le.trans hxc.le) hx.2
      have hRle := R_le_Phi hr hR
      rw [← heq] at hRle
      exact not_lt_of_ge (hRle.trans hBi) hRgt
  · rintro ⟨hmax, hA, hR⟩
    apply le_antisymm (B_le_Phi hr hi hir x)
    apply Phi_le hr
    · exact hmax
    · intro hAx
      rcases hA with hA | hA
      · exact ((A_le_B_one_iff hr hx.1).mpr hA).trans (hmax 1 le_rfl (by omega))
      · have heq : x = AEnd r := le_antisymm hAx.2 hA
        rw [heq, AEnd_tangent hr]
        simpa only [heq] using hmax 2 (by omega) (by omega)
    · intro hRx
      exact ((R_le_B_last_iff hr hRx).mpr hR).trans (hmax _ (by omega) (by omega))

/-- Full ordinary activity, stated using just the explicit adjacent crossing
parameters and the two exceptional intervals. -/
theorem B_active_iff_intervals {r i : ℕ} (hr : 3 ≤ r) (hi : 1 ≤ i) (hir : i < r)
    {x : ℝ} (hx : x ∈ Set.Icc 0 (1 / (r : ℝ))) :
    B r i x = Phi r x ↔
      ((1 < i → BCrossing r (i - 1) i ≤ x) ∧
        (i + 1 < r → x ≤ BCrossing r i (i + 1))) ∧
      (x ≤ AStart r ∨ AEnd r ≤ x) ∧ x ≤ RCrossing r := by
  rw [B_active_iff hr hi hir hx, B_dominates_iff_crossing_interval hi hir hx.1 hx.2]

/-- The only intersections between active `A` and ordinary branches are
the stated first crossing, the tangent endpoint, and the common point zero. -/
theorem A_B_coactive_iff {r i : ℕ} (hr : 3 ≤ r) (hi : 1 ≤ i) (hir : i < r)
    {x : ℝ} (hx : x ∈ Set.Icc 0 (1 / (r : ℝ))) :
    (ADomain r x ∧ A r x = Phi r x ∧ B r i x = Phi r x) ↔
      (i = 1 ∧ (x = 0 ∨ x = AStart r)) ∨ (i = 2 ∧ x = AEnd r) := by
  constructor
  · rintro ⟨hA, hAPhi, hBPhi⟩
    have heq : A r x = B r i x := hAPhi.trans hBPhi.symm
    by_cases hi1 : i = 1
    · exact Or.inl ⟨hi1, (A_eq_B_one_iff hr x).mp (by simpa [hi1] using heq)⟩
    by_cases hi2 : i = 2
    · exact Or.inr ⟨hi2, (A_eq_B_two_iff hr x).mp (by simpa [hi2] using heq)⟩
    have hlt := (B_lt_B_two_on_ADomain hr (by omega : 2 < i) hir hA).trans_le (B_two_le_A hr x)
    exact False.elim (hlt.ne heq.symm)
  · rintro (⟨rfl, hx'⟩ | ⟨rfl, hx'⟩)
    · have hactivity : ADomain r x ∧ A r x = Phi r x := by
        apply (A_active_iff hr hx).mpr
        rcases hx' with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h.ge, h.le.trans (AStart_lt_AEnd hr).le⟩
      refine ⟨hactivity.1, hactivity.2, ?_⟩
      exact ((A_eq_B_one_iff hr x).mpr hx').symm.trans hactivity.2
    · have hactivity : ADomain r x ∧ A r x = Phi r x :=
        (A_active_iff hr hx).mpr (Or.inr ⟨(AStart_lt_AEnd hr).le.trans hx'.ge, hx'.le⟩)
      exact ⟨hactivity.1, hactivity.2, ((A_eq_B_two_iff hr x).mpr hx').symm.trans hactivity.2⟩

/-- The two exceptional constructions are never simultaneously active. -/
theorem A_R_not_coactive {r : ℕ} (hr : 3 ≤ r) {x : ℝ}
    (hx : x ∈ Set.Icc 0 (1 / (r : ℝ))) :
    ¬ (ADomain r x ∧ A r x = Phi r x ∧ RDomain r x ∧ R r x = Phi r x) := by
  rintro ⟨hA, _hAPhi, hR, hRPhi⟩
  have hcross := (R_active_iff hr hx).mp ⟨hR, hRPhi⟩
  exact (AEnd_lt_RCrossing hr).not_ge (hcross.trans hA.2)

/-- Every simultaneous pair of active ordinary branches is a consecutive
pair starting at index at least two, at its unique stated crossing. -/
theorem B_B_coactive_only_adjacent {r i j : ℕ} (hr : 3 ≤ r)
    (hi : 1 ≤ i) (hij : i < j) (hjr : j < r) {x : ℝ}
    (hx : x ∈ Set.Icc 0 (1 / (r : ℝ)))
    (hiPhi : B r i x = Phi r x) (hjPhi : B r j x = Phi r x) :
    2 ≤ i ∧ j = i + 1 ∧ x = BCrossing r i j := by
  have hmax := ((B_active_iff hr hi (hij.trans hjr) hx).mp hiPhi).1
  have heq : B r i x = B r j x := hiPhi.trans hjPhi.symm
  have hadj := ordinary_active_indices_adjacent hi hij hjr hx.1 hx.2 hmax heq
  have hcross := (B_eq_B_iff_crossing hij hjr hx.1 hx.2).mp heq
  refine ⟨?_, hadj, hcross⟩
  by_contra h
  have hi1 : i = 1 := by omega
  have hj2 : j = 2 := by omega
  have hbetween := first_BCrossing_between_A_endpoints hr
  rw [hi1, hj2] at hcross
  have hlt := A_strictly_dominates_interior hr (hcross ▸ hbetween.1) (hcross ▸ hbetween.2)
    i hi (hij.trans hjr)
  have hAle := A_le_Phi hr (show ADomain r x from ⟨hx.1, (hcross ▸ hbetween.2).le⟩)
  rw [← hiPhi] at hAle
  exact not_lt_of_ge hAle hlt

theorem B_lt_last_after_reciprocal_succ {r i : ℕ} (hr : 3 ≤ r) (hi : i < r - 1)
    {x : ℝ} (hxl : 1 / ((r : ℝ) + 1) < x) (hxu : x ≤ 1 / (r : ℝ)) :
    B r i x < B r (r - 1) x := by
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hx0 : 0 < x := (by positivity : 0 < 1 / ((r : ℝ) + 1)).trans hxl
  have hl := (div_lt_iff₀ (by linarith : 0 < (r : ℝ) + 1)).mp hxl
  have hu := (le_div_iff₀ hr0).mp hxu
  have hell : 0 ≤ 1 - (r : ℝ) * x := by nlinarith
  have hlt : 1 - (r : ℝ) * x < x := by nlinarith
  have hiR : (i : ℝ) + 1 < r := by exact_mod_cast (by omega : i + 1 < r)
  have hprod := mul_nonneg (by linarith : 0 ≤ (r : ℝ) - i - 1) (sq_nonneg x)
  apply (B_lt_B_iff_square hi (by omega) x).mpr
  rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
  nlinarith

/-- The only simultaneous terminal/ordinary activity is the last ordinary
branch, at the smaller root specified in the paper. -/
theorem R_B_coactive_iff {r i : ℕ} (hr : 3 ≤ r) (hi : 1 ≤ i) (hir : i < r)
    {x : ℝ} (hx : x ∈ Set.Icc 0 (1 / (r : ℝ))) :
    (RDomain r x ∧ R r x = Phi r x ∧ B r i x = Phi r x) ↔
      i = r - 1 ∧ x = RCrossing r := by
  constructor
  · rintro ⟨hR, hRPhi, hBPhi⟩
    have hxl := (R_active_iff hr hx).mp ⟨hR, hRPhi⟩
    have hxu := ((B_active_iff hr hi hir hx).mp hBPhi).2.2
    have heq : x = RCrossing r := le_antisymm hxu hxl
    refine ⟨?_, heq⟩
    by_contra hn
    have hilast : i < r - 1 := by omega
    have hlt := B_lt_last_after_reciprocal_succ hr hilast
      ((RCrossing_gt_reciprocal_succ hr).trans_le hxl) hx.2
    have hlast := B_le_Phi hr (by omega : 1 ≤ r - 1) (by omega : r - 1 < r) x
    rw [← hBPhi] at hlast
    exact not_lt_of_ge hlast hlt
  · rintro ⟨rfl, heq⟩
    have hR := RDomain_of_after_crossing hr heq.ge hx.2
    have hPhi := Phi_eq_R_after_crossing hr heq.ge hx.2
    have hBR := (R_eq_B_last_iff hr hR).mpr heq
    exact ⟨hR, hPhi.symm, hBR.symm.trans hPhi.symm⟩

/-- Past the last adjacent crossing and the `A` domain, only the last ordinary
branch and `R` remain. Both retain their original restricted domains. -/
theorem Phi_eq_max_last_R {r : ℕ} (hr : 3 ≤ r) {x : ℝ}
    (hx : x ∈ Set.Icc 0 (1 / (r : ℝ))) (hA : AEnd r < x)
    (hB : BCrossing r (r - 2) (r - 1) ≤ x) (hR : RDomain r x) :
    Phi r x = max (B r (r - 1) x) (R r x) := by
  have hmax : ∀ j, 1 ≤ j → j < r → B r j x ≤ B r (r - 1) x := by
    apply (B_dominates_iff_crossing_interval (by omega : 1 ≤ r - 1) (by omega) hx.1 hx.2).mpr
    refine ⟨?_, by omega⟩
    intro _
    simpa only [Nat.sub_sub, show (1 : ℕ) + 1 = 2 by norm_num] using hB
  apply le_antisymm
  · apply Phi_le hr
    · intro j hj hjr
      exact (hmax j hj hjr).trans (le_max_left _ _)
    · intro hAx
      exact False.elim (hA.not_ge hAx.2)
    · intro _
      exact le_max_right _ _
  · exact max_le (B_le_Phi hr (by omega) (by omega) x) (R_le_Phi hr hR)

end DensityHS
