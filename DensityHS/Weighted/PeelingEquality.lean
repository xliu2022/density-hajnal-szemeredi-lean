module

public import DensityHS.Weighted.TransitionPeelBounds

/-!
# Bellman equality and strict universal peeling at the early transitions

Author and maintainer: Xizhi Liu.

At B1=A for r>=4 and at the active ordinary crossings before the last one,
equality can occur only at one of the two endpoint peel sizes. In particular,
every strict intermediate multiplier gives a strict recursion inequality.
-/

@[expose] public section

namespace DensityHS

theorem peel_length_of_B_optimizer {s i : ℕ} (his : i < s) {x L : ℝ}
    (hq : 1 - L = BPeelOptimizer s i x) :
    L = (1 - (i : ℝ) * x) / ((s : ℝ) + 1 - i) := by
  have h := one_sub_BPeelOptimizer his x
  linarith

theorem peel_length_of_A_optimizer {s : ℕ} (hs : 0 < s) {L : ℝ}
    (hq : 1 - L = ((s : ℝ) - 1) / s) : L = 1 / (s : ℝ) := by
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs)
  have hid : 1 - (((s : ℝ) - 1) / s) = 1 / (s : ℝ) := by field_simp; ring
  linarith

theorem R_three_peel_lt_at_BA_four {q : ℝ} (hq : q ≠ 0) :
    peelValue (R 3) (AStart 4) q < Phi 4 (AStart 4) := by
  rw [Phi_eq_A_on_middle_interval (by norm_num : 3 ≤ 4) le_rfl
    (AStart_lt_AEnd (by norm_num : 3 ≤ 4)).le, R_peel_polynomial 3 hq]
  norm_num [AStart, A]
  nlinarith [sq_nonneg (q - 7 / 13)]

theorem BA_peel_eq_imp_endpoints {r : ℕ} (hr : 4 ≤ r) {L : ℝ}
    (hq : 0 < 1 - L) (hq1 : 1 - L ≤ 1)
    (heq : peelValue (Phi (r - 1)) (AStart r) (1 - L) = Phi r (AStart r)) :
    L = (1 - AStart r) / ((r : ℝ) - 1) ∨ L = 1 / ((r : ℝ) - 1) := by
  have hr3 : 3 ≤ r := by omega
  have hsucc : (r - 1 : ℕ) + 1 = r := by omega
  have hcast : ((r - 1 : ℕ) : ℝ) + 1 = r := by exact_mod_cast hsucc
  have hx0 := AStart_pos hr3
  have hxA := AStart_lt_AEnd hr3
  have hx : AStart r ∈ Set.Icc 0 (1 / (r : ℝ)) :=
    ⟨hx0.le, hxA.le.trans (A_endpoint_le (by omega))⟩
  have hADomain : ADomain r (AStart r) := ⟨hx0.le, hxA.le⟩
  have hPhi : Phi r (AStart r) = A r (AStart r) :=
    Phi_eq_A_on_middle_interval hr3 le_rfl hxA.le
  have hlast : B r (r - 1) (AStart r) < Phi r (AStart r) := by
    apply lt_of_le_of_ne (B_le_Phi hr3 (by omega) (by omega) _)
    intro he
    have h := (A_B_coactive_iff hr3 (by omega : 1 ≤ r - 1) (by omega) hx).mp
      ⟨hADomain, hPhi.symm, he⟩
    rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  have hRstrict : RDomain (r - 1) (AStart r / (1 - L)) →
      peelValue (R (r - 1)) (AStart r) (1 - L) < Phi ((r - 1) + 1) (AStart r) := by
    intro hR
    by_cases hr4 : r = 4
    · subst r
      exact R_three_peel_lt_at_BA_four (ne_of_gt hq)
    · apply R_peel_lt_Phi_of_inactive_last (by omega : 4 ≤ r - 1) hx.1
        (by simpa only [hcast] using hx.2) hq hq1 hR
      simpa only [hsucc] using hlast
  have heq' : peelValue (Phi (r - 1)) (AStart r) (1 - L) =
      Phi ((r - 1) + 1) (AStart r) := by simpa only [hsucc] using heq
  rcases peel_Phi_equality_trace (by omega : 3 ≤ r - 1) hx.1 hq hRstrict heq' with
    ⟨i, hi, his, hactive, hopt⟩ | ⟨_, _, hopt⟩
  · rw [hsucc] at hactive
    have hco := (A_B_coactive_iff hr3 hi (by omega : i < r) hx).mp
      ⟨hADomain, hPhi.symm, hactive⟩
    have hi1 : i = 1 := by
      rcases hco with ⟨hi1, _⟩ | ⟨_, hxend⟩
      · exact hi1
      · exact False.elim (hxA.ne hxend)
    subst i
    have hL := peel_length_of_B_optimizer his hopt
    rw [hcast, Nat.cast_one, one_mul] at hL
    exact Or.inl hL
  · have hL := peel_length_of_A_optimizer (by omega : 0 < r - 1) hopt
    rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one] at hL
    exact Or.inr hL

theorem BA_transition_universal_peel_strict {r : ℕ} (hr : 4 ≤ r) {L : ℝ}
    (hL0 : (1 - AStart r) / ((r : ℝ) - 1) < L)
    (hL1 : L < 1 / ((r : ℝ) - 1)) :
    peelValue (Phi (r - 1)) (AStart r) (1 - L) < Phi r (AStart r) := by
  obtain ⟨hLp, hLt, hLx, _⟩ := BA_transition_peel_bounds hr hL0 hL1
  have hq : 0 < 1 - L := by linarith
  have hq1 : 1 - L ≤ 1 := by linarith
  have hsucc : (r - 1 : ℕ) + 1 = r := by omega
  have hcast : ((r - 1 : ℕ) : ℝ) + 1 = r := by exact_mod_cast hsucc
  have hx1 : AStart r ≤ 1 / ((r - 1 : ℕ) + (1 : ℝ)) := by
    rw [hcast]
    exact (AStart_lt_AEnd (by omega : 3 ≤ r)).le.trans (A_endpoint_le (by omega))
  have hle := peel_Phi_le (by omega : 2 ≤ r - 1) (AStart_pos (by omega : 3 ≤ r)).le
    hx1 hq hq1 (by linarith : ((r - 1 : ℕ) : ℝ) * AStart r ≤ 1 - L)
  rw [hsucc] at hle
  apply lt_of_le_of_ne hle
  intro heq
  rcases BA_peel_eq_imp_endpoints hr hq hq1 heq with h | h
  · exact hL0.ne' h
  · exact hL1.ne h

theorem B_coactive_only_two {r i k : ℕ} (hr : 3 ≤ r) (hi : 1 ≤ i)
    (hir : i + 1 < r) {x : ℝ} (hx : x ∈ Set.Icc 0 (1 / (r : ℝ)))
    (hiPhi : B r i x = Phi r x) (hjPhi : B r (i + 1) x = Phi r x)
    (hk : 1 ≤ k) (hkr : k < r) (hkPhi : B r k x = Phi r x) : k = i ∨ k = i + 1 := by
  by_cases hki : k = i
  · exact Or.inl hki
  rcases lt_or_gt_of_ne hki with hki' | hik
  · have h := B_B_coactive_only_adjacent hr hk (by omega : k < i + 1) hir hx hkPhi hjPhi
    omega
  · have h := B_B_coactive_only_adjacent hr hi hik hkr hx hiPhi hkPhi
    exact Or.inr h.2.1

theorem BB_peel_eq_imp_endpoints {r i : ℕ} (hi : 2 ≤ i) (hir : i ≤ r - 3)
    {x L : ℝ} (hx : x ∈ Set.Icc 0 (1 / (r : ℝ)))
    (hiPhi : B r i x = Phi r x) (hjPhi : B r (i + 1) x = Phi r x)
    (hq : 0 < 1 - L) (hq1 : 1 - L ≤ 1)
    (heq : peelValue (Phi (r - 1)) x (1 - L) = Phi r x) :
    L = (1 - (i : ℝ) * x) / ((r : ℝ) - i) ∨
      L = (1 - ((i + 1 : ℕ) : ℝ) * x) / ((r : ℝ) - (i + 1 : ℕ)) := by
  have hr : 3 ≤ r := by omega
  have hsucc : (r - 1 : ℕ) + 1 = r := by omega
  have hcast : ((r - 1 : ℕ) : ℝ) + 1 = r := by exact_mod_cast hsucc
  have hlast : B r (r - 1) x < Phi r x := by
    apply lt_of_le_of_ne (B_le_Phi hr (by omega) (by omega) x)
    intro he
    have h := B_coactive_only_two hr (by omega : 1 ≤ i) (by omega) hx hiPhi hjPhi
      (by omega : 1 ≤ r - 1) (by omega) he
    rcases h with h | h <;> omega
  have hRstrict : RDomain (r - 1) (x / (1 - L)) →
      peelValue (R (r - 1)) x (1 - L) < Phi ((r - 1) + 1) x := by
    intro hR
    apply R_peel_lt_Phi_of_inactive_last (by omega : 4 ≤ r - 1) hx.1
      (by simpa only [hcast] using hx.2) hq hq1 hR
    simpa only [hsucc] using hlast
  have heq' : peelValue (Phi (r - 1)) x (1 - L) = Phi ((r - 1) + 1) x := by
    simpa only [hsucc] using heq
  rcases peel_Phi_equality_trace (by omega : 3 ≤ r - 1) hx.1 hq hRstrict heq' with
    ⟨k, hk, hks, hactive, hopt⟩ | ⟨hAx, hAPhi, _⟩
  · rw [hsucc] at hactive
    have hk2 := B_coactive_only_two hr (by omega : 1 ≤ i) (by omega) hx hiPhi hjPhi
      hk (by omega) hactive
    have hL := peel_length_of_B_optimizer hks hopt
    rw [hcast] at hL
    rcases hk2 with rfl | rfl
    · exact Or.inl hL
    · exact Or.inr hL
  · rw [hsucc] at hAx hAPhi
    have h := (A_B_coactive_iff hr (by omega : 1 ≤ i + 1) (by omega) hx).mp
      ⟨hAx, hAPhi, hjPhi⟩
    rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> omega

theorem BB_transition_universal_peel_strict {r i : ℕ} (hi : 2 ≤ i) (hir : i ≤ r - 3)
    {x L : ℝ} (hx : x ∈ Set.Icc 0 (1 / (r : ℝ)))
    (hiPhi : B r i x = Phi r x) (hjPhi : B r (i + 1) x = Phi r x)
    (hL0 : (1 - (i : ℝ) * x) / ((r : ℝ) - i) < L)
    (hL1 : L < (1 - ((i + 1 : ℕ) : ℝ) * x) / ((r : ℝ) - (i + 1 : ℕ))) :
    peelValue (Phi (r - 1)) x (1 - L) < Phi r x := by
  have hcross := (B_eq_B_iff_crossing (by omega : i < i + 1) (by omega) hx.1 hx.2).mp
    (hiPhi.trans hjPhi.symm)
  obtain ⟨hLp, hLt, hLx, _⟩ := BB_transition_peel_bounds hi hir hcross hL0 hL1
  have hq : 0 < 1 - L := by linarith
  have hq1 : 1 - L ≤ 1 := by linarith
  have hsucc : (r - 1 : ℕ) + 1 = r := by omega
  have hcast : ((r - 1 : ℕ) : ℝ) + 1 = r := by exact_mod_cast hsucc
  have hle := peel_Phi_le (by omega : 2 ≤ r - 1) hx.1
    (by simpa only [hcast] using hx.2) hq hq1 (by linarith : ((r - 1 : ℕ) : ℝ) * x ≤ 1 - L)
  rw [hsucc] at hle
  apply lt_of_le_of_ne hle
  intro heq
  rcases BB_peel_eq_imp_endpoints hi hir hx hiPhi hjPhi hq hq1 heq with h | h
  · exact hL0.ne' h
  · exact hL1.ne h

end DensityHS
