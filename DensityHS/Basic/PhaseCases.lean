module

public import DensityHS.Basic.PhaseActive
public import DensityHS.Basic.LocalBranches

/-!
# Exhaustive phase cases for the full equality classification

Author and maintainer: Xizhi Liu.

Every parameter in the closed admissible interval belongs to one of the
nine cases below. The ordinary crossing case records both actual active
branches, their adjacency, and the exact crossing parameter.
-/

@[expose] public section

namespace DensityHS

inductive ActivePhase (r : ℕ) (x : ℝ) : Prop
  | zero (parameter : x = 0)
  | full (parameter : x = 1 / (r : ℝ))
  | ordinary (i : ℕ) (unique : UniqueBActive r i x)
  | exceptional (left : AStart r < x) (right : x < AEnd r)
  | final (left : RCrossing r < x) (right : x < 1 / (r : ℝ))
  | first (parameter : x = AStart r)
  | tangent (parameter : x = AEnd r)
  | ordinaryCross (i : ℕ) (index_lower : 2 ≤ i) (index_upper : i + 1 < r)
      (parameter : x = BCrossing r i (i + 1))
      (left_active : B r i x = Phi r x) (right_active : B r (i + 1) x = Phi r x)
  | terminalCross (parameter : x = RCrossing r)

theorem active_phase_cases {r : ℕ} (hr : 3 ≤ r) {x : ℝ}
    (hx : x ∈ Set.Icc 0 (1 / (r : ℝ))) : ActivePhase r x := by
  classical
  by_cases hzero : x = 0
  · exact .zero hzero
  by_cases hfull : x = 1 / (r : ℝ)
  · exact .full hfull
  by_cases hA : ADomain r x ∧ A r x = Phi r x
  · rcases (A_active_iff hr hx).mp hA with hzero' | ⟨hxl, hxu⟩
    · exact False.elim (hzero hzero')
    by_cases hfirst : x = AStart r
    · exact .first hfirst
    by_cases htangent : x = AEnd r
    · exact .tangent htangent
    exact .exceptional (lt_of_le_of_ne hxl (Ne.symm hfirst)) (lt_of_le_of_ne hxu htangent)
  by_cases hR : RDomain r x ∧ R r x = Phi r x
  · have hxl := (R_active_iff hr hx).mp hR
    by_cases hterminal : x = RCrossing r
    · exact .terminalCross hterminal
    exact .final (lt_of_le_of_ne hxl (Ne.symm hterminal)) (lt_of_le_of_ne hx.2 hfull)
  have hB : ∃ i : ℕ, 1 ≤ i ∧ i < r ∧ Phi r x = B r i x := by
    rcases Phi_mem_branchValues hr x with ⟨i, hi, hir, heq⟩ | ⟨hd, heq⟩ | ⟨hd, heq⟩
    · exact ⟨i, hi, hir, heq⟩
    · exact False.elim (hA ⟨hd, heq.symm⟩)
    · exact False.elim (hR ⟨hd, heq.symm⟩)
  obtain ⟨i, hi, hir, hiPhi⟩ := hB
  by_cases huniq : ∀ j, 1 ≤ j → j < r → j ≠ i → B r j x < Phi r x
  · refine .ordinary i {
      index_pos := hi
      index_lt := hir
      active := hiPhi
      B_lt := huniq
      A_lt := ?_
      R_lt := ?_
    }
    · intro hd
      exact lt_of_le_of_ne (A_le_Phi hr hd) (fun he => hA ⟨hd, he⟩)
    · intro hd
      exact lt_of_le_of_ne (R_le_Phi hr hd) (fun he => hR ⟨hd, he⟩)
  push_neg at huniq
  obtain ⟨j, hj, hjr, hji, hjge⟩ := huniq
  have hjPhi : B r j x = Phi r x := le_antisymm (B_le_Phi hr hj hjr x) hjge
  rcases lt_or_gt_of_ne hji with hji' | hij
  · obtain ⟨hj2, hij', hcross⟩ :=
      B_B_coactive_only_adjacent hr hj hji' hir hx hjPhi hiPhi.symm
    refine .ordinaryCross j hj2 (by omega) ?_ hjPhi ?_
    · simpa only [hij'] using hcross
    · simpa only [hij'] using hiPhi.symm
  · obtain ⟨hi2, hji', hcross⟩ :=
      B_B_coactive_only_adjacent hr hi hij hjr hx hiPhi.symm hjPhi
    refine .ordinaryCross i hi2 (by omega) ?_ hiPhi.symm ?_
    · simpa only [hji'] using hcross
    · simpa only [hji'] using hjPhi

end DensityHS
