module

public import DensityHS.Basic.PhaseActive
public import DensityHS.Graphon.BranchVariation
public import DensityHS.Graphon.NonsmoothCoefficients

/-!
# Actual local branches at every phase transition

Author and maintainer: Xizhi Liu.

The statements identify the two polynomials on the two sides of a crossing.
All excluded construction branches are eliminated using the proved complete
phase diagram, including their restricted admissible domains.
-/

@[expose] public section

namespace DensityHS.Graphon

open Set Filter
open scoped Topology

theorem eventually_admitted_le_of_strict {D : ℝ → Prop} (hD : IsClosed {x | D x})
    {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) {x : ℝ}
    (h : D x → f x < g x) : ∀ᶠ y in 𝓝 x, D y → f y ≤ g y := by
  by_cases hx : D x
  · exact (hf.continuousAt.eventually_lt hg.continuousAt (h hx)).mono
      (fun _ hy _ => hy.le)
  · have he : ∀ᶠ y in 𝓝 x, ¬D y := hD.isOpen_compl.mem_nhds hx
    exact he.mono (fun _ hy hd => False.elim (hy hd))

theorem eventually_B_dominated {r i : ℕ} {x : ℝ}
    (hstrict : ∀ j, 1 ≤ j → j < r → j ≠ i → B r j x < B r i x) :
    ∀ᶠ y in 𝓝 x, ∀ j, 1 ≤ j → j < r → B r j y ≤ B r i y := by
  have h : ∀ᶠ y in 𝓝 x, ∀ j : Fin r, 1 ≤ j.val → B r j y ≤ B r i y := by
    apply Filter.eventually_all.mpr
    intro j
    by_cases hj : 1 ≤ j.val
    · by_cases hji : j.val = i
      · exact Eventually.of_forall (fun _ _ => by rw [hji])
      · exact ((continuous_B r j).continuousAt.eventually_lt (continuous_B r i).continuousAt
          (hstrict j hj j.isLt hji)).mono (fun _ hy _ => hy.le)
    · exact Eventually.of_forall (fun _ hy => False.elim (hj hy))
  exact h.mono (fun _ hy j hj hjr => hy ⟨j, hjr⟩ hj)

theorem AStart_eventually_branches {r : ℕ} (hr : 3 ≤ r) :
    ∀ᶠ y in 𝓝 (AStart r),
      (y ≤ AStart r → Phi r y = B r 1 y) ∧
      (AStart r ≤ y → Phi r y = A r y) := by
  have hnear : ∀ᶠ y in 𝓝 (AStart r), y ∈ Ioo 0 (AEnd r) :=
    isOpen_Ioo.mem_nhds ⟨AStart_pos hr, AStart_lt_AEnd hr⟩
  exact hnear.mono (fun y hy => ⟨fun h => Phi_eq_B_one_before_A hr hy.1.le h,
    fun h => Phi_eq_A_on_middle_interval hr h hy.2.le⟩)

theorem AEnd_eventually_branches {r : ℕ} (hr : 3 ≤ r) :
    ∀ᶠ y in 𝓝 (AEnd r),
      (y ≤ AEnd r → Phi r y = A r y) ∧
      (AEnd r ≤ y → Phi r y = B r 2 y) := by
  have hx : AEnd r ∈ Icc 0 (1 / (r : ℝ)) :=
    ⟨A_endpoint_nonneg (by omega), A_endpoint_le (by omega)⟩
  have hPhi : Phi r (AEnd r) = A r (AEnd r) :=
    Phi_eq_A_on_middle_interval hr (AStart_lt_AEnd hr).le le_rfl
  have hB : ∀ j, 1 ≤ j → j < r → j ≠ 2 → B r j (AEnd r) < B r 2 (AEnd r) := by
    intro j hj hjr hj2
    apply lt_of_le_of_ne
    · simpa only [hPhi, AEnd_tangent hr] using B_le_Phi hr hj hjr (AEnd r)
    · intro heq
      have hjPhi : B r j (AEnd r) = Phi r (AEnd r) := by
        rw [hPhi, AEnd_tangent hr]
        exact heq
      have hco := (A_B_coactive_iff hr hj hjr hx).mp
        ⟨⟨hx.1, le_rfl⟩, hPhi.symm, hjPhi⟩
      rcases hco with ⟨_, hz | hz⟩ | ⟨hj', _⟩
      · exact (ne_of_gt ((AStart_pos hr).trans (AStart_lt_AEnd hr))) hz
      · exact (AStart_lt_AEnd hr).ne hz.symm
      · exact hj2 hj'
  have hnear : ∀ᶠ y in 𝓝 (AEnd r), y ∈ Ioo (AStart r) (RCrossing r) :=
    isOpen_Ioo.mem_nhds ⟨AStart_lt_AEnd hr, AEnd_lt_RCrossing hr⟩
  filter_upwards [hnear, eventually_B_dominated hB] with y hy hyB
  refine ⟨fun h => Phi_eq_A_on_middle_interval hr hy.1.le h, ?_⟩
  intro h
  apply le_antisymm _ (B_le_Phi hr (by omega) (by omega) y)
  apply Phi_le hr hyB
  · intro hA
    have heq : y = AEnd r := le_antisymm hA.2 h
    rw [heq, AEnd_tangent hr]
  · intro hR
    exact ((R_le_B_last_iff hr hR).mpr hy.2.le).trans (hyB _ (by omega) (by omega))

theorem ordinary_coactive_eventually_max {r i j : ℕ} (hr : 3 ≤ r)
    (hi : 1 ≤ i) (hij : i < j) (hjr : j < r) {x : ℝ}
    (hx : x ∈ Icc 0 (1 / (r : ℝ)))
    (hiPhi : B r i x = Phi r x) (hjPhi : B r j x = Phi r x) :
    ∀ᶠ y in 𝓝 x, Phi r y = max (B r i y) (B r j y) := by
  obtain ⟨hi2, hji, hcross⟩ := B_B_coactive_only_adjacent hr hi hij hjr hx hiPhi hjPhi
  have hstrict : ∀ k, 1 ≤ k → k < r → k ≠ i → k ≠ j → B r k x < B r i x := by
    intro k hk hkr hki hkj
    apply lt_of_le_of_ne
    · simpa only [hiPhi] using B_le_Phi hr hk hkr x
    · intro heq
      have hkPhi := heq.trans hiPhi
      rcases lt_or_gt_of_ne hki with hki' | hik
      · have h := B_B_coactive_only_adjacent hr hk (hki'.trans hij) hjr hx hkPhi hjPhi
        omega
      · have h := B_B_coactive_only_adjacent hr hi hik hkr hx hiPhi hkPhi
        omega
  have hA : ADomain r x → A r x < B r i x := by
    intro hxA
    apply lt_of_le_of_ne
    · simpa only [hiPhi] using A_le_Phi hr hxA
    · intro heq
      have h := (A_B_coactive_iff hr (by omega : 1 ≤ j) hjr hx).mp
        ⟨hxA, heq.trans hiPhi, hjPhi⟩
      rcases h with ⟨hj1, _⟩ | ⟨hj2, _⟩ <;> omega
  have hR : RDomain r x → R r x < B r i x := by
    intro hxR
    apply lt_of_le_of_ne
    · simpa only [hiPhi] using R_le_Phi hr hxR
    · intro heq
      have h := (R_B_coactive_iff hr hi (hij.trans hjr) hx).mp
        ⟨hxR, heq.trans hiPhi, hiPhi⟩
      omega
  have hB : ∀ᶠ y in 𝓝 x, ∀ k, 1 ≤ k → k < r →
      B r k y ≤ max (B r i y) (B r j y) := by
    have h : ∀ᶠ y in 𝓝 x, ∀ k : Fin r, 1 ≤ k.val →
        B r k y ≤ max (B r i y) (B r j y) := by
      apply Filter.eventually_all.mpr
      intro k
      by_cases hk : 1 ≤ k.val
      · by_cases hki : k.val = i
        · exact Eventually.of_forall (fun y _ => by rw [hki]; exact le_max_left _ _)
        · by_cases hkj : k.val = j
          · exact Eventually.of_forall (fun y _ => by rw [hkj]; exact le_max_right _ _)
          · exact ((continuous_B r k).continuousAt.eventually_lt (continuous_B r i).continuousAt
              (hstrict k hk k.isLt hki hkj)).mono (fun _ hy _ => hy.le.trans (le_max_left _ _))
      · exact Eventually.of_forall (fun _ hy => False.elim (hk hy))
    exact h.mono (fun _ hy k hk hkr => hy ⟨k, hkr⟩ hk)
  have hAn := eventually_admitted_le_of_strict (D := ADomain r) isClosed_Icc
    (continuous_A r) (continuous_B r i) hA
  have hRn := eventually_admitted_le_of_strict (D := RDomain r) isClosed_Icc
    (continuous_R r) (continuous_B r i) hR
  filter_upwards [hB, hAn, hRn] with y hyB hyA hyR
  apply le_antisymm (Phi_le hr hyB (fun hd => (hyA hd).trans (le_max_left _ _))
    (fun hd => (hyR hd).trans (le_max_left _ _)))
  exact max_le (B_le_Phi hr hi (hij.trans hjr) y) (B_le_Phi hr (by omega) hjr y)

theorem ordinary_coactive_eventually_branches {r i j : ℕ} (hr : 3 ≤ r)
    (hi : 1 ≤ i) (hij : i < j) (hjr : j < r) {x : ℝ}
    (hx : x ∈ Icc 0 (1 / (r : ℝ)))
    (hiPhi : B r i x = Phi r x) (hjPhi : B r j x = Phi r x) :
    ∀ᶠ y in 𝓝 x,
      (y ≤ x → Phi r y = B r i y) ∧ (x ≤ y → Phi r y = B r j y) := by
  have hcross := (B_eq_B_iff_crossing hij hjr hx.1 hx.2).mp (hiPhi.trans hjPhi.symm)
  have hxi : x ∈ Ioo 0 (1 / (r : ℝ)) := by
    rw [hcross]
    exact ⟨BCrossing_pos (by omega), BCrossing_lt_right_endpoint (hij.trans hjr) hjr⟩
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ Ioo 0 (1 / (r : ℝ)) := isOpen_Ioo.mem_nhds hxi
  filter_upwards [hnear, ordinary_coactive_eventually_max hr hi hij hjr hx hiPhi hjPhi]
    with y hy heq
  refine ⟨?_, ?_⟩
  · intro hyx
    rw [heq, max_eq_left]
    apply le_of_not_gt
    rw [B_lt_B_iff_crossing hij hjr hy.1.le hy.2.le]
    simpa only [← hcross, not_lt] using hyx
  · intro hxy
    rw [heq, max_eq_right]
    exact (B_le_B_iff_crossing hij hjr hy.1.le hy.2.le).mpr (hcross ▸ hxy)

theorem RCrossing_eventually_branches {r : ℕ} (hr : 3 ≤ r) :
    ∀ᶠ y in 𝓝 (RCrossing r),
      (y ≤ RCrossing r → Phi r y = B r (r - 1) y) ∧
      (RCrossing r ≤ y → Phi r y = R r y) := by
  have hnear : ∀ᶠ y in 𝓝 (RCrossing r),
      y ∈ Ioo (max (AEnd r) (1 / ((r : ℝ) + 1))) (1 / (r : ℝ)) :=
    isOpen_Ioo.mem_nhds ⟨max_lt (AEnd_lt_RCrossing hr) (RCrossing_gt_reciprocal_succ hr),
      RCrossing_lt_right_endpoint hr⟩
  filter_upwards [hnear] with y hy
  have hyA : AEnd r < y := (le_max_left _ _).trans_lt hy.1
  have hyrec : 1 / ((r : ℝ) + 1) < y := (le_max_right _ _).trans_lt hy.1
  refine ⟨?_, fun h => Phi_eq_R_after_crossing hr h hy.2.le⟩
  intro h
  apply le_antisymm _ (B_le_Phi hr (by omega) (by omega) y)
  apply Phi_le hr
  · intro i _ hir
    exact B_le_last_on_upper_interval hr hir hyrec.le hy.2.le
  · intro hA
    exact False.elim (hyA.not_ge hA.2)
  · intro hR
    exact (R_le_B_last_iff hr hR).mpr h

end DensityHS.Graphon
