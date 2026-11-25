module

public import DensityHS.Basic.Envelope

/-!
# Strict increase and endpoint values of the density envelope

Author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS

theorem B_strictMonoOn {r i : ℕ} (hr : 1 ≤ r) (hi : 1 ≤ i) (hir : i < r) :
    StrictMonoOn (B r i) (Set.Icc 0 (1 / (r : ℝ))) := by
  intro x hx y hy hxy
  have hrp : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hip : (0 : ℝ) < i := by exact_mod_cast (by omega : 0 < i)
  have hri : (i : ℝ) < r := by exact_mod_cast hir
  have hry : (r : ℝ) * y ≤ 1 := by
    have := (le_div_iff₀ hrp).mp hy.2
    nlinarith
  have hiy : (i : ℝ) * y ≤ 1 := by nlinarith [hy.1]
  have hixy : (i : ℝ) * x < i * y := mul_lt_mul_of_pos_left hxy hip
  have hsq : (1 - (i : ℝ) * y) ^ 2 < (1 - (i : ℝ) * x) ^ 2 := by
    nlinarith
  have hdiv := div_lt_div_of_pos_right hsq (by linarith : 0 < (r : ℝ) - i)
  unfold B
  linarith

theorem A_strictMonoOn (r : ℕ) : StrictMonoOn (A r) (Set.Ici 0) := by
  intro x hx y hy hxy
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  unfold A
  nlinarith

theorem R_strictMonoOn {r : ℕ} (hr : 2 ≤ r) :
    StrictMonoOn (R r)
      (Set.Ici (((r : ℝ) - 2) / ((r : ℝ) * ((r : ℝ) - 1)))) := by
  intro x hx y hy hxy
  have hr1 : (1 : ℝ) < r := by exact_mod_cast (by omega : 1 < r)
  have hden : 0 < (r : ℝ) * ((r : ℝ) - 1) := mul_pos (by linarith) (by linarith)
  have hxl := (div_le_iff₀ hden).mp hx
  have hdiff := mul_lt_mul_of_pos_left hxy hden
  have hcoef : 0 < (r : ℝ) * ((r : ℝ) - 1) * (x + y) / 2 - ((r : ℝ) - 2) := by
    nlinarith
  have hp := mul_pos (mul_pos (by linarith : (0 : ℝ) < r) (sub_pos.mpr hxy)) hcoef
  unfold R
  nlinarith

theorem Phi2_strictMonoOn : StrictMonoOn Phi2 (Set.Icc 0 (1 / 2)) := by
  intro x hx y hy hxy
  have ha : x - x ^ 2 / 2 < y - y ^ 2 / 2 := by nlinarith [hx.1, hy.2]
  have hb : 2 * x ^ 2 < 2 * y ^ 2 := by nlinarith [hx.1]
  unfold Phi2
  by_cases h : x - x ^ 2 / 2 ≤ 2 * x ^ 2
  · rw [max_eq_right h]
    exact hb.trans_le (le_max_right _ _)
  · rw [max_eq_left (le_of_not_ge h)]
    exact ha.trans_le (le_max_left _ _)

theorem Phi_strictMonoOn {r : ℕ} (hr : 2 ≤ r) :
    StrictMonoOn (Phi r) (Set.Icc 0 (1 / (r : ℝ))) := by
  by_cases hr2 : r = 2
  · subst r
    simpa only [StrictMonoOn, Phi_two, Nat.cast_ofNat] using Phi2_strictMonoOn
  have hr3 : 3 ≤ r := by omega
  intro x hx y hy hxy
  have hmem := Phi_mem_branchValues hr3 x
  rcases hmem with ⟨i, hi, hir, heq⟩ | ⟨hax, heq⟩ | ⟨hrx, heq⟩
  · rw [heq]
    exact (B_strictMonoOn (by omega) hi hir hx hy hxy).trans_le (B_le_Phi hr3 hi hir y)
  · rw [heq]
    by_cases hay : y ≤ 1 / (2 * ((r : ℝ) - 1))
    · exact (A_strictMonoOn r hx.1 hy.1 hxy).trans_le (A_le_Phi hr3 ⟨hy.1, hay⟩)
    · calc
        A r x ≤ A r (1 / (2 * ((r : ℝ) - 1))) :=
          A_monotoneOn r hx.1 (A_endpoint_nonneg hr) hax.2
        _ = B r 2 (1 / (2 * ((r : ℝ) - 1))) := A_tangent_eq_B_two hr3
        _ < B r 2 y := B_strictMonoOn (by omega) (by omega) (by omega)
          ⟨A_endpoint_nonneg hr, A_endpoint_le hr⟩ hy (lt_of_not_ge hay)
        _ ≤ Phi r y := B_le_Phi hr3 (by omega) (by omega) y
  · rw [heq]
    exact (R_strictMonoOn hr hrx.1 (hrx.1.trans (le_of_lt hxy)) hxy).trans_le
      (R_le_Phi hr3 ⟨hrx.1.trans (le_of_lt hxy), hy.2⟩)

theorem Phi_right_endpoint {r : ℕ} (hr : 2 ≤ r) : Phi r (1 / (r : ℝ)) = 1 / 2 := by
  by_cases hr2 : r = 2
  · subst r
    norm_num [Phi_two, Phi2]
  have hr3 : 3 ≤ r := by omega
  apply le_antisymm (Phi_le_half hr3 _)
  rw [← R_right_endpoint (by omega : 1 ≤ r)]
  apply R_le_Phi hr3
  constructor
  · have hr1 : (1 : ℝ) < r := by exact_mod_cast (by omega : 1 < r)
    apply (div_le_iff₀ (mul_pos (by linarith : (0 : ℝ) < r) (by linarith))).mpr
    have hr0 : (r : ℝ) ≠ 0 := by linarith
    field_simp
    nlinarith
  · exact le_rfl

theorem Phi_lt_half {r : ℕ} (hr : 2 ≤ r) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 1 / (r : ℝ)) : Phi r x < 1 / 2 := by
  rw [← Phi_right_endpoint hr]
  exact Phi_strictMonoOn hr ⟨hx0, le_of_lt hx1⟩
    ⟨le_trans hx0 (le_of_lt hx1), le_rfl⟩ hx1

theorem Phi_zero {r : ℕ} (hr : 2 ≤ r) :
    Phi r 0 = ((r : ℝ) - 2) / (2 * ((r : ℝ) - 1)) := by
  by_cases hr2 : r = 2
  · subst r
    norm_num [Phi_two, Phi2]
  have hr3 : 3 ≤ r := by omega
  have hr2R : (2 : ℝ) < r := by exact_mod_cast hr3
  have hB : B r 1 0 = ((r : ℝ) - 2) / (2 * ((r : ℝ) - 1)) := by
    unfold B
    norm_num only [Nat.cast_one, mul_zero, sub_zero, one_pow]
    have hden : (r : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    <;> ring
  apply le_antisymm
  · apply Phi_le hr3
    · intro i hi hir
      have hiR : (1 : ℝ) ≤ i := by exact_mod_cast hi
      have hirR : (i : ℝ) < r := by exact_mod_cast hir
      have hinv := one_div_le_one_div_of_le (by linarith : 0 < (r : ℝ) - i)
        (show (r : ℝ) - i ≤ (r : ℝ) - 1 by linarith)
      rw [← hB]
      unfold B
      norm_num only [mul_zero, sub_zero, one_pow, Nat.cast_one]
      linarith
    · intro _
      unfold A
      norm_num
    · intro hR
      have hleft : 0 < ((r : ℝ) - 2) / ((r : ℝ) * ((r : ℝ) - 1)) :=
        div_pos (by linarith) (mul_pos (by linarith) (by linarith))
      exact False.elim ((not_le_of_gt hleft) hR.1)
  · rw [← hB]
    exact B_le_Phi hr3 le_rfl (by omega) 0

theorem continuousOn_Phi_of_two_le {r : ℕ} (hr : 2 ≤ r) :
    ContinuousOn (Phi r) (Set.Icc 0 (1 / (r : ℝ))) := by
  by_cases hr2 : r = 2
  · subst r
    have heq : Phi 2 = Phi2 := funext Phi_two
    rw [heq]
    exact continuous_Phi2.continuousOn
  · exact continuousOn_Phi (by omega)

/-- The envelope parametrizes the entire admissible density interval. -/
theorem Phi_image_interval {r : ℕ} (hr : 2 ≤ r) :
    Phi r '' Set.Icc 0 (1 / (r : ℝ)) =
      Set.Icc (((r : ℝ) - 2) / (2 * ((r : ℝ) - 1))) (1 / 2) := by
  have h := (continuousOn_Phi_of_two_le hr).image_Icc_of_monotoneOn
    (show (0 : ℝ) ≤ 1 / (r : ℝ) by positivity) (Phi_strictMonoOn hr).monotoneOn
  simpa only [Phi_zero hr, Phi_right_endpoint hr] using h

/-- Each admissible edge density determines one and only one cover parameter. -/
theorem existsUnique_Phi_parameter {r : ℕ} (hr : 2 ≤ r) {e : ℝ}
    (he : e ∈ Set.Icc (((r : ℝ) - 2) / (2 * ((r : ℝ) - 1))) (1 / 2)) :
    ∃! x : ℝ, x ∈ Set.Icc 0 (1 / (r : ℝ)) ∧ Phi r x = e := by
  rw [← Phi_image_interval hr] at he
  obtain ⟨x, hx, hxe⟩ := he
  refine ⟨x, ⟨hx, hxe⟩, ?_⟩
  intro y hy
  exact (Phi_strictMonoOn hr).injOn hy.1 hx (hy.2.trans hxe.symm)

end DensityHS
