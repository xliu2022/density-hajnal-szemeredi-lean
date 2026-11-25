module

public import DensityHS.Basic.EnvelopeStrict

/-!
# Local polynomial identity at a unique ordinary branch

Author and maintainer: Xizhi Liu.

The admissible domains of the exceptional branches are closed. Consequently
strict uniqueness among the admitted branches gives an actual neighborhood
on which the envelope equals the ordinary quadratic.
-/

@[expose] public section

namespace DensityHS

open Set Filter
open scoped Topology

/-- The ordinary branch is the unique admissible active construction. -/
structure UniqueBActive (r i : ℕ) (x : ℝ) : Prop where
  index_pos : 1 ≤ i
  index_lt : i < r
  active : Phi r x = B r i x
  B_lt : ∀ j, 1 ≤ j → j < r → j ≠ i → B r j x < Phi r x
  A_lt : ADomain r x → A r x < Phi r x
  R_lt : RDomain r x → R r x < Phi r x

theorem UniqueBActive.eventually_eq {r i : ℕ} (hr : 3 ≤ r) {x : ℝ}
    (h : UniqueBActive r i x) : Phi r =ᶠ[𝓝 x] B r i := by
  have hB : ∀ᶠ y in 𝓝 x, ∀ j : Fin r, 1 ≤ j.val → B r j y ≤ B r i y := by
    apply Filter.eventually_all.mpr
    intro j
    by_cases hj : 1 ≤ j.val
    · by_cases hji : j.val = i
      · exact Eventually.of_forall fun _ _ => by rw [hji]
      · have he := (continuous_B r j).continuousAt.eventually_lt (continuous_B r i).continuousAt
          (by simpa only [h.active] using h.B_lt j hj j.isLt hji)
        exact he.mono fun _ hy _ => hy.le
    · exact Eventually.of_forall fun _ hy => False.elim (hj hy)
  have hA : ∀ᶠ y in 𝓝 x, ADomain r y → A r y ≤ B r i y := by
    by_cases hxA : ADomain r x
    · have he := (continuous_A r).continuousAt.eventually_lt (continuous_B r i).continuousAt
        (by simpa only [h.active] using h.A_lt hxA)
      exact he.mono fun _ hy _ => hy.le
    · have hopen : IsOpen {y : ℝ | ¬ADomain r y} :=
        isClosed_Icc.isOpen_compl
      have he : ∀ᶠ y in 𝓝 x, ¬ADomain r y := hopen.mem_nhds hxA
      exact he.mono fun _ hy hdom => False.elim (hy hdom)
  have hR : ∀ᶠ y in 𝓝 x, RDomain r y → R r y ≤ B r i y := by
    by_cases hxR : RDomain r x
    · have he := (continuous_R r).continuousAt.eventually_lt (continuous_B r i).continuousAt
        (by simpa only [h.active] using h.R_lt hxR)
      exact he.mono fun _ hy _ => hy.le
    · have hopen : IsOpen {y : ℝ | ¬RDomain r y} :=
        isClosed_Icc.isOpen_compl
      have he : ∀ᶠ y in 𝓝 x, ¬RDomain r y := hopen.mem_nhds hxR
      exact he.mono fun _ hy hdom => False.elim (hy hdom)
  filter_upwards [hB, hA, hR] with y hyB hyA hyR
  exact le_antisymm (Phi_le hr (fun j hj hjr => hyB ⟨j, hjr⟩ hj) hyA hyR)
    (B_le_Phi hr h.index_pos h.index_lt y)

/-- A unique ordinary phase cannot occur at either global endpoint. -/
theorem UniqueBActive.interior {r i : ℕ} (hr : 3 ≤ r) {x : ℝ}
    (h : UniqueBActive r i x) (hx : x ∈ Icc 0 (1 / (r : ℝ))) :
    0 < x ∧ x < 1 / (r : ℝ) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hxne : x ≠ 0 := by
    intro hz
    subst x
    have hr3 : (3 : ℝ) ≤ r := by exact_mod_cast hr
    have hA : ADomain r 0 := ⟨le_rfl, div_nonneg (by norm_num) (by nlinarith)⟩
    have hs := h.A_lt hA
    rw [Phi_zero (by omega)] at hs
    simp only [A, zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero] at hs
    exact (lt_irrefl _) hs
  have hxend : x ≠ 1 / (r : ℝ) := by
    intro hz
    have hiR : (i : ℝ) < r := by exact_mod_cast h.index_lt
    have hd : 0 < (r : ℝ) - i := sub_pos.mpr hiR
    have ha : 0 < 1 - (i : ℝ) * (1 / (r : ℝ)) := by
      have hiMul : (i : ℝ) * (1 / (r : ℝ)) < 1 := by
        simpa only [div_eq_mul_inv, one_mul] using (div_lt_one hrR).mpr hiR
      linarith
    have hpos := div_pos (sq_pos_of_pos ha) hd
    have he := h.active
    rw [hz, Phi_right_endpoint (by omega)] at he
    unfold B at he
    linarith
  exact ⟨lt_of_le_of_ne hx.1 (Ne.symm hxne), lt_of_le_of_ne hx.2 hxend⟩

end DensityHS
