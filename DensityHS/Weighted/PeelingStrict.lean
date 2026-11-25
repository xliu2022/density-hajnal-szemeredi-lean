module

public import DensityHS.Weighted.Peeling
public import DensityHS.Basic.PhaseActive

/-!
# Strict branches and an equality trace for universal peeling

Author and maintainer: Xizhi Liu.

The terminal lower branch is strictly dominated when the upper last ordinary
branch is inactive. Beyond the upper A-domain, the constrained lower A branch
is strictly below B2. These facts make the completed-square equality trace
valid at the early phase transitions.
-/

@[expose] public section

namespace DensityHS

theorem R_left_lt_B_last {s : ℕ} (hs : 3 ≤ s) :
    R s (((s : ℝ) - 2) / ((s : ℝ) * ((s : ℝ) - 1))) <
      B s (s - 1) (((s : ℝ) - 2) / ((s : ℝ) * ((s : ℝ) - 1))) := by
  have hsR : (3 : ℝ) ≤ s := by exact_mod_cast hs
  have hs0 : (s : ℝ) ≠ 0 := by linarith
  have hs1 : (s : ℝ) - 1 ≠ 0 := by linarith
  have hgap :
      B s (s - 1) (((s : ℝ) - 2) / ((s : ℝ) * ((s : ℝ) - 1))) -
        R s (((s : ℝ) - 2) / ((s : ℝ) * ((s : ℝ) - 1))) =
          ((s : ℝ) - 2)^2 / (2 * ((s : ℝ) - 1) * (s : ℝ)^2) := by
    unfold B R
    rw [Nat.cast_sub (by omega : 1 ≤ s), Nat.cast_one]
    have hden : (s : ℝ) - ((s : ℝ) - 1) = 1 := by ring
    rw [hden]
    field_simp
    <;> ring
  have hp : 0 < ((s : ℝ) - 2)^2 / (2 * ((s : ℝ) - 1) * (s : ℝ)^2) :=
    div_pos (sq_pos_of_pos (by linarith))
      (mul_pos (by linarith) (sq_pos_of_pos (by linarith)))
  linarith

theorem R_peel_lt_Phi_of_inactive_last {s : ℕ} (hs : 4 ≤ s) {x q : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / ((s : ℝ) + 1))
    (hq : 0 < q) (hq1 : q ≤ 1) (hR : RDomain s (x / q))
    (hlast : B (s + 1) s x < Phi (s + 1) x) :
    peelValue (R s) x q < Phi (s + 1) x := by
  have hsR : (4 : ℝ) ≤ s := by exact_mod_cast hs
  have hsp : (0 : ℝ) < s := by linarith
  let y0 : ℝ := ((s : ℝ) - 2) / ((s : ℝ) * ((s : ℝ) - 1))
  have hy0 : 0 < y0 := div_pos (by linarith) (mul_pos hsp (by linarith))
  have hleft : y0 ≤ x / q := hR.1
  have hprod : y0 * q ≤ x := (le_div_iff₀ hq).mp hleft
  have hxp : 0 < x := lt_of_lt_of_le (mul_pos hy0 hq) hprod
  let l : ℝ := (s : ℝ) * x
  let u : ℝ := min 1 (x / y0)
  have hlp : 0 < l := mul_pos hsp hxp
  have hup : 0 < u := lt_min (by norm_num) (div_pos hxp hy0)
  have hlq : l ≤ q := by
    have h := (div_le_div_iff₀ hq hsp).mp hR.2
    dsimp [l]
    nlinarith
  have hqu : q ≤ u := le_min hq1 ((le_div_iff₀ hy0).mpr (by nlinarith))
  let f : ℝ → ℝ := fun t =>
    (((s : ℝ) - 4) / 2) * t^2 + (1 - (s : ℝ) * ((s : ℝ) - 2) * x) * t +
      ((s : ℝ) - 1) * (s : ℝ)^2 * x^2 / 2
  have hf : ∀ t : ℝ, t ≠ 0 → peelValue (R s) x t = f t :=
    fun _ ht => R_peel_polynomial s ht
  have hconv : f q ≤ max (f l) (f u) :=
    convex_quadratic_le_max (by linarith) hlq hqu
  have hfl : f l < Phi (s + 1) x := by
    rw [← hf l (ne_of_gt hlp)]
    have hratio : x / l = 1 / (s : ℝ) := by dsimp [l]; field_simp
    unfold peelValue
    rw [hratio, R_right_endpoint (by omega)]
    change (s : ℝ) * x * (1 - (s : ℝ) * x) + ((s : ℝ) * x)^2 * (1 / 2) < _
    have heq := complete_peel_boundary s x
    linarith
  have hfu : f u < Phi (s + 1) x := by
    rw [← hf u (ne_of_gt hup)]
    by_cases hupper : 1 ≤ x / y0
    · have hu : u = 1 := min_eq_left hupper
      rw [hu]
      simp only [peelValue, one_mul, one_pow, sub_self, mul_zero, zero_add, div_one]
      have hyx : y0 ≤ x := by
        have h := (le_div_iff₀ hy0).mp hupper
        simpa using h
      exact (R_le_next_B_last (by omega) hx0 hx1 hyx).trans_lt hlast
    · have hu : u = x / y0 := min_eq_right (le_of_not_ge hupper)
      have hratio : x / u = y0 := by rw [hu]; field_simp
      have hcompare : peelValue (R s) x u < peelValue (B s (s - 1)) x u := by
        unfold peelValue
        rw [hratio]
        have h := mul_lt_mul_of_pos_left
          (R_left_lt_B_last (s := s) (by omega)) (sq_pos_of_pos hup)
        change u^2 * R s y0 < u^2 * B s (s - 1) y0 at h
        linarith
      exact hcompare.trans_le ((B_peel_le (by omega) (ne_of_gt hup)).trans
        (B_le_Phi (by omega) (by omega) (by omega) x))
  rw [hf q (ne_of_gt hq)]
  exact hconv.trans_lt (max_lt hfl hfu)

theorem A_peel_lt_B_two_of_past_endpoint {s : ℕ} (hs : 3 ≤ s) {x q : ℝ}
    (hx : 1 / (2 * (s : ℝ)) < x) (hq : 0 < q) (hA : ADomain s (x / q)) :
    peelValue (A s) x q < B (s + 1) 2 x := by
  have hsR : (3 : ℝ) ≤ s := by exact_mod_cast hs
  have hd : 0 < 2 * ((s : ℝ) - 1) := by linarith
  have hsp : (0 : ℝ) < s := by linarith
  have hxp : 0 < x := (by positivity : 0 < 1 / (2 * (s : ℝ))).trans hx
  let t : ℝ := 2 * ((s : ℝ) - 1) * x
  have ht : 0 < t := mul_pos hd hxp
  have htq : t ≤ q := by
    have h := (div_le_div_iff₀ hq hd).mp hA.2
    dsimp [t]
    nlinarith
  have hxmul : 1 < 2 * (s : ℝ) * x := by
    have h := (div_lt_iff₀ (by positivity : 0 < 2 * (s : ℝ))).mp hx
    nlinarith
  have hvertex : 1 ≤ 2 * ((s : ℝ) / (2 * ((s : ℝ) - 1))) * t := by
    have heq : 2 * ((s : ℝ) / (2 * ((s : ℝ) - 1))) * t = 2 * s * x := by
      dsimp [t]
      field_simp [show (s : ℝ) - 1 ≠ 0 by linarith]
      <;> ring
    rw [heq]
    exact hxmul.le
  have hquad := concave_quadratic_right_le
    (show 0 ≤ (s : ℝ) / (2 * ((s : ℝ) - 1)) from div_nonneg hsp.le hd.le) htq hvertex
  have hbound : peelValue (A s) x q ≤ peelValue (A s) x t := by
    rw [A_peel_polynomial (by omega) (ne_of_gt hq),
      A_peel_polynomial (by omega) (ne_of_gt ht)]
    nlinarith
  have hratio : x / t = 1 / (2 * ((s : ℝ) - 1)) := by dsimp [t]; field_simp
  have hboundary : peelValue (A s) x t = peelValue (B s 2) x t := by
    unfold peelValue
    rw [hratio, A_tangent_eq_B_two hs]
  have hoptgap : t - BPeelOptimizer s 2 x =
      (((s : ℝ) - 2) / ((s : ℝ) - 1)) * (2 * s * x - 1) := by
    dsimp [t, BPeelOptimizer]
    norm_num only [Nat.cast_ofNat]
    have hden : (s : ℝ) + 1 - 2 = s - 1 := by ring
    rw [hden]
    field_simp [show (s : ℝ) - 1 ≠ 0 by linarith]
    <;> ring
  have hne : t ≠ BPeelOptimizer s 2 x := by
    have hp : 0 < t - BPeelOptimizer s 2 x := by
      rw [hoptgap]
      exact mul_pos (div_pos (by linarith) (by linarith)) (by linarith)
    exact ne_of_gt (sub_pos.mp hp)
  have hstrict : peelValue (B s 2) x t < B (s + 1) 2 x :=
    lt_of_le_of_ne (B_peel_le (by omega) (ne_of_gt ht))
      (fun he => hne ((B_peel_eq_iff (by omega) (ne_of_gt ht)).mp he))
  exact hbound.trans_lt (hboundary ▸ hstrict)

theorem peel_Phi_equality_trace {s : ℕ} (hs : 3 ≤ s) {x q : ℝ}
    (hx0 : 0 ≤ x) (hq : 0 < q)
    (hRstrict : RDomain s (x / q) → peelValue (R s) x q < Phi (s + 1) x)
    (heq : peelValue (Phi s) x q = Phi (s + 1) x) :
    (∃ i, 1 ≤ i ∧ i < s ∧ B (s + 1) i x = Phi (s + 1) x ∧
      q = BPeelOptimizer s i x) ∨
    (ADomain (s + 1) x ∧ A (s + 1) x = Phi (s + 1) x ∧ q = ((s : ℝ) - 1) / s) := by
  rcases Phi_mem_branchValues hs (x / q) with ⟨i, hi, his, hval⟩ | ⟨hA, hval⟩ | ⟨hR, hval⟩
  · have he : peelValue (B s i) x q = Phi (s + 1) x := by
      simpa only [peelValue, hval] using heq
    have hle := B_peel_le (x := x) his (ne_of_gt hq)
    have hPhi := B_le_Phi (by omega : 3 ≤ s + 1) hi (by omega) x
    have hactive : B (s + 1) i x = Phi (s + 1) x := by rw [he] at hle; exact le_antisymm hPhi hle
    exact Or.inl ⟨i, hi, his, hactive,
      (B_peel_eq_iff his (ne_of_gt hq)).mp (he.trans hactive.symm)⟩
  · have he : peelValue (A s) x q = Phi (s + 1) x := by
      simpa only [peelValue, hval] using heq
    by_cases hxA : x ≤ 1 / (2 * (s : ℝ))
    · have hxA' : ADomain (s + 1) x :=
        ⟨hx0, by simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hxA⟩
      have hle := A_peel_le (x := x) (by omega : 2 ≤ s) (ne_of_gt hq)
      have hPhi := A_le_Phi (by omega : 3 ≤ s + 1) hxA'
      have hactive : A (s + 1) x = Phi (s + 1) x := by rw [he] at hle; exact le_antisymm hPhi hle
      exact Or.inr ⟨hxA', hactive,
        (A_peel_eq_iff (by omega) (ne_of_gt hq)).mp (he.trans hactive.symm)⟩
    · have hlt := (A_peel_lt_B_two_of_past_endpoint hs (lt_of_not_ge hxA) hq hA).trans_le
        (B_le_Phi (by omega : 3 ≤ s + 1) (by omega) (by omega) x)
      exact False.elim (hlt.ne he)
  · have he : peelValue (R s) x q = Phi (s + 1) x := by
      simpa only [peelValue, hval] using heq
    exact False.elim ((hRstrict hR).ne he)

theorem one_sub_BPeelOptimizer {s i : ℕ} (his : i < s) (x : ℝ) :
    1 - BPeelOptimizer s i x = (1 - (i : ℝ) * x) / ((s : ℝ) + 1 - i) := by
  have hiR : (i : ℝ) < s := by exact_mod_cast his
  have hden : (s : ℝ) + 1 - i ≠ 0 := by linarith
  unfold BPeelOptimizer
  field_simp
  <;> ring

end DensityHS
