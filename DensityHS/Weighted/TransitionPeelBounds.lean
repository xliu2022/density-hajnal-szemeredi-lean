module

public import DensityHS.Weighted.PeelingStrict

/-!
# Feasible peel sizes and the strict zero-mass gap at early transitions

Author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS

theorem B_peel_length_pos {r i : ℕ} (hir : i < r) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 1 / (r : ℝ)) :
    0 < (1 - (i : ℝ) * x) / ((r : ℝ) - i) := by
  have hrp : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hiR : (i : ℝ) < r := by exact_mod_cast hir
  have hxr := (lt_div_iff₀ hrp).mp hx1
  have hix := mul_le_mul_of_nonneg_right hiR.le hx0
  exact div_pos (by nlinarith) (by linarith)

theorem B_peel_length_le_remainder {r i : ℕ} (hr : 3 ≤ r) (hir : i < r - 1)
    {x : ℝ} (hx : x ∈ Set.Icc 0 (1 / (r : ℝ))) :
    (1 - (i : ℝ) * x) / ((r : ℝ) - i) ≤ 1 - ((r - 1 : ℕ) : ℝ) * x := by
  have hsucc : (r - 1 : ℕ) + 1 = r := by omega
  have hcast : ((r - 1 : ℕ) : ℝ) + 1 = r := by exact_mod_cast hsucc
  have hopt := BPeelOptimizer_feasible (by omega : 1 ≤ r - 1) hir hx.1
    (by simpa only [hcast] using hx.2)
  have hid := one_sub_BPeelOptimizer hir x
  rw [hcast] at hid
  linarith [hopt.1]

theorem BA_zero_mass_gt_Apeel {r : ℕ} (hr : 4 ≤ r) :
    1 / ((r : ℝ) - 1) < 1 - (r : ℝ) * AStart r := by
  have hrR : (4 : ℝ) ≤ r := by exact_mod_cast hr
  have hd1 : (r : ℝ) - 1 ≠ 0 := by linarith
  have hd2 : 4 * (r : ℝ) - 3 ≠ 0 := by linarith
  have hgap : 1 - (r : ℝ) * AStart r - 1 / ((r : ℝ) - 1) =
      (2 * (r : ℝ)^2 - 9 * r + 6) / ((4 * (r : ℝ) - 3) * ((r : ℝ) - 1)) := by
    unfold AStart
    field_simp [hd1, hd2]
    ring_nf
    field_simp [show (-3 + (r : ℝ) * 4) ≠ 0 by linarith]
    <;> ring
  have hnum : 0 < 2 * (r : ℝ)^2 - 9 * r + 6 := by
    nlinarith [sq_nonneg ((r : ℝ) - 4)]
  have hp := div_pos hnum (mul_pos (by linarith : 0 < 4 * (r : ℝ) - 3)
    (by linarith : 0 < (r : ℝ) - 1))
  linarith

theorem BA_transition_peel_bounds {r : ℕ} (hr : 4 ≤ r) {L : ℝ}
    (hL0 : (1 - AStart r) / ((r : ℝ) - 1) < L)
    (hL1 : L < 1 / ((r : ℝ) - 1)) :
    0 < L ∧ L < 1 ∧ L ≤ 1 - ((r - 1 : ℕ) : ℝ) * AStart r ∧
      L < 1 - (r : ℝ) * AStart r := by
  have hrR : (4 : ℝ) ≤ r := by exact_mod_cast hr
  have hx0 := AStart_pos (by omega : 3 ≤ r)
  have hxA := AStart_lt_AEnd (by omega : 3 ≤ r)
  have hxr : AStart r < 1 / (r : ℝ) := hxA.trans_le (A_endpoint_le (by omega))
  have hbase : 0 < (1 - AStart r) / ((r : ℝ) - 1) := by
    simpa only [Nat.cast_one, one_mul] using
      B_peel_length_pos (i := 1) (by omega : 1 < r) hx0.le hxr
  have hLpos : 0 < L := hbase.trans hL0
  have hAone : 1 / ((r : ℝ) - 1) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have hrec : 1 / ((r : ℝ) - 1) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hxmul : ((r : ℝ) - 1) * AStart r < 1 / 2 := by
    have h := (lt_div_iff₀ (by linarith : 0 < 2 * ((r : ℝ) - 1))).mp hxA
    nlinarith
  refine ⟨hLpos, hL1.trans hAone, ?_, hL1.trans (BA_zero_mass_gt_Apeel hr)⟩
  rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
  linarith

theorem BB_zero_mass_gt_upper_peel {r i : ℕ} (hi : 2 ≤ i) (hir : i ≤ r - 3)
    {x : ℝ} (hx : x = BCrossing r i (i + 1)) :
    (1 - ((i + 1 : ℕ) : ℝ) * x) / ((r : ℝ) - (i + 1 : ℕ)) < 1 - (r : ℝ) * x := by
  have hr : 0 < r := by omega
  have hrp : (0 : ℝ) < r := by exact_mod_cast hr
  let d : ℝ := (r : ℝ) - (i + 1 : ℕ)
  let S : ℝ := Real.sqrt (((r : ℝ) - i) * ((r : ℝ) - (i + 1 : ℕ)))
  have hd : 2 ≤ d := by
    have h : ((i + 1 : ℕ) : ℝ) + 2 ≤ r := by exact_mod_cast (by omega : i + 1 + 2 ≤ r)
    dsimp [d]
    linarith
  have hdi : (r : ℝ) - i = d + 1 := by dsimp [d]; push_cast; ring
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hS2 : S^2 = (d + 1) * d := by
    dsimp [S]
    rw [hdi]
    exact Real.sq_sqrt (mul_nonneg (by linarith) (by linarith))
  have hSd : d < S := by nlinarith
  have hSbig : d < (d - 1) * S := by
    have h := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ d - 1 by linarith) hS0
    nlinarith
  have hxp : 0 < x := by rw [hx]; exact BCrossing_pos hr
  have hidentity : ((r : ℝ) + S) * x = 1 := by
    rw [hx]
    change ((r : ℝ) + S) * (1 / ((r : ℝ) + S)) = 1
    have hn : (r : ℝ) + S ≠ 0 := by positivity
    field_simp
  have hgap : (1 - (r : ℝ) * x) * d - (1 - ((i + 1 : ℕ) : ℝ) * x) =
      x * ((d - 1) * S - d) := by
    calc
      _ = x * ((d - 1) * S - d) + (d - 1) * (1 - ((r : ℝ) + S) * x) := by
        dsimp [d]
        ring
      _ = _ := by rw [hidentity]; ring
  have hp : 0 < (1 - (r : ℝ) * x) * d - (1 - ((i + 1 : ℕ) : ℝ) * x) := by
    rw [hgap]
    exact mul_pos hxp (sub_pos.mpr hSbig)
  exact (div_lt_iff₀ (show 0 < d by linarith)).mpr (sub_pos.mp hp)

theorem BB_transition_peel_bounds {r i : ℕ} (hi : 2 ≤ i) (hir : i ≤ r - 3)
    {x L : ℝ} (hx : x = BCrossing r i (i + 1))
    (hL0 : (1 - (i : ℝ) * x) / ((r : ℝ) - i) < L)
    (hL1 : L < (1 - ((i + 1 : ℕ) : ℝ) * x) / ((r : ℝ) - (i + 1 : ℕ))) :
    0 < L ∧ L < 1 ∧ L ≤ 1 - ((r - 1 : ℕ) : ℝ) * x ∧ L < 1 - (r : ℝ) * x := by
  have hr : 3 ≤ r := by omega
  have hx0 : 0 < x := by rw [hx]; exact BCrossing_pos (by omega)
  have hx1 : x < 1 / (r : ℝ) := by
    rw [hx]
    exact BCrossing_lt_right_endpoint (by omega) (by omega)
  have hLpos := (B_peel_length_pos (by omega : i < r) hx0.le hx1).trans hL0
  have hLbound := hL1.trans_le (B_peel_length_le_remainder hr
    (by omega : i + 1 < r - 1) ⟨hx0.le, hx1.le⟩)
  have hs : (0 : ℝ) < (r - 1 : ℕ) := by exact_mod_cast (by omega : 0 < r - 1)
  exact ⟨hLpos, by nlinarith [mul_pos hs hx0], hLbound.le,
    hL1.trans (BB_zero_mass_gt_upper_peel hi hir hx)⟩

end DensityHS
