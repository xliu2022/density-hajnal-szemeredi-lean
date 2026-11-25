module

public import DensityHS.Basic.Envelope

/-!
# Algebra for the peeling recursion

Exact completed-square identities and branch bounds for Lemma 3.3 of
*The density Hajnal–Szemerédi theorem*.

Formalization author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS

/-- Adding a universal atom of mass `1-q` to a normalized remainder. -/
noncomputable def peelValue (f : ℝ → ℝ) (x q : ℝ) : ℝ :=
  q * (1 - q) + q ^ 2 * f (x / q)

/-- The unique unconstrained maximizing remainder mass for a `B` branch. -/
noncomputable def BPeelOptimizer (s i : ℕ) (x : ℝ) : ℝ :=
  ((s : ℝ) - i + i * x) / ((s : ℝ) + 1 - i)

theorem B_peel_square {s i : ℕ} (his : i < s) {x q : ℝ} (hq : q ≠ 0) :
    peelValue (B s i) x q = B (s + 1) i x -
      (((s : ℝ) + 1 - i) / (2 * ((s : ℝ) - i))) *
        (q - BPeelOptimizer s i x) ^ 2 := by
  have hsi : (i : ℝ) < s := by exact_mod_cast his
  have hd : (s : ℝ) - i ≠ 0 := by linarith
  have hd' : (s : ℝ) + 1 - i ≠ 0 := by linarith
  simp only [peelValue, B, BPeelOptimizer, Nat.cast_add, Nat.cast_one]
  field_simp
  <;> ring

theorem B_peel_le {s i : ℕ} (his : i < s) {x q : ℝ} (hq : q ≠ 0) :
    peelValue (B s i) x q ≤ B (s + 1) i x := by
  rw [B_peel_square his hq]
  have hsi : (i : ℝ) < s := by exact_mod_cast his
  have hc : 0 ≤ ((s : ℝ) + 1 - i) / (2 * ((s : ℝ) - i)) :=
    div_nonneg (by linarith) (by linarith)
  have hp := mul_nonneg hc (sq_nonneg (q - BPeelOptimizer s i x))
  linarith

theorem B_peel_eq_iff {s i : ℕ} (his : i < s) {x q : ℝ} (hq : q ≠ 0) :
    peelValue (B s i) x q = B (s + 1) i x ↔ q = BPeelOptimizer s i x := by
  rw [B_peel_square his hq]
  have hsi : (i : ℝ) < s := by exact_mod_cast his
  have hc : 0 < ((s : ℝ) + 1 - i) / (2 * ((s : ℝ) - i)) :=
    div_pos (by linarith) (by linarith)
  constructor
  · intro h
    have hz : (((s : ℝ) + 1 - i) / (2 * ((s : ℝ) - i))) *
        (q - BPeelOptimizer s i x) ^ 2 = 0 := by linarith
    have := (mul_eq_zero.mp hz).resolve_left (ne_of_gt hc)
    nlinarith [sq_nonneg (q - BPeelOptimizer s i x)]
  · intro h
    simp [h]

theorem BPeelOptimizer_feasible {s i : ℕ} (hs : 1 ≤ s) (his : i < s)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / ((s : ℝ) + 1)) :
    (s : ℝ) * x ≤ BPeelOptimizer s i x ∧ BPeelOptimizer s i x ≤ 1 := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  have hsi : (i : ℝ) < s := by exact_mod_cast his
  have hden : 0 < (s : ℝ) + 1 - i := by linarith
  have hsx : ((s : ℝ) + 1) * x ≤ 1 := by
    have := (le_div_iff₀ (by linarith : (0 : ℝ) < s + 1)).mp hx1
    nlinarith
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  unfold BPeelOptimizer
  constructor
  · apply (le_div_iff₀ hden).mpr
    have hp := mul_nonneg (le_of_lt (sub_pos.mpr hsi)) (sub_nonneg.mpr hsx)
    nlinarith
  · apply (div_le_iff₀ hden).mpr
    nlinarith

theorem A_peel_square {s : ℕ} (hs : 2 ≤ s) {x q : ℝ} (hq : q ≠ 0) :
    peelValue (A s) x q = A (s + 1) x -
      ((s : ℝ) / (2 * ((s : ℝ) - 1))) * (q - ((s : ℝ) - 1) / s) ^ 2 := by
  have hs1 : (1 : ℝ) < s := by exact_mod_cast (by omega : 1 < s)
  have hs0 : (s : ℝ) ≠ 0 := by linarith
  have hd : (s : ℝ) - 1 ≠ 0 := by linarith
  simp only [peelValue, A, Nat.cast_add, Nat.cast_one]
  simp only [add_sub_cancel_right]
  field_simp [hq, hs0, hd]
  <;> ring

theorem A_peel_le {s : ℕ} (hs : 2 ≤ s) {x q : ℝ} (hq : q ≠ 0) :
    peelValue (A s) x q ≤ A (s + 1) x := by
  rw [A_peel_square hs hq]
  have hs1 : (1 : ℝ) < s := by exact_mod_cast (by omega : 1 < s)
  have hc : 0 ≤ (s : ℝ) / (2 * ((s : ℝ) - 1)) := by positivity
  have hp := mul_nonneg hc (sq_nonneg (q - ((s : ℝ) - 1) / s))
  linarith

theorem A_peel_eq_iff {s : ℕ} (hs : 2 ≤ s) {x q : ℝ} (hq : q ≠ 0) :
    peelValue (A s) x q = A (s + 1) x ↔ q = ((s : ℝ) - 1) / s := by
  rw [A_peel_square hs hq]
  have hs1 : (1 : ℝ) < s := by exact_mod_cast (by omega : 1 < s)
  have hc : 0 < (s : ℝ) / (2 * ((s : ℝ) - 1)) := by positivity
  constructor
  · intro h
    have hz : ((s : ℝ) / (2 * ((s : ℝ) - 1))) *
        (q - ((s : ℝ) - 1) / s) ^ 2 = 0 := by linarith
    have := (mul_eq_zero.mp hz).resolve_left (ne_of_gt hc)
    nlinarith [sq_nonneg (q - ((s : ℝ) - 1) / s)]
  · intro h
    simp [h]

/-- The normalized complete remainder gives the last `B` branch. -/
theorem complete_peel_boundary (s : ℕ) (x : ℝ) :
    ((s : ℝ) * x) * (1 - (s : ℝ) * x) + ((s : ℝ) * x) ^ 2 / 2 =
      B (s + 1) s x := by
  simp only [B, Nat.cast_add, Nat.cast_one]
  have h : (s : ℝ) + 1 - s = 1 := by ring
  rw [h]
  ring

/-- The `R` transform is quadratic, with coefficient `(s-4)/2`. -/
theorem R_peel_polynomial (s : ℕ) {x q : ℝ} (hq : q ≠ 0) :
    peelValue (R s) x q =
      (((s : ℝ) - 4) / 2) * q ^ 2 +
        (1 - (s : ℝ) * ((s : ℝ) - 2) * x) * q +
        ((s : ℝ) - 1) * (s : ℝ) ^ 2 * x ^ 2 / 2 := by
  unfold peelValue R
  field_simp
  <;> ring

theorem A_peel_polynomial {s : ℕ} (hs : 2 ≤ s) {x q : ℝ} (hq : q ≠ 0) :
    peelValue (A s) x q = q - (s : ℝ) / (2 * ((s : ℝ) - 1)) * q ^ 2 + 2 * x ^ 2 := by
  have hs1 : (1 : ℝ) < s := by exact_mod_cast (by omega : 1 < s)
  have hd : (s : ℝ) - 1 ≠ 0 := by linarith
  unfold peelValue A
  field_simp
  <;> ring

/-- A concave quadratic decreases to the right of its vertex. -/
theorem concave_quadratic_right_le {a b t u : ℝ} (ha : 0 ≤ a) (htu : t ≤ u)
    (hvertex : b ≤ 2 * a * t) : b * u - a * u ^ 2 ≤ b * t - a * t ^ 2 := by
  have h1 := mul_nonneg (sub_nonneg.mpr htu) (sub_nonneg.mpr hvertex)
  have h2 := mul_nonneg ha (sq_nonneg (u - t))
  nlinarith

/-- The exceptional branch is controlled even when its unconstrained maximum
has left the admissible domain of the next exceptional branch. -/
theorem A_peel_le_Phi {s : ℕ} (hs : 3 ≤ s) {x q : ℝ} (hx0 : 0 ≤ x)
    (hq : 0 < q) (hA : ADomain s (x / q)) :
    peelValue (A s) x q ≤ Phi (s + 1) x := by
  have hs2 : (2 : ℝ) < s := by exact_mod_cast (by omega : 2 < s)
  have hd : 0 < 2 * ((s : ℝ) - 1) := by linarith
  by_cases hxA : x ≤ 1 / (2 * (s : ℝ))
  · apply (A_peel_le (by omega) (ne_of_gt hq)).trans
    apply A_le_Phi (by omega)
    exact ⟨hx0, by simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hxA⟩
  have hxp : 0 < x := lt_of_lt_of_le (by positivity : 0 < 1 / (2 * (s : ℝ)))
    (le_of_not_ge hxA)
  let t : ℝ := 2 * ((s : ℝ) - 1) * x
  have ht : 0 < t := mul_pos hd hxp
  have htq : t ≤ q := by
    have h := (div_le_div_iff₀ hq hd).mp hA.2
    dsimp [t]
    nlinarith
  have hk : 0 ≤ (s : ℝ) / (2 * ((s : ℝ) - 1)) := div_nonneg (Nat.cast_nonneg _) hd.le
  have hvertex : (1 : ℝ) ≤ 2 * ((s : ℝ) / (2 * ((s : ℝ) - 1))) * t := by
    have h := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * s)).mp (le_of_not_ge hxA)
    have heq : 2 * ((s : ℝ) / (2 * ((s : ℝ) - 1))) * t = 2 * s * x := by
      dsimp [t]
      field_simp [show (s : ℝ) - 1 ≠ 0 by linarith]
      <;> ring
    rw [heq]
    nlinarith
  have hquad := concave_quadratic_right_le hk htq hvertex
  have hbound : peelValue (A s) x q ≤ peelValue (A s) x t := by
    rw [A_peel_polynomial (by omega) (ne_of_gt hq),
      A_peel_polynomial (by omega) (ne_of_gt ht)]
    nlinarith
  have hratio : x / t = 1 / (2 * ((s : ℝ) - 1)) := by
    dsimp [t]
    field_simp
  have hboundary : peelValue (A s) x t = peelValue (B s 2) x t := by
    unfold peelValue
    rw [hratio, A_tangent_eq_B_two hs]
  calc
    peelValue (A s) x q ≤ peelValue (A s) x t := hbound
    _ = peelValue (B s 2) x t := hboundary
    _ ≤ B (s + 1) 2 x := B_peel_le (by omega) (ne_of_gt ht)
    _ ≤ Phi (s + 1) x := B_le_Phi (by omega) (by omega) (by omega) x

/-- The maximum principle for a convex quadratic, including the affine case. -/
theorem convex_quadratic_le_max {a b c l u q : ℝ} (ha : 0 ≤ a)
    (hlq : l ≤ q) (hqu : q ≤ u) :
    a * q ^ 2 + b * q + c ≤ max (a * l ^ 2 + b * l + c) (a * u ^ 2 + b * u + c) := by
  have hconv : ConvexOn ℝ Set.univ (fun t : ℝ => a * t ^ 2 + b * t + c) := by
    refine ⟨convex_univ, ?_⟩
    intro v _ w _ α β hα hβ hsum
    simp only [smul_eq_mul]
    have hp := mul_nonneg (mul_nonneg (mul_nonneg ha hα) hβ) (sq_nonneg (v - w))
    have hβeq : β = 1 - α := by linarith
    have hid :
        α * (a * v ^ 2 + b * v + c) + β * (a * w ^ 2 + b * w + c) -
          (a * (α * v + β * w) ^ 2 + b * (α * v + β * w) + c) =
            a * α * β * (v - w) ^ 2 := by rw [hβeq]; ring
    linarith
  exact hconv.le_max_of_mem_Icc (Set.mem_univ _) (Set.mem_univ _) ⟨hlq, hqu⟩

theorem R_left_le_B_last {s : ℕ} (hs : 3 ≤ s) :
    R s (((s : ℝ) - 2) / ((s : ℝ) * ((s : ℝ) - 1))) ≤
      B s (s - 1) (((s : ℝ) - 2) / ((s : ℝ) * ((s : ℝ) - 1))) := by
  have hs2 : (2 : ℝ) < s := by exact_mod_cast (by omega : 2 < s)
  have hs0 : (s : ℝ) ≠ 0 := by linarith
  have hs1 : (s : ℝ) - 1 ≠ 0 := by linarith
  have hgap :
      B s (s - 1) (((s : ℝ) - 2) / ((s : ℝ) * ((s : ℝ) - 1))) -
        R s (((s : ℝ) - 2) / ((s : ℝ) * ((s : ℝ) - 1))) =
          ((s : ℝ) - 2) ^ 2 / (2 * ((s : ℝ) - 1) * (s : ℝ) ^ 2) := by
    unfold B R
    rw [Nat.cast_sub (by omega : 1 ≤ s), Nat.cast_one]
    have hden : (s : ℝ) - ((s : ℝ) - 1) = 1 := by ring
    rw [hden]
    field_simp
    <;> ring
  have hp : 0 ≤ ((s : ℝ) - 2) ^ 2 / (2 * ((s : ℝ) - 1) * (s : ℝ) ^ 2) :=
    div_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (sq_nonneg _))
  linarith

theorem R_le_next_B_last {s : ℕ} (hs : 3 ≤ s) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / ((s : ℝ) + 1))
    (hleft : ((s : ℝ) - 2) / ((s : ℝ) * ((s : ℝ) - 1)) ≤ x) :
    R s x ≤ B (s + 1) s x := by
  have hs2 : (2 : ℝ) < s := by exact_mod_cast (by omega : 2 < s)
  have hden : 0 < (s : ℝ) * ((s : ℝ) - 1) := mul_pos (by linarith) (by linarith)
  have hxl := (div_le_iff₀ hden).mp hleft
  have hxu := (le_div_iff₀ (by linarith : (0 : ℝ) < s + 1)).mp hx1
  have h1 : 0 ≤ 1 - (s : ℝ) * x := by nlinarith
  have h2 : 0 ≤ (s : ℝ) ^ 2 * x - (s : ℝ) + 2 := by nlinarith
  have hp := mul_nonneg h1 h2
  have hgap : B (s + 1) s x - R s x =
      (1 - (s : ℝ) * x) * ((s : ℝ) ^ 2 * x - (s : ℝ) + 2) / 2 := by
    simp only [B, R, Nat.cast_add, Nat.cast_one]
    have h : (s : ℝ) + 1 - s = 1 := by ring
    rw [h]
    ring
  linarith

/-- For `s ≥ 4`, the final branch is convex after peeling, and its two
admissible endpoints are controlled by the `B` branches. -/
theorem R_peel_le_Phi_of_four_le {s : ℕ} (hs : 4 ≤ s) {x q : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / ((s : ℝ) + 1))
    (hq : 0 < q) (hq1 : q ≤ 1) (hR : RDomain s (x / q)) :
    peelValue (R s) x q ≤ Phi (s + 1) x := by
  have hs3 : (3 : ℝ) < s := by exact_mod_cast (by omega : 3 < s)
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
    (((s : ℝ) - 4) / 2) * t ^ 2 + (1 - (s : ℝ) * ((s : ℝ) - 2) * x) * t +
      ((s : ℝ) - 1) * (s : ℝ) ^ 2 * x ^ 2 / 2
  have hf : ∀ t : ℝ, t ≠ 0 → peelValue (R s) x t = f t :=
    fun t ht => R_peel_polynomial s ht
  have hconv : f q ≤ max (f l) (f u) := by
    apply convex_quadratic_le_max _ hlq hqu
    have hs4 : (4 : ℝ) ≤ s := by exact_mod_cast hs
    linarith
  have hfl : f l ≤ Phi (s + 1) x := by
    rw [← hf l (ne_of_gt hlp)]
    have hratio : x / l = 1 / (s : ℝ) := by dsimp [l]; field_simp
    unfold peelValue
    rw [hratio, R_right_endpoint (by omega)]
    change (s : ℝ) * x * (1 - (s : ℝ) * x) + ((s : ℝ) * x) ^ 2 * (1 / 2) ≤ _
    have heq := complete_peel_boundary s x
    have hB := B_le_Phi (by omega : 3 ≤ s + 1) (by omega : 1 ≤ s) (by omega : s < s + 1) x
    linarith
  have hfu : f u ≤ Phi (s + 1) x := by
    rw [← hf u (ne_of_gt hup)]
    by_cases hupper : 1 ≤ x / y0
    · have hu : u = 1 := min_eq_left hupper
      rw [hu]
      simp only [peelValue, one_mul, one_pow, sub_self, mul_zero, zero_add, div_one]
      have hyx : y0 ≤ x := by
        have h := (le_div_iff₀ hy0).mp hupper
        simpa using h
      exact (R_le_next_B_last (by omega) hx0 hx1 hyx).trans
        (B_le_Phi (by omega) (by omega) (by omega) x)
    · have hu : u = x / y0 := min_eq_right (le_of_not_ge hupper)
      have hratio : x / u = y0 := by rw [hu]; field_simp
      have hcompare : peelValue (R s) x u ≤ peelValue (B s (s - 1)) x u := by
        unfold peelValue
        rw [hratio]
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_left (R_left_le_B_last (by omega)) (sq_nonneg u))
      exact hcompare.trans ((B_peel_le (by omega) (ne_of_gt hup)).trans
        (B_le_Phi (by omega) (by omega) (by omega) x))
  rw [hf q (ne_of_gt hq)]
  exact hconv.trans (max_le hfl hfu)

/-- A concave quadratic increases to the left of its vertex. -/
theorem concave_quadratic_left_le {a b t u : ℝ} (ha : 0 ≤ a) (htu : u ≤ t)
    (hvertex : 2 * a * t ≤ b) : b * u - a * u ^ 2 ≤ b * t - a * t ^ 2 := by
  have h1 := mul_nonneg (sub_nonneg.mpr htu) (sub_nonneg.mpr hvertex)
  have h2 := mul_nonneg ha (sq_nonneg (t - u))
  nlinarith

/-- The exceptional concave `R₃` transform, split at `1/9` and `1/6`. -/
theorem R_three_peel_le_Phi_four {x q : ℝ} (hq : 0 < q)
    (hR : RDomain 3 (x / q)) : peelValue (R 3) x q ≤ Phi 4 x := by
  have hxl : (1 / 6 : ℝ) ≤ x / q := by norm_num [RDomain] at hR ⊢; exact hR.1
  have hxu : x / q ≤ (1 / 3 : ℝ) := by norm_num [RDomain] at hR ⊢; exact hR.2
  have hxq : 0 < x := by
    have h := (le_div_iff₀ hq).mp hxl
    nlinarith
  have hlq : 3 * x ≤ q := by
    have h := (div_le_iff₀ hq).mp hxu
    linarith
  have hqu : q ≤ 6 * x := by
    have h := (le_div_iff₀ hq).mp hxl
    linarith
  have hpoly : ∀ t : ℝ, t ≠ 0 →
      peelValue (R 3) x t = (1 - 3 * x) * t - t ^ 2 / 2 + 9 * x ^ 2 := by
    intro t ht
    rw [R_peel_polynomial 3 ht]
    norm_num
    ring
  by_cases hxsmall : x ≤ 1 / 9
  · have ht : (0 : ℝ) < 6 * x := by linarith
    have hquad := concave_quadratic_left_le (a := (1 / 2 : ℝ))
      (b := 1 - 3 * x) (t := 6 * x) (u := q) (by norm_num) hqu (by linarith)
    have hbound : peelValue (R 3) x q ≤ peelValue (R 3) x (6 * x) := by
      rw [hpoly q (ne_of_gt hq), hpoly (6 * x) (ne_of_gt ht)]
      nlinarith
    have hratio : x / (6 * x) = (1 / 6 : ℝ) := by field_simp
    have hboundary : peelValue (R 3) x (6 * x) ≤ peelValue (B 3 1) x (6 * x) := by
      unfold peelValue
      rw [hratio]
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      norm_num [R, B]
    exact hbound.trans (hboundary.trans
      ((B_peel_le (by norm_num : 1 < 3) (ne_of_gt ht)).trans
        (B_le_Phi (by norm_num) (by norm_num) (by norm_num) x)))
  by_cases hxmiddle : x ≤ 1 / 6
  · have hmax : peelValue (R 3) x q ≤ 1 / 2 - 3 * x + 27 * x ^ 2 / 2 := by
      rw [hpoly q (ne_of_gt hq)]
      nlinarith [sq_nonneg (q - (1 - 3 * x))]
    have hgap : 1 / 2 - 3 * x + 27 * x ^ 2 / 2 ≤ A 4 x := by
      have hprod := mul_nonneg (sub_nonneg.mpr (le_of_not_ge hxsmall))
        (sub_nonneg.mpr hxmiddle)
      norm_num [A]
      nlinarith
    exact hmax.trans (hgap.trans (A_le_Phi (by norm_num)
      ⟨hxq.le, by norm_num; exact hxmiddle⟩))
  · have hquad := concave_quadratic_right_le (a := (1 / 2 : ℝ))
      (b := 1 - 3 * x) (t := 3 * x) (u := q) (by norm_num) hlq (by linarith)
    have hbound : peelValue (R 3) x q ≤ B 4 3 x := by
      rw [hpoly q (ne_of_gt hq)]
      norm_num [B]
      nlinarith
    exact hbound.trans (B_le_Phi (by norm_num) (by norm_num) (by norm_num) x)

/-- The second matching branch after adding a universal atom. -/
theorem matching_second_peel_le {x q : ℝ} (hx0 : 0 ≤ x) (hq : 0 < q)
    (hqx : 2 * x ≤ q) : peelValue (fun y => 2 * y ^ 2) x q ≤ Phi 3 x := by
  have hpoly : peelValue (fun y => 2 * y ^ 2) x q = q - q ^ 2 + 2 * x ^ 2 := by
    unfold peelValue
    field_simp
    <;> ring
  by_cases hx : x ≤ 1 / 4
  · have hb : q - q ^ 2 + 2 * x ^ 2 ≤ A 3 x := by
      norm_num [A]
      nlinarith [sq_nonneg (q - 1 / 2)]
    rw [hpoly]
    exact hb.trans (A_le_Phi (by norm_num) ⟨hx0, by norm_num; exact hx⟩)
  · have hquad := concave_quadratic_right_le (a := (1 : ℝ)) (b := 1)
      (t := 2 * x) (u := q) (by norm_num) hqx (by linarith)
    have hb : q - q ^ 2 + 2 * x ^ 2 ≤ B 3 2 x := by
      norm_num [B]
      nlinarith
    rw [hpoly]
    exact hb.trans (B_le_Phi (by norm_num) (by norm_num) (by norm_num) x)

/-- The full pointwise peeling inequality of Lemma 3.3, with the normalized
remainder indexed by `s` and the original clique size `s + 1`. -/
theorem peel_Phi_le {s : ℕ} (hs : 2 ≤ s) {x q : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / ((s : ℝ) + 1))
    (hq : 0 < q) (hq1 : q ≤ 1) (hqx : (s : ℝ) * x ≤ q) :
    peelValue (Phi s) x q ≤ Phi (s + 1) x := by
  by_cases hs2 : s = 2
  · subst s
    change peelValue Phi2 x q ≤ Phi 3 x
    by_cases hbranch : x / q - (x / q) ^ 2 / 2 ≤ 2 * (x / q) ^ 2
    · have heq : peelValue Phi2 x q = peelValue (fun y => 2 * y ^ 2) x q := by
        simp only [peelValue, Phi2, max_eq_right hbranch]
      rw [heq]
      exact matching_second_peel_le hx0 hq (by simpa using hqx)
    · have hfirst : x / q - (x / q) ^ 2 / 2 = B 2 1 (x / q) := by
        norm_num [B]
        ring
      have heq : peelValue Phi2 x q = peelValue (B 2 1) x q := by
        unfold peelValue Phi2
        rw [max_eq_left (le_of_not_ge hbranch), hfirst]
      rw [heq]
      exact (B_peel_le (by norm_num) (ne_of_gt hq)).trans
        (B_le_Phi (by norm_num) (by norm_num) (by norm_num) x)
  have hs3 : 3 ≤ s := by omega
  have hmem := Phi_mem_branchValues hs3 (x / q)
  rcases hmem with ⟨i, hi, his, hval⟩ | ⟨hA, hval⟩ | ⟨hR, hval⟩
  · change q * (1 - q) + q ^ 2 * Phi s (x / q) ≤ _
    rw [hval]
    exact (B_peel_le his (ne_of_gt hq)).trans (B_le_Phi (by omega) hi (by omega) x)
  · change q * (1 - q) + q ^ 2 * Phi s (x / q) ≤ _
    rw [hval]
    exact A_peel_le_Phi hs3 hx0 hq hA
  · change q * (1 - q) + q ^ 2 * Phi s (x / q) ≤ _
    rw [hval]
    by_cases hs4 : 4 ≤ s
    · exact R_peel_le_Phi_of_four_le hs4 hx0 hx1 hq hq1 hR
    · have hsval : s = 3 := by omega
      subst s
      exact R_three_peel_le_Phi_four hq hR

end DensityHS
