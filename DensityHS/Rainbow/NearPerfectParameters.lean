module

public import DensityHS.Rainbow.RegularExtraction

/-!
# Parameters for near-perfect rainbow tilings

The fixed regularity and reserve parameters are selected before the graph
order.  A separate large-order estimate makes the regular transversal count
dominate the explicit colour-collision bound.

Formalization author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS.Rainbow

theorem exists_nearPerfect_parameters {r : ℕ} (hr : 0 < r) {δ η : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) :
    ∃ α q ε : ℝ, 0 < α ∧ α ≤ 1 / 8 ∧ 3 * α ≤ η ∧
      0 < q ∧ q ≤ 1 / 2 ∧ 0 < ε ∧ ε < q ∧ q - ε ≤ 1 ∧
      5 * ε ≤ q ^ 2 ∧ ε + q ≤ α ∧ δ / 4 + 5 * q ≤ δ - ε ∧
      2 * ε * r < α * (q - ε) ^ (r - 1) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  let α := min (η / 8) (1 / 8)
  have hα : 0 < α := by dsimp [α]; positivity
  have hαη : α ≤ η / 8 := min_le_left _ _
  have hα1 : α ≤ 1 / 8 := min_le_right _ _
  let q := min (δ / 32) (min (α / 4) (1 / 4))
  have hq : 0 < q := by dsimp [q]; positivity
  have hqδ : q ≤ δ / 32 := min_le_left _ _
  have hqα : q ≤ α / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hq1 : q ≤ 1 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  let ε := min (q ^ 2 / 8) (min (q / 2) (min (α / 4)
    (min (δ / 8) (α * (q / 2) ^ (r - 1) / (4 * r)))))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεq2 : ε ≤ q ^ 2 / 8 := min_le_left _ _
  have hεq : ε ≤ q / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hεα : ε ≤ α / 4 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hεδ : ε ≤ δ / 8 := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hεcount : ε ≤ α * (q / 2) ^ (r - 1) / (4 * r) := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨α, q, ε, hα, hα1, by linarith, hq, by linarith, hε, by linarith,
    by linarith, by nlinarith [sq_nonneg q], by linarith, by linarith, ?_⟩
  have hmult := (le_div_iff₀ (by positivity : 0 < (4 : ℝ) * r)).mp hεcount
  have hp : 0 < α * (q / 2) ^ (r - 1) := by positivity
  have hpow := pow_le_pow_left₀ (show 0 ≤ q / 2 by positivity)
    (show q / 2 ≤ q - ε by linarith) (r - 1)
  have hpow' := mul_le_mul_of_nonneg_left hpow hα.le
  nlinarith

theorem exists_rainbow_counting_order {r : ℕ} (hr : 0 < r) {A C : ℝ}
    (hA : 0 < A) (hC : 0 < C) (B : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ m : ℕ,
      (n : ℝ) ≤ 2 * C * m → 4 ≤ A * m ∧
      B * (n : ℝ) ^ (r - 1) < (A / 4) ^ r * (m : ℝ) ^ r := by
  let γ := (A / (8 * C)) ^ r
  have hγ : 0 < γ := by dsimp [γ]; positivity
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (8 * C / A)
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt ((B + 1) / γ)
  refine ⟨max N₁ N₂ + 1, by omega, ?_⟩
  intro n hn m hnm
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hN₁n : (N₁ : ℝ) ≤ n := by exact_mod_cast (show N₁ ≤ n by omega)
  have hN₂n : (N₂ : ℝ) ≤ n := by exact_mod_cast (show N₂ ≤ n by omega)
  have hAn : 8 * C < A * n := by
    have hh := (div_lt_iff₀ hA).mp (hN₁.trans_le hN₁n)
    nlinarith
  have hBn : B < γ * n := by
    have hh := (div_lt_iff₀ hγ).mp (hN₂.trans_le hN₂n)
    nlinarith
  have hAm : 4 ≤ A * m := by
    have hh := mul_le_mul_of_nonneg_left hnm hA.le
    nlinarith
  have hbase : A / (8 * C) * n ≤ A / 4 * m := by
    apply (mul_le_mul_iff_left₀ (show 0 < 8 * C by positivity)).mp
    have hid : (A / (8 * C) * n) * (8 * C) = A * n := by field_simp
    rw [hid]
    have hh := mul_le_mul_of_nonneg_left hnm hA.le
    nlinarith
  have hp := pow_le_pow_left₀ (show 0 ≤ A / (8 * C) * n by positivity) hbase r
  rw [mul_pow, mul_pow] at hp
  have hnPow : 0 < (n : ℝ) ^ (r - 1) := by positivity
  have hstrict := mul_lt_mul_of_pos_right hBn hnPow
  have hpowEq : γ * n * (n : ℝ) ^ (r - 1) = γ * (n : ℝ) ^ r := by
    rw [mul_assoc, ← pow_succ', Nat.sub_add_cancel hr]
  rw [hpowEq] at hstrict
  exact ⟨hAm, hstrict.trans_le hp⟩

end DensityHS.Rainbow
