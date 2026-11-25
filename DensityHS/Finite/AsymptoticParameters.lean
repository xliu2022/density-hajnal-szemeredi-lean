module

public import DensityHS.Basic.Envelope
public import DensityHS.Basic.Tilings
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Data.Fintype.Powerset

/-!
# Uniform parameters for the finite density upper bound

Author and maintainer: Xizhi Liu.

All choices depend only on the clique size and the requested density error.
The parameters separate the regularity tolerance, pair-density threshold,
and reserved proportion used when rounding a fractional reduced tiling.
-/

@[expose] public section

namespace DensityHS.Regularity

/-- Uniform continuity of the envelope on its full parameter interval. -/
theorem exists_Phi_uniform_radius {r : ℕ} (hr : 3 ≤ r) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Set.Icc 0 (1 / (r : ℝ)),
      ∀ y ∈ Set.Icc 0 (1 / (r : ℝ)), |x - y| < δ → |Phi r x - Phi r y| < ε := by
  have huc := IsCompact.uniformContinuousOn_of_continuous
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (1 / (r : ℝ)))) (continuousOn_Phi hr)
  obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy hxy
  simpa only [Real.dist_eq] using h x hx y hy (by simpa only [Real.dist_eq] using hxy)

/-- The three independent regularity parameters can always be chosen so that
both the edge loss and the transversal embedding condition hold. -/
theorem exists_regular_rounding_parameters {r : ℕ} (hr : 3 ≤ r)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ β d α : ℝ, 0 < β ∧ β < 1 ∧ β ≤ δ / 4 ∧ 0 < α ∧ α < d ∧
      d - α ≤ 1 ∧ α * r < β * (d - α) ^ (r - 1) ∧
      2 * α + 2 * d + ε / 4 < ε / 2 := by
  let β : ℝ := min (δ / 4) (1 / 2)
  let d : ℝ := min (ε / 16) (1 / 2)
  have hβ : 0 < β := lt_min (by positivity) (by norm_num)
  have hβ1 : β ≤ 1 / 2 := min_le_right _ _
  have hd : 0 < d := lt_min (by positivity) (by norm_num)
  have hd1 : d ≤ 1 / 2 := min_le_right _ _
  have hdε : d ≤ ε / 16 := min_le_left _ _
  have hrR : 0 < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hcap : 0 < min (d / 2) (min (ε / 16) (β * (d / 2) ^ (r - 1) / r)) :=
    lt_min (by positivity) (lt_min (by positivity) (by positivity))
  obtain ⟨α, hα, hαcap⟩ := exists_between hcap
  have hαd : α < d / 2 := hαcap.trans_le (min_le_left _ _)
  have hαε : α < ε / 16 := hαcap.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hαsmall : α < β * (d / 2) ^ (r - 1) / r :=
    hαcap.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hpow : (d / 2) ^ (r - 1) ≤ (d - α) ^ (r - 1) :=
    pow_le_pow_left₀ (by positivity) (by linarith) (r - 1)
  refine ⟨β, d, α, hβ, by linarith, min_le_left _ _, hα, by linarith,
    by linarith, ?_, by linarith⟩
  exact ((lt_div_iff₀ hrR).mp hαsmall).trans_le
    (mul_le_mul_of_nonneg_left hpow hβ.le)

/-- A fixed finite rounding error is uniformly negligible for large orders. -/
theorem exists_order_bound (l M : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ n₀ : ℕ, l ≤ n₀ ∧ 0 < n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      (2 : ℝ) ^ M / n ≤ δ / 4 := by
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (max (l : ℝ) (4 * (2 : ℝ) ^ M / δ))
  have hl : (l : ℝ) < n₀ := (le_max_left _ _).trans_lt hn₀
  have hpos : 0 < (n₀ : ℝ) := lt_of_le_of_lt (Nat.cast_nonneg l) hl
  refine ⟨n₀, by exact_mod_cast hl.le, by exact_mod_cast hpos, ?_⟩
  intro n hn
  have hnn : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := hpos.trans_le hnn
  apply (div_le_iff₀ hnpos).2
  have hbig : 4 * (2 : ℝ) ^ M / δ < n := (le_max_right _ _).trans_lt (hn₀.trans_le hnn)
  have hmul := (div_lt_iff₀ hδ).mp hbig
  linarith

/-- The number of clique coordinates is bounded by the number of all vertex
subsets, which is enough to make the rounding error uniform. -/
theorem card_cliqueFamily_le_two_pow {I : Type*} [Fintype I] [DecidableEq I]
    (r : ℕ) (H : SimpleGraph I) {M : ℕ} (hM : Fintype.card I ≤ M) :
    (cliqueFamily r H).card ≤ 2 ^ M := by
  calc
    (cliqueFamily r H).card ≤ Fintype.card (Finset I) := Finset.card_le_univ _
    _ = 2 ^ Fintype.card I := Fintype.card_finset
    _ ≤ 2 ^ M := Nat.pow_le_pow_right (by norm_num) hM

/-- The rounding inequality implies a small one-sided error in the normalized
fractional packing number; division by the reserve factor is unnecessary. -/
theorem fractional_gap_of_rounding {N k C β z δ : ℝ}
    (hN : 0 < N) (hβ : 0 ≤ β) (hβδ : β ≤ δ / 4) (hz : z ≤ 1)
    (hC : C / N ≤ δ / 4)
    (hround : (1 - β) * N * z ≤ k + C) : z ≤ k / N + δ / 2 := by
  have hnorm : (1 - β) * z ≤ (k + C) / N := by
    apply (le_div_iff₀ hN).2
    nlinarith only [hround]
  rw [add_div] at hnorm
  have hβz : β * z ≤ β := by simpa using mul_le_mul_of_nonneg_left hz hβ
  linarith

/-- A small one-sided excess in the parameter is sufficient for an envelope
upper bound, by monotonicity on the other side. -/
theorem Phi_le_of_one_sided_close {r : ℕ} (hr : 3 ≤ r) {ε δ x z : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ)
    (hmod : ∀ x ∈ Set.Icc 0 (1 / (r : ℝ)), ∀ y ∈ Set.Icc 0 (1 / (r : ℝ)),
      |x - y| < δ → |Phi r x - Phi r y| < ε)
    (hx : x ∈ Set.Icc 0 (1 / (r : ℝ))) (hz : z ∈ Set.Icc 0 (1 / (r : ℝ)))
    (hgap : z ≤ x + δ / 2) : Phi r z ≤ Phi r x + ε := by
  by_cases hzx : z ≤ x
  · exact (Phi_monotoneOn hr hz hx hzx).trans (by linarith)
  · have hzx' : 0 ≤ z - x := by linarith
    have hdist : |z - x| < δ := by rw [abs_of_nonneg hzx']; linarith
    have h := (abs_lt.mp (hmod z hz x hx hdist)).2
    linarith

end DensityHS.Regularity
