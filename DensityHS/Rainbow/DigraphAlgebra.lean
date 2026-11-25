module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

/-!
# The strict density gap from directed arc counting

Author and maintainer: Xizhi Liu.

The missing diagonal in the bound on single arcs gives a strict inequality,
including at the endpoint `ρ = 1`.
-/

@[expose] public section

namespace DensityHS

/-- The directed arc bound forces the double-edge graph above the critical
density.  The positive diagonal correction is retained throughout the proof. -/
theorem directed_arc_strict_density_gap {N m e ρ : ℝ}
    (hm : 0 < m) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hmass : ρ * N ≤ m)
    (harcs : m * (ρ * N - N + m) ≤ m * (m - 1) / 2 + m ^ 2 * e) :
    (3 * ρ - 2) / (2 * ρ) < e := by
  have hscaled := mul_le_mul_of_nonneg_left harcs (by positivity : 0 ≤ 2 * ρ)
  have hgap := mul_nonneg
    (mul_nonneg (sub_nonneg.mpr hρ1) (sub_nonneg.mpr hmass)) hm.le
  have hdiag : 0 < ρ * m := mul_pos hρ hm
  have hstrict : (3 * ρ - 2) * m ^ 2 < (2 * ρ * e) * m ^ 2 := by
    nlinarith
  have hcancel := (mul_lt_mul_iff_left₀ (sq_pos_of_pos hm)).mp hstrict
  apply (div_lt_iff₀ (by positivity : 0 < 2 * ρ)).mpr
  simpa only [mul_comm e (2 * ρ)] using hcancel

end DensityHS
