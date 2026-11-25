module

public import DensityHS.Basic.Envelope

/-!
# Exact algebra in the rigid-cover cases

The stationarity substitutions and positive-semidefinite certificate in
Proposition 3.11 of *The density Hajnal–Szemerédi theorem*.
All hypotheses here are explicit real algebraic hypotheses; deriving them
from the graph and its extreme cover is a separate combinatorial step.

Formalization author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS

noncomputable def rigidQ11 (r j κ : ℝ) : ℝ :=
  (j ^ 2 * (r + κ) + 2 * j * κ * (r + κ) + κ ^ 2 * (r - 1)) / j ^ 2

noncomputable def rigidQ12 (r j h κ : ℝ) : ℝ :=
  (j * r * (j + κ) - h * κ * (j - 1)) / (j * (j + h))

noncomputable def rigidQ22 (r j h : ℝ) : ℝ :=
  (j ^ 2 * r + h * j ^ 2 + h ^ 2 * (j - 1)) / (j + h) ^ 2

noncomputable def rigidEll (j h κ u v : ℝ) : ℝ := h / (j + h) * v - κ / j * u

noncomputable def rigidDeficiency (r j h κ u v : ℝ) : ℝ :=
  (r + κ) * u ^ 2 + 2 * r * u * v + (r + j * h / (j + h)) * v ^ 2

/-- The exact determinant factorization from the paper. -/
theorem rigid_determinant_identity {r j h κ : ℝ} (hj : j ≠ 0) (hN : j + h ≠ 0) :
    rigidQ11 r j κ * rigidQ22 r j h - (rigidQ12 r j h κ) ^ 2 =
      (h * j * κ + h * j * r + h * κ * r + j * κ * r) /
          (j ^ 2 * (j + h) ^ 2) *
        (h * (j - 1) * (j + κ) + j * (j ^ 2 + κ * (2 * j - 1))) := by
  unfold rigidQ11 rigidQ12 rigidQ22
  field_simp
  <;> ring

theorem rigidQ11_pos {r j κ : ℝ} (hr : 1 < r) (hj : 1 ≤ j) (hκ : 0 ≤ κ) :
    0 < rigidQ11 r j κ := by
  have hjp : 0 < j := by linarith
  have hrκ : 0 < r + κ := by linarith
  have hmain : 0 < j ^ 2 * (r + κ) := mul_pos (sq_pos_of_pos hjp) hrκ
  have hsecond : 0 ≤ 2 * j * κ * (r + κ) := by positivity
  have hthird : 0 ≤ κ ^ 2 * (r - 1) := mul_nonneg (sq_nonneg _) (by linarith)
  unfold rigidQ11
  apply div_pos _ (sq_pos_of_pos hjp)
  linarith

theorem rigidQ22_pos {r j h : ℝ} (hr : 1 < r) (hj : 1 ≤ j) (hh : 0 ≤ h) :
    0 < rigidQ22 r j h := by
  have hjp : 0 < j := by linarith
  have hNp : 0 < j + h := by linarith
  have hmain : 0 < j ^ 2 * r := mul_pos (sq_pos_of_pos hjp) (by linarith)
  have hsecond : 0 ≤ h * j ^ 2 := mul_nonneg hh (sq_nonneg _)
  have hthird : 0 ≤ h ^ 2 * (j - 1) := mul_nonneg (sq_nonneg _) (by linarith)
  unfold rigidQ22
  apply div_pos _ (sq_pos_of_pos hNp)
  linarith

theorem rigid_determinant_nonneg {r j h κ : ℝ}
    (hr : 1 < r) (hj : 1 ≤ j) (hh : 0 ≤ h) (hκ : 0 ≤ κ) :
    0 ≤ rigidQ11 r j κ * rigidQ22 r j h - (rigidQ12 r j h κ) ^ 2 := by
  have hjp : 0 < j := by linarith
  have hNp : 0 < j + h := by linarith
  rw [rigid_determinant_identity (ne_of_gt hjp) (ne_of_gt hNp)]
  have hr0 : 0 ≤ r := by linarith
  have hj0 : 0 ≤ j := hjp.le
  have hjm : 0 ≤ j - 1 := by linarith
  have hj2m : 0 ≤ 2 * j - 1 := by linarith
  positivity

/-- A two-variable quadratic certificate proved by completing a square. -/
theorem quadratic_form_nonneg_of_determinant {a b c u v : ℝ}
    (ha : 0 < a) (hdet : 0 ≤ a * c - b ^ 2) :
    0 ≤ a * u ^ 2 + 2 * b * u * v + c * v ^ 2 := by
  have hp := mul_nonneg hdet (sq_nonneg v)
  have hs := sq_nonneg (a * u + b * v)
  have hid : a * (a * u ^ 2 + 2 * b * u * v + c * v ^ 2) =
      (a * u + b * v) ^ 2 + (a * c - b ^ 2) * v ^ 2 := by ring
  exact nonneg_of_mul_nonneg_right (by linarith) ha

theorem rigid_quadratic_nonneg {r j h κ u v : ℝ}
    (hr : 1 < r) (hj : 1 ≤ j) (hh : 0 ≤ h) (hκ : 0 ≤ κ) :
    0 ≤ rigidQ11 r j κ * u ^ 2 + 2 * rigidQ12 r j h κ * u * v +
      rigidQ22 r j h * v ^ 2 :=
  quadratic_form_nonneg_of_determinant (rigidQ11_pos hr hj hκ)
    (rigid_determinant_nonneg hr hj hh hκ)

/-- Homogenization of the target deficiency using the total-mass equation. -/
theorem rigid_deficiency_identity {r j h κ u v : ℝ} (hj : j ≠ 0) (hN : j + h ≠ 0) :
    rigidDeficiency r j h κ u v -
        2 * rigidEll j h κ u v * (r * v + (r + κ) * u) +
        (r - 1) * (rigidEll j h κ u v) ^ 2 =
      rigidQ11 r j κ * u ^ 2 + 2 * rigidQ12 r j h κ * u * v +
        rigidQ22 r j h * v ^ 2 := by
  unfold rigidDeficiency rigidEll rigidQ11 rigidQ12 rigidQ22
  field_simp
  <;> ring

/-- The central deficiency bound; no sign hypotheses on `u,v` are needed for
the positive-semidefinite step itself. -/
theorem rigid_deficiency_bound {r j h κ u v : ℝ}
    (hr : 1 < r) (hj : 1 ≤ j) (hh : 0 ≤ h) (hκ : 0 ≤ κ)
    (hnorm : r * v + (r + κ) * u = 1) :
    2 * rigidEll j h κ u v - (r - 1) * (rigidEll j h κ u v) ^ 2 ≤
      rigidDeficiency r j h κ u v := by
  have hjp : 0 < j := by linarith
  have hNp : 0 < j + h := by linarith
  have hid := rigid_deficiency_identity (r := r) (κ := κ) (u := u) (v := v)
    (ne_of_gt hjp) (ne_of_gt hNp)
  rw [hnorm] at hid
  have hp := rigid_quadratic_nonneg (u := u) (v := v) hr hj hh hκ
  linarith

/-- The two stationarity comparisons determine the module weights. -/
theorem rigid_weights_from_stationarity {r j h w d u L μ v : ℝ}
    (hr : r ≠ 0) (hj : j ≠ 0) (hN : j + h ≠ 0)
    (hA : μ / r = (j + h) * w)
    (hhigh : (j + h + 1) * w + d - u = μ * (j + 1) / (r * j))
    (hlow : L = d + w) (hv : v = (j + h) * w / j) :
    w = j / (j + h) * v ∧ d = u + h / (j + h) * v ∧ L = u + v := by
  have hw : w = j / (j + h) * v := by rw [hv]; field_simp
  have hμ : μ = r * ((j + h) * w) := by
    have h := (div_eq_iff hr).mp hA
    nlinarith
  have hd : d = u + h / (j + h) * v := by
    rw [hμ] at hhigh
    have heq : r * ((j + h) * w) * (j + 1) / (r * j) =
        (j + h) * w * (j + 1) / j := by field_simp
    rw [heq] at hhigh
    rw [hv]
    have hden : h / (j + h) * ((j + h) * w / j) = h * w / j := by field_simp
    rw [hden]
    have heq' : (j + h) * w * (j + 1) / j = (j + h + 1) * w + h * w / j := by
      field_simp
      <;> ring
    rw [heq'] at hhigh
    linarith
  refine ⟨hw, hd, ?_⟩
  rw [hlow, hd, hw]
  field_simp
  <;> ring

theorem rigid_total_mass_identity {r j h κ u v : ℝ} (hN : j + h ≠ 0) :
    (j + h + 1) * (j / (j + h) * v) + (r - 1 - j) * (u + v) +
      (j + κ) * u + (u + h / (j + h) * v) = r * v + (r + κ) * u := by
  field_simp
  <;> ring

theorem rigid_cover_cost_identity {r j h κ u v : ℝ}
    (hr : r ≠ 0) (hj : j ≠ 0) (hN : j + h ≠ 0) :
    r * v + (r + κ) * u -
      r * (((j + h + 1) * (j / (j + h) * v) + (r - 1 - j) * (u + v)) / r +
        (j + κ) * ((j + 1) / (r * j)) * u) = rigidEll j h κ u v := by
  unfold rigidEll
  field_simp
  <;> ring

theorem rigid_diagonal_deficiency_identity {r j h κ u v : ℝ} (hN : j + h ≠ 0) :
    (j + h + 1) * (j / (j + h) * v) ^ 2 + (r - 1 - j) * (u + v) ^ 2 +
      (j + κ) * u ^ 2 + (u + h / (j + h) * v) ^ 2 +
      2 * (j + h + 1) * (j / (j + h) * v) * (u + h / (j + h) * v) =
        rigidDeficiency r j h κ u v := by
  unfold rigidDeficiency
  field_simp
  <;> ring

/-- Translation of the positive-semidefinite certificate to the `R` branch. -/
theorem rigid_edge_bound {r : ℕ} (hr : 3 ≤ r) {j h κ u v x e : ℝ}
    (hj : 1 ≤ j) (hh : 0 ≤ h) (hκ : 0 ≤ κ)
    (hnorm : (r : ℝ) * v + ((r : ℝ) + κ) * u = 1)
    (hell : 1 - (r : ℝ) * x = rigidEll j h κ u v)
    (hdef : 1 - 2 * e = rigidDeficiency r j h κ u v) : e ≤ R r x := by
  have hr1 : (1 : ℝ) < r := by exact_mod_cast (by omega : 1 < r)
  have hb := rigid_deficiency_bound hr1 hj hh hκ hnorm
  rw [← hell, ← hdef] at hb
  unfold R
  linarith

/-- Positivity of the high-atom weight puts the parameter in the actual
admissible domain of `R`; the domain restriction is not dropped. -/
theorem rigid_parameter_in_RDomain {r : ℕ} (hr : 3 ≤ r) {j h κ u v x : ℝ}
    (hj : 1 ≤ j) (hh : 0 ≤ h) (hκ : 0 ≤ κ) (hu : 0 < u) (hv : 0 ≤ v)
    (hnorm : (r : ℝ) * v + ((r : ℝ) + κ) * u = 1)
    (hell : 1 - (r : ℝ) * x = rigidEll j h κ u v)
    (hx1 : x ≤ 1 / (r : ℝ)) : RDomain r x := by
  have hr2 : (2 : ℝ) < r := by exact_mod_cast (by omega : 2 < r)
  have hrp : (0 : ℝ) < r := by linarith
  have hjp : 0 < j := by linarith
  have hNp : 0 < j + h := by linarith
  have hcoef : h / (j + h) ≤ 1 := (div_le_iff₀ hNp).mpr (by linarith)
  have hterm : 0 ≤ κ / j * u := mul_nonneg (div_nonneg hκ hjp.le) hu.le
  have hellv : rigidEll j h κ u v ≤ v := by
    unfold rigidEll
    have hp := mul_le_mul_of_nonneg_right hcoef hv
    linarith
  have hu' : 0 < ((r : ℝ) + κ) * u := mul_pos (by linarith) hu
  have hv1 : v < 1 / (r : ℝ) := (lt_div_iff₀ hrp).mpr (by nlinarith)
  have hrecip : 1 / (r : ℝ) ≤ 1 / ((r : ℝ) - 1) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  have hell1 : 1 - (r : ℝ) * x ≤ 1 / ((r : ℝ) - 1) := by
    rw [hell]
    exact hellv.trans (hv1.le.trans hrecip)
  refine ⟨?_, hx1⟩
  apply (div_le_iff₀ (mul_pos hrp (by linarith : 0 < (r : ℝ) - 1))).mpr
  have h := (le_div_iff₀ (by linarith : 0 < (r : ℝ) - 1)).mp hell1
  nlinarith

theorem rigid_edge_bound_Phi {r : ℕ} (hr : 3 ≤ r) {j h κ u v x e : ℝ}
    (hj : 1 ≤ j) (hh : 0 ≤ h) (hκ : 0 ≤ κ) (hu : 0 < u) (hv : 0 ≤ v)
    (hnorm : (r : ℝ) * v + ((r : ℝ) + κ) * u = 1)
    (hell : 1 - (r : ℝ) * x = rigidEll j h κ u v)
    (hdef : 1 - 2 * e = rigidDeficiency r j h κ u v)
    (hx1 : x ≤ 1 / (r : ℝ)) : e ≤ Phi r x :=
  (rigid_edge_bound hr hj hh hκ hnorm hell hdef).trans
    (R_le_Phi hr (rigid_parameter_in_RDomain hr hj hh hκ hu hv hnorm hell hx1))

/-- The first exceptional case: the two end masses contribute their full
square to the deficiency, and all remaining diagonal terms are nonnegative. -/
theorem two_end_edge_bound {r : ℕ} (hr : 3 ≤ r) {a b c x e diagonal : ℝ}
    (hnorm : a + b + c = 1) (hcost : x = b / ((r : ℝ) - 1))
    (hdiag : 0 ≤ diagonal)
    (hdef : 1 - 2 * e = a ^ 2 + c ^ 2 + 2 * a * c + diagonal) :
    e ≤ B r (r - 1) x := by
  have hr2 : (2 : ℝ) < r := by exact_mod_cast (by omega : 2 < r)
  have hden : (r : ℝ) - 1 ≠ 0 := by linarith
  have hx : ((r : ℝ) - 1) * x = b := by rw [hcost]; field_simp
  unfold B
  rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
  have hd : (r : ℝ) - ((r : ℝ) - 1) = 1 := by ring
  rw [hd, div_one, hx]
  have hac : 1 - b = a + c := by linarith
  rw [hac]
  nlinarith

theorem two_end_edge_bound_Phi {r : ℕ} (hr : 3 ≤ r) {a b c x e diagonal : ℝ}
    (hnorm : a + b + c = 1) (hcost : x = b / ((r : ℝ) - 1))
    (hdiag : 0 ≤ diagonal)
    (hdef : 1 - 2 * e = a ^ 2 + c ^ 2 + 2 * a * c + diagonal) : e ≤ Phi r x :=
  (two_end_edge_bound hr hnorm hcost hdiag hdef).trans
    (B_le_Phi hr (by omega) (by omega) x)

end DensityHS
