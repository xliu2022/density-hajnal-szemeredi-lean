module

public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Tactic

/-!
# Null polarization on a constrained subspace

Author and maintainer: Xizhi Liu.

The null-polarization lemma from the equality analysis holds on every real
inner product space. No finite-dimensionality or spectral theorem is needed.
-/

public section

namespace DensityHS.Analysis

/-- A quadratic polynomial nonpositive everywhere and vanishing at zero has
zero linear coefficient. -/
theorem linear_coefficient_eq_zero {a b : ℝ}
    (h : ∀ t : ℝ, a * t + b * t ^ 2 ≤ 0) : a = 0 := by
  have hmax : IsLocalMax (fun t : ℝ => a * t + b * t ^ 2) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    simpa using h t
  have hd : HasDerivAt (fun t : ℝ => a * t + b * t ^ 2) a 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).const_mul a).add
      (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul b) using 1 <;> simp [Pi.add_def]
  exact hmax.hasDerivAt_eq_zero hd

/-- A null vector for a nonpositive symmetric quadratic form on a subspace
is mapped into its orthogonal complement. -/
theorem null_polarization {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (T : E →ₗ[ℝ] E) (H : Submodule ℝ E)
    (hT : ∀ u v, inner ℝ u (T v) = inner ℝ (T u) v)
    (hneg : ∀ h ∈ H, inner ℝ h (T h) ≤ 0)
    {h₀ : E} (hh₀ : h₀ ∈ H) (hzero : inner ℝ h₀ (T h₀) = 0) :
    T h₀ ∈ Hᗮ := by
  rw [Submodule.mem_orthogonal]
  intro g hg
  have hsym : inner ℝ h₀ (T g) = inner ℝ g (T h₀) := by
    rw [hT, real_inner_comm]
  have hp : ∀ t : ℝ,
      (2 * inner ℝ g (T h₀)) * t + inner ℝ g (T g) * t ^ 2 ≤ 0 := by
    intro t
    have h := hneg (h₀ + t • g) (H.add_mem hh₀ (H.smul_mem t hg))
    simp only [map_add, map_smul, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, hzero, hsym] at h
    nlinarith only [h]
  have h := linear_coefficient_eq_zero hp
  linarith

/-- Reversing the sign gives the corresponding statement for positive forms. -/
theorem null_polarization_nonneg {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (T : E →ₗ[ℝ] E) (H : Submodule ℝ E)
    (hT : ∀ u v, inner ℝ u (T v) = inner ℝ (T u) v)
    (hpos : ∀ h ∈ H, 0 ≤ inner ℝ h (T h))
    {h₀ : E} (hh₀ : h₀ ∈ H) (hzero : inner ℝ h₀ (T h₀) = 0) :
    T h₀ ∈ Hᗮ := by
  have hn : (-T) h₀ ∈ Hᗮ := null_polarization (-T) H
    (by intro u v; simpa using congrArg Neg.neg (hT u v))
    (by intro h hh; simpa using neg_nonpos.mpr (hpos h hh)) hh₀
    (by simpa using congrArg Neg.neg hzero)
  simpa using (Hᗮ).neg_mem hn

end DensityHS.Analysis
