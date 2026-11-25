module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.Tactic

/-!
# Density of bounded tangent vectors

Author and maintainer: Xizhi Liu.

Bounded L² functions remain dense after imposing finitely many orthogonality
constraints against bounded L² functions. Continuous quadratic inequalities
therefore extend from the bounded tangent vectors to the full tangent space.
-/

@[expose] public section

namespace DensityHS.Analysis

open MeasureTheory Set
open scoped ENNReal

/-- A dense linear subspace remains dense in the orthogonal complement of a
finite-dimensional subspace which it contains. -/
theorem closure_inter_orthogonal {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (B V : Submodule ℝ E) [FiniteDimensional ℝ V]
    (hB : Dense (B : Set E)) (hVB : V ≤ B) :
    closure ((B : Set E) ∩ (Vᗮ : Set E)) = (Vᗮ : Set E) := by
  apply Set.Subset.antisymm
  · exact closure_minimal (fun _ hx => hx.2) V.isClosed_orthogonal
  · intro x hx
    let f : E → E := fun y => y - V.starProjection y
    have hf : Continuous f := continuous_id.sub V.starProjection.continuous
    have himage : f '' (B : Set E) ⊆ (B : Set E) ∩ (Vᗮ : Set E) := by
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨B.sub_mem hy (hVB (V.orthogonalProjectionOnto y).property),
        V.sub_starProjection_mem_orthogonal y⟩
    have hfix : f x = x := by
      have hp : V.orthogonalProjectionOnto x = 0 :=
        V.orthogonalProjectionOnto_eq_zero_iff.mpr hx
      dsimp [f]
      rw [Submodule.starProjection_apply, hp]
      simp
    have hm := mem_closure_image hf.continuousAt (hB x)
    rw [hfix] at hm
    exact closure_mono himage hm

variable {Ω : Type*} [MeasurableSpace Ω]

/-- L² classes with an essentially bounded representative form a real
submodule. The bound need not be fixed across the submodule. -/
noncomputable def boundedL2 (μ : Measure Ω) : Submodule ℝ (Lp ℝ 2 μ) where
  carrier := {f | ∃ C : ℝ, ∀ᵐ x ∂μ, ‖f x‖ ≤ C}
  zero_mem' := by
    refine ⟨0, ?_⟩
    filter_upwards [Lp.coeFn_zero ℝ 2 μ] with x hx
    change (0 : Lp ℝ 2 μ) x = 0 at hx
    rw [hx]
    simp
  add_mem' := by
    rintro f g ⟨C, hC⟩ ⟨D, hD⟩
    refine ⟨C+D, ?_⟩
    filter_upwards [hC, hD, Lp.coeFn_add f g] with x hx hy hxy
    rw [hxy, Pi.add_apply]
    exact (norm_add_le _ _).trans (add_le_add hx hy)
  smul_mem' := by
    rintro a f ⟨C, hC⟩
    refine ⟨‖a‖*C, ?_⟩
    filter_upwards [hC, Lp.coeFn_smul a f] with x hx hax
    rw [hax, Pi.smul_apply, norm_smul]
    exact mul_le_mul_of_nonneg_left hx (norm_nonneg a)

/-- The density is witnessed by the actual dense subspace of simple functions. -/
theorem boundedL2_dense (μ : Measure Ω) : Dense (boundedL2 μ : Set (Lp ℝ 2 μ)) := by
  apply (Lp.simpleFunc.dense (E := ℝ) (μ := μ) (by norm_num : (2:ℝ≥0∞) ≠ ∞)).mono
  intro f hf
  let g : Lp.simpleFunc ℝ 2 μ := ⟨f, hf⟩
  obtain ⟨C, hC⟩ := (Lp.simpleFunc.toSimpleFunc g).exists_forall_norm_le
  refine ⟨C, ?_⟩
  filter_upwards [Lp.simpleFunc.toSimpleFunc_eq_toFun g] with x hx
  rw [← hx]
  exact hC x

/-- The bounded-tangent-density lemma for a finite-dimensional space of
bounded constraints. -/
theorem bounded_tangent_density (μ : Measure Ω)
    (V : Submodule ℝ (Lp ℝ 2 μ)) [FiniteDimensional ℝ V]
    (hV : V ≤ boundedL2 μ) :
    closure ((boundedL2 μ : Set (Lp ℝ 2 μ)) ∩ (Vᗮ : Set (Lp ℝ 2 μ))) =
      (Vᗮ : Set (Lp ℝ 2 μ)) :=
  closure_inter_orthogonal (boundedL2 μ) V (boundedL2_dense μ) hV

/-- Explicitly, finitely many bounded constraint functions generate such a
finite-dimensional space. -/
theorem bounded_tangent_density_fin (μ : Measure Ω) {ι : Type*} [Finite ι]
    (φ : ι → Lp ℝ 2 μ) (hφ : ∀ i, φ i ∈ boundedL2 μ) :
    closure ((boundedL2 μ : Set (Lp ℝ 2 μ)) ∩
      ((Submodule.span ℝ (Set.range φ))ᗮ : Set (Lp ℝ 2 μ))) =
      ((Submodule.span ℝ (Set.range φ))ᗮ : Set (Lp ℝ 2 μ)) := by
  letI : FiniteDimensional ℝ (Submodule.span ℝ (Set.range φ)) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range φ)
  apply bounded_tangent_density
  exact Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hφ i)

/-- Every continuous scalar inequality valid on bounded tangent vectors
extends to all tangent vectors; this includes the quadratic forms used in
the equality proof. -/
theorem continuous_inequality_on_tangent (μ : Measure Ω)
    (V : Submodule ℝ (Lp ℝ 2 μ)) [FiniteDimensional ℝ V]
    (hV : V ≤ boundedL2 μ) {Q : Lp ℝ 2 μ → ℝ} (hQ : Continuous Q)
    (hbound : ∀ h ∈ boundedL2 μ, h ∈ Vᗮ → Q h ≤ 0) :
    ∀ h ∈ Vᗮ, Q h ≤ 0 := by
  have hc : closure ((boundedL2 μ : Set (Lp ℝ 2 μ)) ∩ (Vᗮ : Set (Lp ℝ 2 μ))) ⊆
      {h | Q h ≤ 0} :=
    closure_minimal (fun h hh => hbound h hh.1 hh.2) (isClosed_le hQ continuous_const)
  rw [bounded_tangent_density μ V hV] at hc
  exact hc

end DensityHS.Analysis
