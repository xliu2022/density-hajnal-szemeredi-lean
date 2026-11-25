module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.LocallyConvex.WeakSpace

/-!
# Weak compactness and linear optimization in a real Hilbert space

Author and maintainer: Xizhi Liu.

Riesz representation makes the canonical map into the bidual surjective.
Banach–Alaoglu and equality of weak and norm closures for convex sets then give
attainment of continuous linear minima on closed bounded convex sets.
-/

@[expose] public section

namespace DensityHS.Analysis

open Set Topology Bornology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Real Hilbert spaces are reflexive, proved directly from Riesz representation. -/
theorem hilbert_biddual_surjective :
    Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E) := by
  intro F
  let R : E ≃ₗᵢ[ℝ] StrongDual ℝ E := InnerProductSpace.toDual ℝ E
  let g : StrongDual ℝ E := F.comp R.toContinuousLinearEquiv.toContinuousLinearMap
  let x : E := R.symm g
  refine ⟨x, ?_⟩
  ext φ
  let y : E := R.symm φ
  have hy : R y = φ := R.apply_symm_apply φ
  calc
    φ x = @inner ℝ E _ y x := by rw [← hy]; rfl
    _ = @inner ℝ E _ x y := real_inner_comm _ _
    _ = g y := InnerProductSpace.toDual_symm_apply
    _ = F (R y) := rfl
    _ = F φ := by rw [hy]

/-- The canonical map from the weak Hilbert space to its weak-star bidual is
also onto. -/
theorem hilbert_weak_biddual_surjective :
    Function.Surjective (NormedSpace.inclusionInDoubleDualWeak ℝ E) := by
  intro F
  obtain ⟨x, hx⟩ := hilbert_biddual_surjective (StrongDual.toWeakDual.symm F)
  refine ⟨toWeakSpace ℝ E x, ?_⟩
  apply StrongDual.toWeakDual.symm.injective
  ext φ
  change φ x = F φ
  simpa using congrArg (fun g => g φ) hx

/-- Closed bounded convex subsets of a Hilbert space are weakly compact. -/
theorem isCompact_weak_image {s : Set E} (hs : IsClosed s) (hconv : Convex ℝ s)
    (hbound : IsBounded s) : IsCompact (toWeakSpace ℝ E '' s) := by
  have hclosure : closure (toWeakSpace ℝ E '' s) = toWeakSpace ℝ E '' s := by
    rw [← hconv.toWeakSpace_closure ℝ, hs.closure_eq]
  have hb : IsBounded ((toWeakSpace ℝ E) ⁻¹' (toWeakSpace ℝ E '' s)) := by
    convert hbound using 1
    ext x
    simp
  have hcompact := NormedSpace.isCompact_closure_of_isBounded ℝ E
    (toWeakSpace ℝ E '' s) hb (fun F _ => hilbert_weak_biddual_surjective F)
  rwa [hclosure] at hcompact

/-- Continuous linear functionals attain their minima on nonempty closed
bounded convex subsets of a Hilbert space. -/
theorem exists_linear_minimum {s : Set E} (hs : IsClosed s) (hconv : Convex ℝ s)
    (hbound : IsBounded s) (hne : s.Nonempty) (f : StrongDual ℝ E) :
    ∃ x ∈ s, ∀ y ∈ s, f x ≤ f y := by
  let fw : WeakSpace ℝ E → ℝ := fun y => f ((toWeakSpace ℝ E).symm y)
  have hcont : Continuous fw := WeakBilin.eval_continuous (topDualPairing ℝ E).flip f
  obtain ⟨y, ⟨x, hx, rfl⟩, hmin⟩ := (isCompact_weak_image hs hconv hbound).exists_isMinOn
    (hne.image (toWeakSpace ℝ E)) hcont.continuousOn
  refine ⟨x, hx, ?_⟩
  intro z hz
  exact hmin ⟨z, hz, rfl⟩

end DensityHS.Analysis
