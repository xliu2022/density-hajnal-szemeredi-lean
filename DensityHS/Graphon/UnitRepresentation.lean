module

public import DensityHS.Graphon.Pullback
public import DensityHS.Constructions.IntervalKernel

/-!
# Unit-interval representation of arbitrary standard atomless graphons

Author and maintainer: Xizhi Liu.

Only the standard-Borel, probability, and null-singleton assumptions are
needed. The proved mod-zero measure isomorphism upgrades to an everywhere
measure-preserving measurable equivalence; the required null reservoirs
are constructed by the imported theorem, not assumed here. Pulling back a
kernel therefore preserves both its actual fractional clique-tiling number
and its edge density.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set Constructions

variable {Ω Λ : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]

/-- Density is preserved by a measure-preserving map between probability
spaces, whether or not the map is invertible. -/
theorem density_comap (W : Kernel Λ) {μ : Measure Ω} {ν : Measure Λ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {φ : Ω → Λ} (hφ : MeasurePreserving φ μ ν) :
    density μ (W.comap φ hφ.measurable) = density ν W := by
  rw [density_eq_prod_integral, density_eq_prod_integral]
  apply congrArg (fun a : ℝ => a / 2)
  have h := integral_comap_measurable (hφ.prod hφ) W.measurable_uncurry
  exact h

/-- Every standard atomless probability space is measure-preservingly
measurably equivalent to the fixed real unit probability space. -/
theorem exists_unit_measurePreservingEquiv (μ : Measure Ω)
    [StandardBorelSpace Ω] [IsProbabilityMeasure μ] [NullSingletonClass μ] :
    ∃ e : ℝ ≃ᵐ Ω, MeasurePreserving e unitMeasure μ := by
  have hinterval : (volume : Measure ℝ).restrict (Icc 0 1) = unitMeasure :=
    (restrict_Ioc_eq_restrict_Icc (μ := (volume : Measure ℝ))).symm
  obtain ⟨e⟩ :=
    Vendor.Graphon.MeasureIso.atomless_standardBorel_mod0MeasureIso_unitInterval Ω μ
  have e' : Vendor.Graphon.MeasureIso.Mod0MeasureIso Ω ℝ μ unitMeasure := by
    simpa only [hinterval] using e
  obtain ⟨φ, hφ, _, _⟩ := e'.toMeasurableEquiv
  exact ⟨φ.symm, hφ.symm φ⟩

/-- An actual unit-interval representative, with a pointwise pullback
identity and exact density and genuine fractional-tiling invariants. -/
theorem Kernel.exists_unit_representation (W : Kernel Ω) (μ : Measure Ω)
    [StandardBorelSpace Ω] [IsProbabilityMeasure μ] [NullSingletonClass μ] :
    ∃ U : Kernel ℝ, ∃ e : ℝ ≃ᵐ Ω,
      MeasurePreserving e unitMeasure μ ∧
      (∀ u v, U u v = W (e u) (e v)) ∧
      density unitMeasure U = density μ W ∧
      (∀ r : ℕ, 0 < r → tilingNumber r U unitMeasure = tilingNumber r W μ) := by
  obtain ⟨e, he⟩ := exists_unit_measurePreservingEquiv μ
  refine ⟨W.comap e he.measurable, e, he, fun _ _ => rfl, density_comap W he, ?_⟩
  intro r hr
  exact tilingNumber_comap_equiv hr W e he

/-- The numerical form of unit normalization, simultaneously for every
positive clique order. -/
theorem Kernel.exists_unit_invariants (W : Kernel Ω) (μ : Measure Ω)
    [StandardBorelSpace Ω] [IsProbabilityMeasure μ] [NullSingletonClass μ] :
    ∃ U : Kernel ℝ, density unitMeasure U = density μ W ∧
      (∀ r : ℕ, 0 < r → tilingNumber r U unitMeasure = tilingNumber r W μ) := by
  obtain ⟨U, _, _, _, hd, ht⟩ := W.exists_unit_representation μ
  exact ⟨U, hd, ht⟩

end DensityHS.Graphon
