module

public import DensityHS.Constructions.FinalKernel

/-!
# Actual finite labelled model of the final graphon family

Author and maintainer: Xizhi Liu.

The label fibers are the clique cell and the Y/Z subdivisions of r-1
independent parts. The structure records the actual measurable kernel
identity and cell masses, not a fractional cover certificate.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory

structure FinalPartition {Ω : Type*} [MeasurableSpace Ω]
    (r : ℕ) (x : ℝ) (W : Kernel Ω) (μ : Measure Ω) where
  label : Ω → Option (Fin (r - 1) × Bool)
  measurable_fiber : ∀ i, MeasurableSet {z | label z = i}
  clique_mass : μ.real {z | label z = none} = 1 - (r - 1 : ℕ) * (1 - (r : ℝ) * x)
  part_mass : ∀ j, μ.real {z | label z = some (j, false)} +
    μ.real {z | label z = some (j, true)} = 1 - (r : ℝ) * x
  zero_mass : (∑ j, μ.real {z | label z = some (j, true)}) = 1 - (r : ℝ) * x
  realization : ∀ᵐ z : Ω × Ω ∂μ.prod μ,
    W z.1 z.2 = (Constructions.finalTemplate (r - 1)).entry (label z.1) (label z.2)

end DensityHS.Graphon

