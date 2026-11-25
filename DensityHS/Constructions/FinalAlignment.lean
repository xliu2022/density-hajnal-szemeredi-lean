module

public import DensityHS.Graphon.FinalPartition
public import DensityHS.Constructions.Alignment

/-!
# Canonical simplex representative of the final equality model

Author and maintainer: Xizhi Liu.

The normalized zero-cell masses give the simplex parameter when ell>0.
At ell=0 all independent cells are null, and any simplex vector gives the
same complete kernel; a uniform vector is chosen explicitly.
-/

@[expose] public section

namespace DensityHS.Graphon.FinalPartition

open MeasureTheory Set DensityHS.Constructions

theorem exists_graphon_eq {r : ℕ} (hr : 2 ≤ r) {x : ℝ} (hx : RDomain r x)
    {W : Kernel ℝ} (P : FinalPartition r x W unitMeasure) :
    ∃ z : Fin (r - 1) → ℝ, IsProbabilityWeight z ∧
      Vendor.GraphonSpace.mk (W.toVendorGraphon unitMeasure) = finalGraphon r x z := by
  classical
  letI : MeasurableSpace (Option (Fin (r - 1) × Bool)) := ⊤
  have hlabel : Measurable P.label := by
    apply measurable_to_countable'
    intro i
    exact P.measurable_fiber i
  let L := 1 - (r : ℝ) * x
  have hrp : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hL : 0 ≤ L := by
    have h := (le_div_iff₀ hrp).mp hx.2
    dsimp [L]
    nlinarith
  by_cases hL0 : L = 0
  · let z : Fin (r - 1) → ℝ := fun _ => 1 / ((r - 1 : ℕ) : ℝ)
    have hs : (r - 1 : ℕ) ≠ 0 := by omega
    have hz : IsProbabilityWeight z := by
      refine ⟨fun _ => by dsimp [z]; positivity, ?_⟩
      simp [z, hs]
    refine ⟨z, hz, ?_⟩
    apply (finalTemplate (r - 1)).graphon_eq_of_label W P.label hlabel
      (finalWeight_admissible hr hx hz) _ P.realization
    intro i
    rcases i with _ | ⟨j, b⟩
    · exact P.clique_mass
    · have hpart := P.part_mass j
      change unitMeasure.real {u | P.label u = some (j, false)} +
        unitMeasure.real {u | P.label u = some (j, true)} = L at hpart
      rw [hL0] at hpart
      have hnonnegY : 0 ≤ unitMeasure.real {u | P.label u = some (j, false)} :=
        measureReal_nonneg
      have hnonnegZ : 0 ≤ unitMeasure.real {u | P.label u = some (j, true)} :=
        measureReal_nonneg
      cases b <;>
        change unitMeasure.real _ = if _ then _ * L else (1 - _) * L <;>
        simp only [hL0, mul_zero, ite_self] <;> linarith
  · have hLpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hL0)
    let z : Fin (r - 1) → ℝ := fun j => unitMeasure.real {u | P.label u = some (j, true)} / L
    have hz : IsProbabilityWeight z := by
      refine ⟨fun _ => div_nonneg measureReal_nonneg hL, ?_⟩
      change (∑ j, unitMeasure.real {u | P.label u = some (j, true)} / L) = 1
      rw [← Finset.sum_div, P.zero_mass]
      change L / L = 1
      exact div_self hL0
    refine ⟨z, hz, ?_⟩
    apply (finalTemplate (r - 1)).graphon_eq_of_label W P.label hlabel
      (finalWeight_admissible hr hx hz) _ P.realization
    intro i
    rcases i with _ | ⟨j, b⟩
    · exact P.clique_mass
    · cases b
      · have hpart := P.part_mass j
        change unitMeasure.real {u | P.label u = some (j, false)} +
          unitMeasure.real {u | P.label u = some (j, true)} = L at hpart
        change unitMeasure.real _ = (1 - unitMeasure.real {u | P.label u = some (j, true)} / L) * L
        rw [sub_mul, one_mul, div_mul_cancel₀ _ hL0]
        linarith
      · change unitMeasure.real _ = (unitMeasure.real {u | P.label u = some (j, true)} / L) * L
        exact (div_mul_cancel₀ _ hL0).symm

end DensityHS.Graphon.FinalPartition

