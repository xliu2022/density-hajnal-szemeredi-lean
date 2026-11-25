module

public import DensityHS.Graphon.EndpointEquality
public import DensityHS.Constructions.OrdinaryAlignment
public import DensityHS.Constructions.FinalAlignment
public import DensityHS.Constructions.CompactFamilies
public import DensityHS.Basic.PhaseActive

/-!
# Boundary equality models belong to the actual active family

Author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS.Constructions

open MeasureTheory Set Graphon

theorem kernel_zero_endpoint_mem_active {r : ℕ} (hr : 3 ≤ r) (W : Kernel ℝ)
    (htiling : tilingNumber r W unitMeasure ≤ 0)
    (he : density unitMeasure W = Phi r 0) :
    Vendor.GraphonSpace.mk (W.toVendorGraphon unitMeasure) ∈ activeFamily r 0 := by
  letI : IsProbabilityMeasure (volume.restrict (Ioc (0 : ℝ) 1)) := by
    change IsProbabilityMeasure unitMeasure
    infer_instance
  obtain ⟨P⟩ := zero_endpoint_classification (by omega : 2 ≤ r) volume
    (D := Ioc 0 1) measurableSet_Ioc W htiling he
  have hx : (0 : ℝ) ∈ Icc 0 (1 / (r : ℝ)) := ⟨le_rfl, by positivity⟩
  have hmodel := P.graphon_eq (by omega : 1 < r) hx
  let z : Fin (r - 1) → ℝ := fun _ => 1 / ((r - 1 : ℕ) : ℝ)
  have hs : (r - 1 : ℕ) ≠ 0 := by omega
  have hz : IsProbabilityWeight z := by
    refine ⟨fun _ => by dsimp [z]; positivity, ?_⟩
    simp [z, hs]
  apply (mem_activeFamily_iff hr).mpr
  refine ⟨.ordinary ⟨0, by omega⟩, z, hx, hz, trivial, ?_, ?_⟩
  · exact Phi_eq_B_one_before_A hr le_rfl (AStart_pos hr).le
  · exact hmodel

theorem kernel_full_endpoint_mem_active {r : ℕ} (hr : 3 ≤ r) (W : Kernel ℝ)
    (he : density unitMeasure W = Phi r (1 / (r : ℝ))) :
    Vendor.GraphonSpace.mk (W.toVendorGraphon unitMeasure) ∈
      activeFamily r (1 / (r : ℝ)) := by
  obtain ⟨P⟩ := full_endpoint_classification (by omega : 2 ≤ r) W unitMeasure he
  have hxR := RDomain_of_after_crossing hr (RCrossing_lt_right_endpoint hr).le le_rfl
  obtain ⟨z, hz, hmodel⟩ := P.exists_graphon_eq (by omega : 2 ≤ r) hxR
  apply (mem_activeFamily_iff hr).mpr
  refine ⟨.final, z, ⟨by positivity, le_rfl⟩, hz, hxR, ?_, hmodel⟩
  exact Phi_eq_R_after_crossing hr (RCrossing_lt_right_endpoint hr).le le_rfl

end DensityHS.Constructions
