module

public import DensityHS.Basic.PhaseCases
public import DensityHS.Graphon.TransitionEquality
public import DensityHS.Graphon.ClassificationBridge
public import DensityHS.Graphon.ClassificationConverse
public import DensityHS.Constructions.ExceptionalEqualityMembership

/-!
# Complete equality classification

Author and maintainer: Xizhi Liu.

All parameters of the closed admissible interval are covered, including
both endpoints, every first-order transition, and the tangent A/B meeting.
Every extremal kernel is identified with an actual active canonical model
in the cut-metric quotient. All variational, structural, uncrossing, and
strict-recursion inputs are supplied by proved theorems.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set ProbabilityTheory Constructions

theorem kernel_equality_classification {r : ℕ} (hr : 3 ≤ r) {x : ℝ}
    (hx : x ∈ Icc 0 (1 / (r : ℝ))) (W : Kernel ℝ)
    (htiling : tilingNumber r W unitMeasure ≤ x)
    (he : density unitMeasure W = Phi r x) :
    Vendor.GraphonSpace.mk (W.toVendorGraphon unitMeasure) ∈ activeFamily r x := by
  have hcond : cond (volume : Measure ℝ) (Ioc 0 1) = unitMeasure := by
    simp [ProbabilityTheory.cond, unitMeasure]
  cases active_phase_cases hr hx with
  | zero h =>
    subst x
    exact kernel_zero_endpoint_mem_active hr W htiling he
  | full h =>
    subst x
    exact kernel_full_endpoint_mem_active hr W he
  | ordinary i hunique =>
    exact kernel_ordinary_unique_mem_active hr W hx hunique htiling he
  | exceptional hxl hxu =>
    exact kernel_exceptional_interior_mem_active hr W hxl hxu htiling he
  | final hxl hxu =>
    exact kernel_final_interior_mem_active hr W hxl hxu htiling he
  | first h =>
    subst x
    have hclasses := first_crossing_classification (volume : Measure ℝ) hr W
      (D := Ioc 0 1) measurableSet_Ioc (by simp) (by simp)
      (by simpa only [hcond] using htiling) (by simpa only [hcond] using he)
    rcases hclasses with hOrd | hExc
    · obtain ⟨q, hq, hqr, hactive, ⟨P⟩⟩ := hOrd
      have P' : OrdinaryPartition r q (AStart r) W unitMeasure := by
        simpa only [hcond] using P
      exact ordinaryPartition_mem_active hr hq hqr hx hactive P'
    · obtain ⟨P⟩ := hExc
      have P' : ExceptionalPartition r (AStart r) W unitMeasure := by
        simpa only [hcond] using P
      exact exceptionalPartition_mem_active hr (AStart_pos hr).le (AStart_lt_AEnd hr).le
        (Phi_eq_A_on_middle_interval hr le_rfl (AStart_lt_AEnd hr).le) P'
  | tangent h =>
    subst x
    obtain ⟨q, hq, hqr, hactive, ⟨P⟩⟩ := tangent_crossing_classification (volume : Measure ℝ)
      hr W (D := Ioc 0 1) measurableSet_Ioc (by simp) (by simp)
      (by simpa only [hcond] using htiling) (by simpa only [hcond] using he)
    have P' : OrdinaryPartition r q (AEnd r) W unitMeasure := by
      simpa only [hcond] using P
    exact ordinaryPartition_mem_active hr hq hqr hx hactive P'
  | ordinaryCross i hi hir _ hiPhi hjPhi =>
    obtain ⟨q, hq, hqr, hactive, ⟨P⟩⟩ := ordinary_crossing_classification (volume : Measure ℝ)
      hi hir W (D := Ioc 0 1) measurableSet_Ioc (by simp) (by simp) hx hiPhi hjPhi
      (by simpa only [hcond] using htiling) (by simpa only [hcond] using he)
    have P' : OrdinaryPartition r q x W unitMeasure := by
      simpa only [hcond] using P
    exact ordinaryPartition_mem_active hr hq hqr hx hactive P'
  | terminalCross h =>
    subst x
    exact kernel_final_crossing_mem_active hr W htiling he

/-- Complete equality classification on the actual compact cut-metric
quotient. This theorem supplies the final input to both stability transfers. -/
theorem graphonSpace_equality_classification {r : ℕ} (hr : 3 ≤ r) {x : ℝ}
    (hx : x ∈ Icc 0 (1 / (r : ℝ))) (W : Vendor.GraphonSpace ℝ unitMeasure)
    (htiling : graphonSpaceTilingNumber unitMeasure r (by omega) W ≤ x)
    (he : graphonSpaceDensity unitMeasure W = Phi r x) : W ∈ activeFamily r x :=
  graphonSpace_classification_of_kernel unitMeasure (by omega : 0 < r)
    (fun U ht hd => kernel_equality_classification hr hx U ht hd) W htiling he

/-- The full equality-set identity, including the reverse inclusion from
explicit feasible construction covers. -/
theorem graphonSpace_extremal_iff_active {r : ℕ} (hr : 3 ≤ r) {x : ℝ}
    (hx : x ∈ Icc 0 (1 / (r : ℝ))) (W : Vendor.GraphonSpace ℝ unitMeasure) :
    (graphonSpaceTilingNumber unitMeasure r (by omega) W ≤ x ∧
      graphonSpaceDensity unitMeasure W = Phi r x) ↔ W ∈ activeFamily r x := by
  exact ⟨fun h => graphonSpace_equality_classification hr hx W h.1 h.2,
    activeFamily_extremal hr⟩

theorem kernel_extremal_iff_active {r : ℕ} (hr : 3 ≤ r) {x : ℝ}
    (hx : x ∈ Icc 0 (1 / (r : ℝ))) (W : Kernel ℝ) :
    (tilingNumber r W unitMeasure ≤ x ∧ density unitMeasure W = Phi r x) ↔
      Vendor.GraphonSpace.mk (W.toVendorGraphon unitMeasure) ∈ activeFamily r x := by
  constructor
  · rintro ⟨ht, hd⟩
    exact kernel_equality_classification hr hx W ht hd
  · intro h
    obtain ⟨ht, hd⟩ := kernel_extremal_of_mem_activeFamily hr W h
    exact ⟨ht.le, hd⟩

end DensityHS.Graphon
