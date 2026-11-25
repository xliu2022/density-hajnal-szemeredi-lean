module

public import DensityHS.Graphon.RResidual

/-!
# Exact terminal neighbor-type cardinalities

Author and maintainer: Xizhi Liu.

Every positive marked type has exactly `r-2` neighbors; distinct positive
types have intersection size `r-3` and are completely joined.
-/

@[expose] public section

namespace DensityHS.Graphon.MarkedBlockSystem

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Classical

variable {Ω : Type*} [MeasurableSpace Ω] {W : Kernel Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Z : Set Ω}

theorem typeFiber_nonzero (P : MarkedBlockSystem W μ Z) (A : Finset P.Index)
    (hA : 0 < μ.real (P.typeFiber A)) : μ (P.typeFiber A) ≠ 0 := by
  intro hz
  have : μ.real (P.typeFiber A) = 0 := by simp [measureReal_def, hz]
  linarith

theorem positive_type_card_le (P : MarkedBlockSystem W μ Z) {r : ℕ} (hr : 2 ≤ r)
    (hZ : MeasurableSet Z) (hfree : NoCliqueMeets r W μ Z)
    (A : Finset P.Index) (hA : 0 < μ.real (P.typeFiber A)) : A.card ≤ r - 2 := by
  classical
  obtain ⟨z, hzA, hz⟩ := exists_mem_of_measure_ne_zero_of_ae (P.typeFiber_nonzero A hA)
    (ae_restrict_of_ae (P.ae_finite_neighbors hr hZ hfree))
  obtain ⟨hs, hn⟩ := hz hzA.1
  have he : hs.toFinset = A := by
    ext i
    exact hs.mem_toFinset.trans (hzA.2 i)
  simpa only [he] using hn

/-- A positive type cannot have fewer than `r-2` neighbors: its entire
fiber would be a marked clique. -/
theorem positive_type_card (P : MarkedBlockSystem W μ Z) {r : ℕ} (hr : 3 ≤ r)
    (hZ : MeasurableSet Z) (hfree : NoCliqueMeets r W μ Z)
    (hd : ∀ᵐ z ∂μ, z ∈ Z → kernelDegree W μ z = ((r : ℝ) - 2) * μ.real Z)
    (A : Finset P.Index) (hA : 0 < μ.real (P.typeFiber A)) : A.card = r - 2 := by
  classical
  have hle := P.positive_type_card_le (by omega) hZ hfree A hA
  by_contra hn
  have hsmall : A.card ≤ r - 3 := by omega
  have hsmallR : (A.card : ℝ) ≤ (r : ℝ) - 3 := by
    have hh : (A.card : ℝ) ≤ ((r - 3 : ℕ) : ℝ) := by exact_mod_cast hsmall
    simpa only [Nat.cast_sub hr, Nat.cast_ofNat] using hh
  have hc : ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      z.1 ∈ P.typeFiber A → z.2 ∈ P.typeFiber A → 0 < W z.1 z.2 := by
    filter_upwards [P.ae_marked_row_of_degree hr hZ hfree hd A hle] with z hz hx hy
    rw [hz hx hy.1, P.neighborSum_of_typeFiber A A hy, Finset.inter_self]
    linarith
  exact hfree.not_complete_blocks (I := Fin r) (by simp)
    (fun _ => P.typeFiber A) (fun _ => P.measurable_typeFiber hZ A)
    (fun _ => P.typeFiber_nonzero A hA) (fun _ _ _ => hc)
    ⟨0, by omega⟩ (fun _ h => h.1)

/-- Two distinct positive types meet in exactly one fewer index. -/
theorem positive_type_inter_card (P : MarkedBlockSystem W μ Z) {r : ℕ} (hr : 3 ≤ r)
    (hZ : MeasurableSet Z) (hfree : NoCliqueMeets r W μ Z)
    (hd : ∀ᵐ z ∂μ, z ∈ Z → kernelDegree W μ z = ((r : ℝ) - 2) * μ.real Z)
    (A B : Finset P.Index) (hA : 0 < μ.real (P.typeFiber A))
    (hB : 0 < μ.real (P.typeFiber B)) (hAB : A ≠ B) : (A ∩ B).card = r - 3 := by
  classical
  have hAc := P.positive_type_card hr hZ hfree hd A hA
  have hBc := P.positive_type_card hr hZ hfree hd B hB
  have hneq : A ∩ B ≠ A := by
    intro he
    have hsub : A ⊆ B := by rw [← he]; exact Finset.inter_subset_right
    exact hAB (Finset.eq_of_subset_of_card_le hsub (by omega))
  have hupper : (A ∩ B).card < A.card := Finset.card_lt_card
    (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left, hneq⟩)
  have hprod : (μ.prod μ) ((P.typeFiber A) ×ˢ P.typeFiber B) ≠ 0 := by
    rw [Measure.prod_prod]
    exact mul_ne_zero (P.typeFiber_nonzero A hA) (P.typeFiber_nonzero B hB)
  obtain ⟨z, hz, hrow⟩ := exists_mem_of_measure_ne_zero_of_ae hprod
    (ae_restrict_of_ae (P.ae_marked_row_of_degree hr hZ hfree hd A hAc.le))
  have he := hrow hz.1 hz.2.1
  rw [P.neighborSum_of_typeFiber A B hz.2] at he
  have hcast : ((r - 2 : ℕ) : ℝ) = (r : ℝ) - 2 := by
    rw [Nat.cast_sub (show 2 ≤ r by omega), Nat.cast_ofNat]
  have hlowR : ((r - 2 : ℕ) : ℝ) ≤ ((A ∩ B).card : ℝ) + 1 := by
    rw [hcast]
    linarith [W.le_one z.1 z.2]
  have hlow : r - 2 ≤ (A ∩ B).card + 1 := by exact_mod_cast hlowR
  omega

/-- Distinct positive marked type fibers are completely joined. -/
theorem positive_type_cross_complete (P : MarkedBlockSystem W μ Z) {r : ℕ} (hr : 3 ≤ r)
    (hZ : MeasurableSet Z) (hfree : NoCliqueMeets r W μ Z)
    (hd : ∀ᵐ z ∂μ, z ∈ Z → kernelDegree W μ z = ((r : ℝ) - 2) * μ.real Z)
    (A B : Finset P.Index) (hA : 0 < μ.real (P.typeFiber A))
    (hB : 0 < μ.real (P.typeFiber B)) (hAB : A ≠ B) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ P.typeFiber A → z.2 ∈ P.typeFiber B → W z.1 z.2 = 1 := by
  have hAc := P.positive_type_card hr hZ hfree hd A hA
  have hIc := P.positive_type_inter_card hr hZ hfree hd A B hA hB hAB
  filter_upwards [P.ae_marked_row_of_degree hr hZ hfree hd A hAc.le] with z hz hx hy
  rw [hz hx hy.1, P.neighborSum_of_typeFiber A B hy, hIc,
    Nat.cast_sub hr, Nat.cast_ofNat]
  ring

end DensityHS.Graphon.MarkedBlockSystem
