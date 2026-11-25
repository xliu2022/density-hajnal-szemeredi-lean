module

public import DensityHS.Graphon.RTypeCardinality
public import DensityHS.Basic.JohnsonClique

/-!
# Terminal types form a finite Johnson clique

Author and maintainer: Xizhi Liu.

Three positive types cannot form a Johnson star: three marked vertices and
one vertex from every common unmarked block would give a forbidden clique.
-/

@[expose] public section

namespace DensityHS.Graphon.MarkedBlockSystem

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Classical

variable {Ω : Type*} [MeasurableSpace Ω] {W : Kernel Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Z : Set Ω}

/-- Three distinct positive marked types cannot contain a common
codimension-one intersection. -/
theorem positive_types_no_star (P : MarkedBlockSystem W μ Z) {r : ℕ} (hr : 3 ≤ r)
    (hZ : MeasurableSet Z) (hfree : NoCliqueMeets r W μ Z)
    (hd : ∀ᵐ z ∂μ, z ∈ Z → kernelDegree W μ z = ((r : ℝ) - 2) * μ.real Z)
    (A B C : Finset P.Index) (hA : 0 < μ.real (P.typeFiber A))
    (hB : 0 < μ.real (P.typeFiber B)) (hC : 0 < μ.real (P.typeFiber C))
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) : ¬ A ∩ B ⊆ C := by
  classical
  intro hstar
  let T : Fin 3 → Finset P.Index := ![A, B, C]
  let K := A ∩ B
  have hK : K.card = r - 3 := P.positive_type_inter_card hr hZ hfree hd A B hA hB hAB
  have hTpos : ∀ i, 0 < μ.real (P.typeFiber (T i)) := by
    intro i
    fin_cases i
    · exact hA
    · exact hB
    · exact hC
  have hTi : Function.Injective T := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [T]
  have hKT : ∀ i, K ⊆ T i := by
    intro i
    fin_cases i
    · exact Finset.inter_subset_left
    · exact Finset.inter_subset_right
    · exact hstar
  let S : Fin 3 ⊕ K → Set Ω := Sum.elim (fun i => P.typeFiber (T i)) (fun j => P.block j)
  have hS : ∀ i, MeasurableSet (S i) := by
    intro i
    cases i with
    | inl a => exact P.measurable_typeFiber hZ (T a)
    | inr j => exact P.measurable j
  have hS0 : ∀ i, μ (S i) ≠ 0 := by
    intro i
    cases i with
    | inl a => exact P.typeFiber_nonzero (T a) (hTpos a)
    | inr j => exact P.block_nonzero j
  have hcross : ∀ i j : Fin 3 ⊕ K, i ≠ j → ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      z.1 ∈ S i → z.2 ∈ S j → 0 < W z.1 z.2 := by
    intro i j hij
    cases i with
    | inl a =>
      cases j with
      | inl b =>
        have hab : T a ≠ T b := fun he => hij (congrArg Sum.inl (hTi he))
        filter_upwards [P.positive_type_cross_complete hr hZ hfree hd
          (T a) (T b) (hTpos a) (hTpos b) hab] with z hz hx hy
        rw [hz hx hy]
        norm_num
      | inr j =>
        filter_upwards [P.neighbor_complete j] with z hz hx hy
        exact hz ((hx.2 j).mpr (hKT a j.2)) hy
    | inr i =>
      cases j with
      | inl b =>
        have hs := (measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
          (P.neighbor_complete i)
        filter_upwards [hs] with z hz hx hy
        rw [W.symmetric z.1 z.2]
        exact hz ((hy.2 i).mpr (hKT b i.2)) hx
      | inr j =>
        exact P.cross_complete i j (fun he => hij (congrArg Sum.inr (Subtype.ext he)))
  exact hfree.not_complete_blocks (I := Fin 3 ⊕ K)
    (by simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_coe]; omega)
    S hS hS0 hcross (.inl 0) (fun _ h => h.1)

/-- All positive marked types lie in one set of at most `r-1` unmarked
block indices. This is the finite Johnson conclusion derived from actual
kernel clique exclusions. -/
theorem exists_type_container (P : MarkedBlockSystem W μ Z) {r : ℕ} (hr : 3 ≤ r)
    (hZ : MeasurableSet Z) (hfree : NoCliqueMeets r W μ Z)
    (hd : ∀ᵐ z ∂μ, z ∈ Z → kernelDegree W μ z = ((r : ℝ) - 2) * μ.real Z) :
    ∃ T : Finset P.Index, T.card ≤ r - 1 ∧
      ∀ A : Finset P.Index, 0 < μ.real (P.typeFiber A) → A ⊆ T := by
  classical
  obtain ⟨T, hT, hsub⟩ := DensityHS.johnson_clique_contained (k := r - 2) (by omega)
    {A | 0 < μ.real (P.typeFiber A)}
    (fun A hA => P.positive_type_card hr hZ hfree hd A hA)
    (fun A hA B hB hAB => by
      have hh := P.positive_type_inter_card hr hZ hfree hd A B hA hB hAB
      simpa only [Nat.sub_sub] using hh)
    (fun A hA B hB C hC hAB hAC hBC =>
      P.positive_types_no_star hr hZ hfree hd A B C hA hB hC hAB hAC hBC)
  exact ⟨T, by omega, hsub⟩

end DensityHS.Graphon.MarkedBlockSystem
