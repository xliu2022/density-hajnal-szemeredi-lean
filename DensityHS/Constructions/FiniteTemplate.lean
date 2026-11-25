module

public import DensityHS.Constructions.WeightedInterval

/-!
# Interval models of arbitrary finite weighted templates

Author and maintainer: Xizhi Liu.

The finite index type need not have an order. A fixed finite equivalence
selects an interval order; the labels have exactly the prescribed masses.
Zero weights and diagonal template entries are allowed.
-/

@[expose] public section

namespace DensityHS.Constructions

open MeasureTheory Set

variable {I : Type*} [Fintype I] [Nonempty I]

/-- A fixed enumeration of a nonempty finite type, used only to arrange cells. -/
noncomputable def intervalEquiv (I : Type*) [Fintype I] [Nonempty I] :
    I ≃ Fin ((Fintype.card I - 1) + 1) :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin]
    exact (Nat.sub_add_cancel (Nat.succ_le_iff.mpr Fintype.card_pos)).symm)

noncomputable def intervalWeights (p : I → ℝ) :
    Fin ((Fintype.card I - 1) + 1) → ℝ := p ∘ (intervalEquiv I).symm

theorem probability_intervalWeights {p : I → ℝ} (hp : IsProbabilityWeight p) :
    IsProbabilityWeight (intervalWeights p) := by
  refine ⟨fun j => hp.1 _, ?_⟩
  exact ((intervalEquiv I).symm.sum_comp p).trans hp.2

/-- The canonical interval label for an arbitrary finite probability vector. -/
noncomputable def intervalLabel (p : I → ℝ) (x : ℝ) : I :=
  (intervalEquiv I).symm (cutLabel (weightedCuts (intervalWeights p)) x)

theorem measurable_intervalLabel [MeasurableSpace I] [MeasurableSingletonClass I]
    (p : I → ℝ) : Measurable (intervalLabel p) :=
  (measurable_of_finite (intervalEquiv I).symm).comp (measurable_cutLabel _)

/-- Exact cell measures, including all zero-mass cells. -/
theorem intervalLabel_mass {p : I → ℝ} (hp : IsProbabilityWeight p) (i : I) :
    unitMeasure.real {x | intervalLabel p x = i} = p i := by
  have he : {x | intervalLabel p x = i} =
      {x | cutLabel (weightedCuts (intervalWeights p)) x = intervalEquiv I i} := by
    ext x
    exact (intervalEquiv I).symm_apply_eq
  rw [he, weighted_label_mass (probability_intervalWeights hp)]
  simp [intervalWeights]

/-- Every integral of a function of the labels is its finite weighted sum. -/
theorem integral_intervalLabel {p : I → ℝ} (hp : IsProbabilityWeight p) (f : I → ℝ) :
    (∫ x, f (intervalLabel p x) ∂unitMeasure) = ∑ i, p i * f i := by
  change (∫ x, (f ∘ (intervalEquiv I).symm)
      (cutLabel (weightedCuts (intervalWeights p)) x) ∂unitMeasure) = _
  rw [integral_weighted_label (probability_intervalWeights hp)]
  exact (intervalEquiv I).symm.sum_comp (fun i => p i * f i)

/-- A finite symmetric matrix with entries in the unit interval. -/
structure FiniteTemplate (I : Type*) where
  entry : I → I → ℝ
  symmetric : ∀ i j, entry i j = entry j i
  nonneg : ∀ i j, 0 ≤ entry i j
  le_one : ∀ i j, entry i j ≤ 1

noncomputable def FiniteTemplate.toPattern (A : FiniteTemplate I) :
    StepPattern (Fintype.card I - 1) where
  entry i j := A.entry ((intervalEquiv I).symm i) ((intervalEquiv I).symm j)
  symmetric _ _ := A.symmetric _ _
  nonneg _ _ := A.nonneg _ _
  le_one _ _ := A.le_one _ _

/-- A concrete kernel on the real unit interval. -/
noncomputable def FiniteTemplate.kernel (A : FiniteTemplate I) (p : I → ℝ) :
    Graphon.Kernel ℝ := A.toPattern.kernel (weightedCuts (intervalWeights p))

@[simp] theorem FiniteTemplate.kernel_apply (A : FiniteTemplate I) (p : I → ℝ)
    (x y : ℝ) : A.kernel p x y = A.entry (intervalLabel p x) (intervalLabel p y) := rfl

/-- The corresponding point in the actual compact graphon quotient. -/
noncomputable def FiniteTemplate.graphon (A : FiniteTemplate I) (p : I → ℝ) :
    Vendor.GraphonSpace ℝ unitMeasure := A.toPattern.graphon (weightedCuts (intervalWeights p))

theorem FiniteTemplate.density (A : FiniteTemplate I) {p : I → ℝ}
    (hp : IsProbabilityWeight p) :
    Graphon.density unitMeasure (A.kernel p) =
      (∑ i, ∑ j, p i * p j * A.entry i j) / 2 := by
  rw [FiniteTemplate.kernel, StepPattern.density_weighted _ (probability_intervalWeights hp)]
  congr 1
  change (∑ i, ∑ j, p ((intervalEquiv I).symm i) * p ((intervalEquiv I).symm j) *
    A.entry ((intervalEquiv I).symm i) ((intervalEquiv I).symm j)) = _
  refine Fintype.sum_equiv (intervalEquiv I).symm _ _ ?_
  intro i
  exact (intervalEquiv I).symm.sum_comp
    (fun j => p ((intervalEquiv I).symm i) * p j * A.entry ((intervalEquiv I).symm i) j)

theorem continuous_intervalWeights : Continuous (intervalWeights (I := I)) := by
  apply continuous_pi
  intro j
  exact continuous_apply _

theorem FiniteTemplate.continuous_graphon (A : FiniteTemplate I) : Continuous A.graphon :=
  A.toPattern.continuous_weighted_graphon.comp continuous_intervalWeights

/-- The zero-one finite template of a loopless simple graph. -/
noncomputable def FiniteTemplate.ofSimpleGraph (G : SimpleGraph I) : FiniteTemplate I := by
  classical
  exact
    { entry := fun i j => if G.Adj i j then 1 else 0
      symmetric := by intro i j; simp only [G.adj_comm i j]
      nonneg := by intro i j; split_ifs <;> norm_num
      le_one := by intro i j; split_ifs <;> norm_num }

theorem FiniteTemplate.density_ofSimpleGraph (G : SimpleGraph I) {p : I → ℝ}
    (hp : IsProbabilityWeight p) :
    Graphon.density unitMeasure ((FiniteTemplate.ofSimpleGraph G).kernel p) = edgeMass G p := by
  classical
  rw [FiniteTemplate.density _ hp]
  unfold edgeMass FiniteTemplate.ofSimpleGraph
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp_all

theorem FiniteTemplate.ofSimpleGraph_pos_iff (G : SimpleGraph I) (p : I → ℝ) (x y : ℝ) :
    0 < (FiniteTemplate.ofSimpleGraph G).kernel p x y ↔
      G.Adj (intervalLabel p x) (intervalLabel p y) := by
  classical
  rw [FiniteTemplate.kernel_apply]
  change (0 < if G.Adj _ _ then (1 : ℝ) else 0) ↔ _
  split_ifs <;> simp_all

end DensityHS.Constructions
