module

public import DensityHS.Stability.EditDistance

/-!
# Rounding a nearby binary kernel to an actual finite graph

Author and maintainer: Xizhi Liu.

The overlap between a vertex cell and a template cell supplies an actual
probability vector. Independent choices give an actual finite template
blow-up while controlling both edge edits and its part sizes.
-/

@[expose] public section

namespace DensityHS.Stability

open MeasureTheory Set Finset Fintype Filter Regularity Graphon
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {Ω V I : Type*} [MeasurableSpace Ω]
  [Fintype V] [DecidableEq V] [MeasurableSpace V] [MeasurableSingletonClass V]
  [Fintype I] [DecidableEq I] [MeasurableSpace I] [MeasurableSingletonClass I]

noncomputable def jointLabelMass (μ : Measure Ω) (vl : Ω → V) (bl : Ω → I)
    (v : V) (i : I) : ℝ := μ.real {x | (vl x,bl x)=(v,i)}

theorem sum_jointLabelMass_right (μ : Measure Ω) [IsFiniteMeasure μ]
    (vl : Ω → V) (hv : Measurable vl) (bl : Ω → I) (hb : Measurable bl) (v : V) :
    (∑ i, jointLabelMass μ vl bl v i) = μ.real {x | vl x=v} := by
  have he : (⋃ i, {x | (vl x,bl x)=(v,i)}) = {x | vl x=v} := by
    ext x
    simp only [Set.mem_iUnion,Set.mem_setOf_eq,Prod.mk.injEq]
    constructor
    · rintro ⟨i,h,h'⟩
      exact h
    · intro h
      exact ⟨bl x,h,rfl⟩
  unfold jointLabelMass
  rw [← measureReal_iUnion_fintype,he]
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hij ((congrArg Prod.snd hx).symm.trans (congrArg Prod.snd hy))
  · intro i
    exact measurableSet_eq_fun (hv.prodMk hb) measurable_const

theorem sum_jointLabelMass_left (μ : Measure Ω) [IsFiniteMeasure μ]
    (vl : Ω → V) (hv : Measurable vl) (bl : Ω → I) (hb : Measurable bl) (i : I) :
    (∑ v, jointLabelMass μ vl bl v i) = μ.real {x | bl x=i} := by
  have he : (⋃ v, {x | (vl x,bl x)=(v,i)}) = {x | bl x=i} := by
    ext x
    simp only [Set.mem_iUnion,Set.mem_setOf_eq,Prod.mk.injEq]
    constructor
    · rintro ⟨v,h,h'⟩
      exact h'
    · intro h
      exact ⟨vl x,rfl,h⟩
  unfold jointLabelMass
  rw [← measureReal_iUnion_fintype,he]
  · intro v w hvw
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hvw ((congrArg Prod.fst hx).symm.trans (congrArg Prod.fst hy))
  · intro v
    exact measurableSet_eq_fun (hv.prodMk hb) measurable_const

noncomputable def vertexBlockWeight (μ : Measure Ω) (vl : Ω → V) (bl : Ω → I)
    (v : V) (i : I) : ℝ := (Fintype.card V : ℝ)*jointLabelMass μ vl bl v i

theorem probability_vertexBlockWeight [Nonempty V]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (vl : Ω → V) (hv : Measurable vl) (bl : Ω → I) (hb : Measurable bl)
    (hmass : ∀ v, μ.real {x | vl x=v} = 1/(Fintype.card V : ℝ)) (v : V) :
    IsProbabilityWeight (vertexBlockWeight μ vl bl v) := by
  refine ⟨fun i => mul_nonneg (Nat.cast_nonneg _) measureReal_nonneg,?_⟩
  unfold vertexBlockWeight
  rw [← Finset.mul_sum,sum_jointLabelMass_right μ vl hv bl hb,hmass]
  have hn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

theorem expectedPartSize_vertexBlockWeight (μ : Measure Ω) [IsFiniteMeasure μ]
    (vl : Ω → V) (hv : Measurable vl) (bl : Ω → I) (hb : Measurable bl) (i : I) :
    expectedPartSize (vertexBlockWeight μ vl bl) i =
      (Fintype.card V : ℝ)*μ.real {x | bl x=i} := by
  unfold expectedPartSize vertexBlockWeight
  rw [← Finset.mul_sum,sum_jointLabelMass_left μ vl hv bl hb]

theorem expectedCostBound_eq_kernelL1
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (vl : Ω → V) (hv : Measurable vl) (bl : Ω → I) (hb : Measurable bl)
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : I → I → ℝ) (W U : Kernel Ω)
    (hW : ∀ x y, W x y=indicatorMatrix G (vl x) (vl y))
    (hU : ∀ x y, U x y=A (bl x) (bl y)) :
    expectedCostBound (vertexBlockWeight μ vl bl) (fun u v i j => |indicatorMatrix G u v-A i j|) =
      (Fintype.card V : ℝ)^2*kernelL1Distance μ W U := by
  let L : Ω → V × I := fun x => (vl x,bl x)
  let F : (V × I) → (V × I) → ℝ := fun a b => |indicatorMatrix G a.1 b.1-A a.2 b.2|
  have hi := integral_finite_pair_labels μ μ L (hv.prodMk hb) L (hv.prodMk hb) F
  have hL1 : kernelL1Distance μ W U =
      ∑ u : V, ∑ i : I, ∑ v : V, ∑ j : I,
        jointLabelMass μ vl bl u i*jointLabelMass μ vl bl v j*|indicatorMatrix G u v-A i j| := by
    calc
      _ = ∫ z : Ω × Ω, F (L z.1) (L z.2) ∂μ.prod μ := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun z => by simp only [F,L,hW,hU])
      _ = _ := by
        rw [hi]
        simp only [Fintype.sum_prod_type,L,F,jointLabelMass]
  calc
    _ = ∑ u, ∑ v, ∑ i, ∑ j,
        (Fintype.card V : ℝ)^2*
          (jointLabelMass μ vl bl u i*jointLabelMass μ vl bl v j*|indicatorMatrix G u v-A i j|) := by
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro v _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      dsimp [vertexBlockWeight]
      ring
    _ = (Fintype.card V : ℝ)^2*(∑ u, ∑ v, ∑ i, ∑ j,
        jointLabelMass μ vl bl u i*jointLabelMass μ vl bl v j*|indicatorMatrix G u v-A i j|) := by
      simp only [Finset.mul_sum]
    _ = _ := by
      rw [hL1]
      congr 1
      apply Finset.sum_congr rfl
      intro u _
      exact Finset.sum_comm

theorem partCount_eq_fiberCount (f : V → I) (i : I) : partCount f i=(fiberCount f i : ℝ) := by
  simp only [partCount,fiberCount,assignmentCoin,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,
    Nat.cast_one,Nat.cast_zero]

/-- An actual finite blow-up close to the original graph, with a simultaneous
second-moment estimate for every template part size. -/
theorem exists_kernel_rounding [Nonempty V]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (vl : Ω → V) (hv : Measurable vl)
    (hmass : ∀ v, μ.real {x | vl x=v} = 1/(Fintype.card V : ℝ))
    (bl : Ω → I) (hb : Measurable bl)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : I → I → ℝ) (hsymm : ∀ i j, A i j=A j i) (hA : ∀ i j, A i j=0 ∨ A i j=1)
    (W U : Kernel Ω)
    (hW : ∀ x y, W x y=indicatorMatrix G (vl x) (vl y))
    (hU : ∀ x y, U x y=A (bl x) (bl y)) :
    ∃ f : V → I,
      2*(editDistance G (templateGraph A hsymm f) : ℝ)+
        (∑ i, ((fiberCount f i : ℝ)-(Fintype.card V : ℝ)*μ.real {x | bl x=i})^2) ≤
        (Fintype.card V : ℝ)^2*kernelL1Distance μ W U+Fintype.card V := by
  obtain ⟨f,hf⟩ := exists_assignment_with_cost_and_sizes (vertexBlockWeight μ vl bl)
    (probability_vertexBlockWeight μ vl hv bl hb hmass)
    (fun u v i j => |indicatorMatrix G u v-A i j|) (fun _ _ _ _ => abs_nonneg _)
  rw [assignmentCost_eq_two_edits G A hsymm hA,
    expectedCostBound_eq_kernelL1 μ vl hv bl hb G A W U hW hU] at hf
  refine ⟨f,?_⟩
  simpa only [partSquareError,partCount_eq_fiberCount,
    expectedPartSize_vertexBlockWeight μ vl hv bl hb] using hf

end DensityHS.Stability
