module

public import DensityHS.Finite.MatrixProjection
public import DensityHS.Finite.EqualChunks
public import Mathlib.Combinatorics.SimpleGraph.Regularity.Uniform

/-!
# Simultaneous matrix energy on vertex partitions

Author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS.MatrixRegularity

open Finset Fintype
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

noncomputable def partIndex (P : Finpartition (Finset.univ : Finset V)) (x : V) :
    P.parts := ⟨P.part x, P.part_mem.mpr (Finset.mem_univ x)⟩

@[simp] theorem partIndex_eq_iff {P : Finpartition (Finset.univ : Finset V)}
    {x : V} {A : P.parts} : partIndex P x = A ↔ x ∈ A.val := by
  rw [Subtype.ext_iff]
  exact P.part_eq_iff_mem A.property

theorem mem_partIndex (P : Finpartition (Finset.univ : Finset V)) (x : V) :
    x ∈ (partIndex P x).val := P.mem_part_self.mpr (Finset.mem_univ x)

theorem sum_parts (P : Finpartition (Finset.univ : Finset V)) (a : V → ℝ) :
    (∑ S ∈ P.parts, ∑ x ∈ S, a x) = ∑ x, a x := by
  calc
    _ = ∑ x ∈ P.parts.biUnion id, a x := (Finset.sum_biUnion P.disjoint).symm
    _ = _ := by rw [P.biUnion_parts]

theorem sum_part_rectangles (P : Finpartition (Finset.univ : Finset V))
    (a : V → V → ℝ) :
    (∑ S ∈ P.parts, ∑ T ∈ P.parts, ∑ x ∈ S, ∑ y ∈ T, a x y) =
      ∑ x, ∑ y, a x y := by
  calc
    _ = ∑ S ∈ P.parts, ∑ x ∈ S, ∑ T ∈ P.parts, ∑ y ∈ T, a x y := by
      apply Finset.sum_congr rfl
      intro S _
      exact Finset.sum_comm
    _ = _ := by simp_rw [sum_parts]

noncomputable def refinementParent {P Q : Finpartition (Finset.univ : Finset V)}
    (h : Q ≤ P) (A : Q.parts) : P.parts :=
  ⟨(h A.property).choose, (h A.property).choose_spec.1⟩

theorem subset_refinementParent {P Q : Finpartition (Finset.univ : Finset V)}
    (h : Q ≤ P) (A : Q.parts) : A.val ⊆ (refinementParent h A).val :=
  (h A.property).choose_spec.2

theorem refinementParent_partIndex {P Q : Finpartition (Finset.univ : Finset V)}
    (h : Q ≤ P) (x : V) : refinementParent h (partIndex Q x) = partIndex P x := by
  symm
  exact partIndex_eq_iff.mpr (subset_refinementParent h _ (mem_partIndex Q x))

noncomputable def matrixLabel (P : Finpartition (Finset.univ : Finset V))
    (z : C × V × V) : C × P.parts × P.parts :=
  (z.1, partIndex P z.2.1, partIndex P z.2.2)

noncomputable def matrixEnergy (P : Finpartition (Finset.univ : Finset V))
    (F : C → V → V → ℝ) : ℝ :=
  energy (matrixLabel P) (fun z : C × V × V => F z.1 z.2.1 z.2.2)

theorem matrixEnergy_nonneg (P : Finpartition (Finset.univ : Finset V))
    (F : C → V → V → ℝ) : 0 ≤ matrixEnergy P F := energy_nonneg _ _

theorem matrixEnergy_le (P : Finpartition (Finset.univ : Finset V))
    {F : C → V → V → ℝ} (h0 : ∀ c x y, 0 ≤ F c x y)
    (h1 : ∀ c x y, F c x y ≤ 1) :
    matrixEnergy P F ≤ (Fintype.card C : ℝ) * (Fintype.card V : ℝ)^2 := by
  have h := energy_le_card (matrixLabel P)
    (fun z : C × V × V => h0 z.1 z.2.1 z.2.2)
    (fun z : C × V × V => h1 z.1 z.2.1 z.2.2)
  simpa [matrixEnergy, Fintype.card_prod, Nat.cast_mul, pow_two, mul_assoc] using h

theorem matrixEnergy_mono {P Q : Finpartition (Finset.univ : Finset V)}
    (h : Q ≤ P) (F : C → V → V → ℝ) : matrixEnergy P F ≤ matrixEnergy Q F := by
  apply energy_mono_refinement (matrixLabel P) (matrixLabel Q)
    (fun z : C × Q.parts × Q.parts =>
      (z.1, refinementParent h z.2.1, refinementParent h z.2.2))
  intro z
  simp only [matrixLabel, refinementParent_partIndex]

/-- Average of an arbitrary, possibly nonsymmetric, matrix on a rectangle. -/
noncomputable def pairAverage (F : V → V → ℝ) (S T : Finset V) : ℝ :=
  (∑ x ∈ S, ∑ y ∈ T, F x y) / ((S.card : ℝ) * T.card)

theorem pairAverage_nonneg {F : V → V → ℝ} (hF : ∀ x y, 0 ≤ F x y)
    (S T : Finset V) : 0 ≤ pairAverage F S T :=
  div_nonneg (Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ => hF x y)))
    (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

theorem pairAverage_le_one {F : V → V → ℝ} (hF : ∀ x y, F x y ≤ 1)
    (S T : Finset V) : pairAverage F S T ≤ 1 := by
  unfold pairAverage
  apply div_le_of_le_mul₀ (by positivity) zero_le_one
  calc
    _ ≤ ∑ _x ∈ S, ∑ _y ∈ T, (1 : ℝ) :=
      Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => hF x y))
    _ = _ := by simp

theorem card_mul_pairAverage (F : V → V → ℝ) (S T : Finset V) :
    ((S.card : ℝ) * T.card) * pairAverage F S T = ∑ x ∈ S, ∑ y ∈ T, F x y := by
  by_cases hS : S = ∅
  · simp [hS, pairAverage]
  by_cases hT : T = ∅
  · simp [hT, pairAverage]
  have hs : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
  have ht : (T.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hT)
  unfold pairAverage
  field_simp

noncomputable def matrixFiberEquiv (P : Finpartition (Finset.univ : Finset V))
    (c : C) (A B : P.parts) :
    {z : C × V × V // matrixLabel P z = (c, A, B)} ≃ A.val × B.val where
  toFun z := by
    have h := z.property
    have hx : partIndex P z.val.2.1 = A := congrArg (fun t => t.2.1) h
    have hy : partIndex P z.val.2.2 = B := congrArg (fun t => t.2.2) h
    exact (⟨z.val.2.1, partIndex_eq_iff.mp hx⟩, ⟨z.val.2.2, partIndex_eq_iff.mp hy⟩)
  invFun z := ⟨(c, z.1.val, z.2.val), by
    simp only [matrixLabel]
    rw [partIndex_eq_iff.mpr z.1.property, partIndex_eq_iff.mpr z.2.property]⟩
  left_inv z := by
    apply Subtype.ext
    have hc : z.val.1 = c := congrArg Prod.fst z.property
    apply Prod.ext
    · exact hc.symm
    · rfl
  right_inv z := by rfl

theorem fiberAverage_matrixLabel (P : Finpartition (Finset.univ : Finset V))
    (F : C → V → V → ℝ) (c : C) (A B : P.parts) :
    fiberAverage (matrixLabel P) (fun z : C × V × V => F z.1 z.2.1 z.2.2) (c, A, B) =
      pairAverage (F c) A.val B.val := by
  classical
  let e := matrixFiberEquiv P c A B
  have hcard := Fintype.card_congr e
  have hsum : (∑ z : {z : C × V × V // matrixLabel P z = (c, A, B)},
      F z.val.1 z.val.2.1 z.val.2.2) = ∑ z : A.val × B.val, F c z.1 z.2 := by
    apply Fintype.sum_equiv e
    intro z
    have hc : z.val.1 = c := congrArg Prod.fst z.property
    simp only [hc]
    rfl
  change (∑ z : {z : C × V × V // matrixLabel P z = (c, A, B)},
      F z.val.1 z.val.2.1 z.val.2.2) /
      (Fintype.card {z : C × V × V // matrixLabel P z = (c, A, B)} : ℝ) =
        (∑ x ∈ A.val, ∑ y ∈ B.val, F c x y) / ((A.val.card : ℝ)*B.val.card)
  rw [hsum, hcard, Fintype.card_prod, Fintype.card_coe, Fintype.card_coe,
    Fintype.sum_prod_type]
  push_cast
  simp only [Finset.sum_coe_sort]
  congr 1
  exact Finset.sum_coe_sort A.val (fun x => ∑ y ∈ B.val, F c x y)

theorem blockProjection_matrixLabel (P : Finpartition (Finset.univ : Finset V))
    (F : C → V → V → ℝ) (c : C) (x y : V) :
    blockProjection (matrixLabel P) (fun z : C × V × V => F z.1 z.2.1 z.2.2) (c, x, y) =
      pairAverage (F c) (P.part x) (P.part y) :=
  fiberAverage_matrixLabel P F c (partIndex P x) (partIndex P y)

/-- A scalar test for a single colour still controls the increase of the
entire simultaneous energy. -/
theorem matrix_correlation_energy_bound
    {P Q : Finpartition (Finset.univ : Finset V)} (hQP : Q ≤ P)
    (F : C → V → V → ℝ) (c : C) (H : V → V → ℝ)
    (hH : ∀ x y x' y', partIndex Q x = partIndex Q x' →
      partIndex Q y = partIndex Q y' → H x y = H x' y')
    (hHsq : ∀ x y, (H x y)^2 ≤ 1) :
    (∑ x, ∑ y, (F c x y - pairAverage (F c) (P.part x) (P.part y)) * H x y)^2 ≤
      (matrixEnergy Q F - matrixEnergy P F) * (Fintype.card V : ℝ)^2 := by
  classical
  let a : C × V × V → ℝ := fun z => F z.1 z.2.1 z.2.2
  let T : C × V × V → ℝ := fun z => if z.1 = c then H z.2.1 z.2.2 else 0
  have hconst : ∀ z z', matrixLabel Q z = matrixLabel Q z' → T z = T z' := by
    intro z z' h
    have hc := congrArg Prod.fst h
    have hx := congrArg (fun t => t.2.1) h
    have hy := congrArg (fun t => t.2.2) h
    dsimp only [matrixLabel] at hc hx hy
    dsimp only [T]
    rw [hc, hH _ _ _ _ hx hy]
  let b := fiberAverage (matrixLabel Q) T
  have hb (z : C × V × V) : b (matrixLabel Q z) = T z :=
    projection_eq_of_fiber_const (matrixLabel Q) T hconst z
  have he := correlation_sq_le_energy_increment (matrixLabel P) (matrixLabel Q)
    (fun z : C × Q.parts × Q.parts =>
      (z.1, refinementParent hQP z.2.1, refinementParent hQP z.2.2))
    (fun z => by simp only [matrixLabel, refinementParent_partIndex]) a b
  simp_rw [hb] at he
  have hcorr : (∑ z : C × V × V, (a z - blockProjection (matrixLabel P) a z) * T z) =
      ∑ x, ∑ y, (F c x y - pairAverage (F c) (P.part x) (P.part y)) * H x y := by
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ j : C, if j = c then
          (∑ x, ∑ y, (F c x y - pairAverage (F c) (P.part x) (P.part y)) * H x y)
          else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j = c
        · subst j
          simp only [a, T, if_pos rfl, ite_true, Fintype.sum_prod_type, blockProjection_matrixLabel]
        · simp only [T, hj, if_false, mul_zero, Finset.sum_const_zero]
      _ = _ := by simp
  have hnorm : (∑ z : C × V × V, (T z)^2) ≤ (Fintype.card V : ℝ)^2 := by
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ x, ∑ y, (H x y)^2 := by
        simp only [T, Fintype.sum_prod_type]
        simp
      _ ≤ ∑ _x : V, ∑ _y : V, (1 : ℝ) :=
        Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => hHsq x y))
      _ = _ := by simp [pow_two]
  rw [hcorr] at he
  exact he.trans (mul_le_mul_of_nonneg_left hnorm (sub_nonneg.mpr (matrixEnergy_mono hQP F)))

/-- The usual regularity condition, now for an arbitrary real matrix. -/
def IsUniform (F : V → V → ℝ) (ε : ℝ) (S T : Finset V) : Prop :=
  ∀ ⦃S'⦄, S' ⊆ S → ∀ ⦃T'⦄, T' ⊆ T →
    (S.card : ℝ)*ε ≤ S'.card → (T.card : ℝ)*ε ≤ T'.card →
      |pairAverage F S' T' - pairAverage F S T| < ε

theorem not_isUniform_iff (F : V → V → ℝ) (ε : ℝ) (S T : Finset V) :
    ¬IsUniform F ε S T ↔ ∃ S' ⊆ S, ∃ T' ⊆ T,
      (S.card : ℝ)*ε ≤ S'.card ∧ (T.card : ℝ)*ε ≤ T'.card ∧
        ε ≤ |pairAverage F S' T' - pairAverage F S T| := by
  simp only [IsUniform, not_forall, not_lt, exists_prop]

/-- Indicator matrices have precisely the existing relation density. -/
theorem pairAverage_indicator (R : V → V → Prop) [DecidableRel R] (S T : Finset V) :
    pairAverage (fun x y => if R x y then 1 else 0) S T = (Rel.edgeDensity R S T : ℝ) := by
  classical
  unfold pairAverage Rel.edgeDensity Rel.interedges
  push_cast
  congr 1
  rw [← Finset.sum_product S T (fun z : V × V => if R z.1 z.2 then (1 : ℝ) else 0)]
  simp

theorem isUniform_graph_iff (G : SimpleGraph V) [DecidableRel G.Adj] (ε : ℝ)
    (S T : Finset V) :
    IsUniform (fun x y => if G.Adj x y then 1 else 0) ε S T ↔ G.IsUniform ε S T := by
  simp only [IsUniform, SimpleGraph.IsUniform, pairAverage_indicator, SimpleGraph.edgeDensity]

end DensityHS.MatrixRegularity
