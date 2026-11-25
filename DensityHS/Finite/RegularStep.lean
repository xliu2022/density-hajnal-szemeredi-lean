module

public import DensityHS.Finite.MatrixCut
public import DensityHS.Finite.ReducedGraph

/-!
# Cut approximation by the regular reduced matrix

Author and maintainer: Xizhi Liu.

The matrix keeps the actual density on every regular dense pair of parts
and is zero elsewhere. Its support is exactly the reduced graph already
used in the integral clique-packing argument.
-/

@[expose] public section

namespace DensityHS.Regularity

open Finset Fintype MatrixRegularity
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

def indicatorMatrix (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) : ℝ :=
  if G.Adj x y then 1 else 0

theorem indicatorMatrix_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) :
    0 ≤ indicatorMatrix G x y := by unfold indicatorMatrix; split_ifs <;> norm_num

theorem indicatorMatrix_le_one (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) :
    indicatorMatrix G x y ≤ 1 := by unfold indicatorMatrix; split_ifs <;> norm_num

theorem indicatorMatrix_symm (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) :
    indicatorMatrix G x y = indicatorMatrix G y x := by
  simp only [indicatorMatrix, G.adj_comm]

theorem sum_indicatorMatrix (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ x, ∑ y, indicatorMatrix G x y) = 2*(G.edgeFinset.card : ℝ) := by
  have h := edgeMass_one G
  unfold edgeMass at h
  simp only [mul_one, one_mul] at h
  change (∑ x, ∑ y, indicatorMatrix G x y)/2 = (G.edgeFinset.card : ℝ) at h
  linarith

noncomputable def reducedStepEntry (P : Finpartition (Finset.univ : Finset V))
    (G : SimpleGraph V) [DecidableRel G.Adj] (ε d : ℝ) (i j : P.parts) : ℝ :=
  if (clusterGraph P G ε d).Adj i j then
    pairAverage (indicatorMatrix G) i.val j.val else 0

noncomputable def reducedStepMatrix (P : Finpartition (Finset.univ : Finset V))
    (G : SimpleGraph V) [DecidableRel G.Adj] (ε d : ℝ) (x y : V) : ℝ :=
  reducedStepEntry P G ε d (clusterOf P x) (clusterOf P y)

theorem reducedStepEntry_nonneg (P : Finpartition (Finset.univ : Finset V))
    (G : SimpleGraph V) [DecidableRel G.Adj] (ε d : ℝ) (i j : P.parts) :
    0 ≤ reducedStepEntry P G ε d i j := by
  unfold reducedStepEntry
  split_ifs
  · exact pairAverage_nonneg (indicatorMatrix_nonneg G) _ _
  · rfl

theorem reducedStepEntry_le_one (P : Finpartition (Finset.univ : Finset V))
    (G : SimpleGraph V) [DecidableRel G.Adj] (ε d : ℝ) (i j : P.parts) :
    reducedStepEntry P G ε d i j ≤ 1 := by
  unfold reducedStepEntry
  split_ifs
  · exact pairAverage_le_one (indicatorMatrix_le_one G) _ _
  · norm_num

theorem reducedStepEntry_symm (P : Finpartition (Finset.univ : Finset V))
    (G : SimpleGraph V) [DecidableRel G.Adj] (ε d : ℝ) (i j : P.parts) :
    reducedStepEntry P G ε d i j = reducedStepEntry P G ε d j i := by
  unfold reducedStepEntry
  rw [(clusterGraph P G ε d).adj_comm]
  congr 1
  change pairAverage (fun x y => if G.Adj x y then 1 else 0) i.val j.val =
    pairAverage (fun x y => if G.Adj x y then 1 else 0) j.val i.val
  rw [pairAverage_indicator, pairAverage_indicator]
  exact_mod_cast G.edgeDensity_comm i.val j.val

theorem regularityReduced_adj_iff_cluster
    (P : Finpartition (Finset.univ : Finset V)) (G : SimpleGraph V)
    [DecidableRel G.Adj] (ε d : ℝ) (x y : V) :
    (G.regularityReduced P ε d).Adj x y ↔
      G.Adj x y ∧ (clusterGraph P G ε d).Adj (clusterOf P x) (clusterOf P y) := by
  constructor
  · intro h
    exact ⟨h.1, reduced_le_cluster_comap P G ε d h⟩
  · rintro ⟨hxy, hparts, hreg, hd⟩
    refine ⟨hxy, P.part x, P.part_mem.mpr (Finset.mem_univ x),
      P.part y, P.part_mem.mpr (Finset.mem_univ y),
      P.mem_part_self.mpr (Finset.mem_univ x),
      P.mem_part_self.mpr (Finset.mem_univ y), ?_, hreg, hd⟩
    intro heq
    exact hparts (Subtype.ext heq)

theorem sum_rectangle_by_parts (P : Finpartition (Finset.univ : Finset V))
    (F : V → V → ℝ) (S T : Finset V) :
    (∑ x ∈ S, ∑ y ∈ T, F x y) =
      ∑ A ∈ P.parts, ∑ B ∈ P.parts, ∑ x ∈ A ∩ S, ∑ y ∈ B ∩ T, F x y := by
  have h := sum_part_rectangles P
    (fun x y => if x ∈ S then (if y ∈ T then F x y else 0) else 0)
  simpa only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_mem,
    Finset.univ_inter] using h.symm

theorem reducedStep_rectangle_on_parts
    (P : Finpartition (Finset.univ : Finset V)) (G : SimpleGraph V)
    [DecidableRel G.Adj] {ε d : ℝ} (hε : 0 ≤ ε)
    {A B : Finset V} (hA : A ∈ P.parts) (hB : B ∈ P.parts) (S T : Finset V) :
    |∑ x ∈ A ∩ S, ∑ y ∈ B ∩ T,
      (indicatorMatrix (G.regularityReduced P ε d) x y - reducedStepMatrix P G ε d x y)| ≤
        ε*A.card*B.card := by
  let i : P.parts := ⟨A,hA⟩
  let j : P.parts := ⟨B,hB⟩
  have hx (x : V) (hx : x ∈ A ∩ S) : clusterOf P x = i :=
    clusterOf_eq_iff.mpr (Finset.mem_inter.mp hx).1
  have hy (y : V) (hy : y ∈ B ∩ T) : clusterOf P y = j :=
    clusterOf_eq_iff.mpr (Finset.mem_inter.mp hy).1
  by_cases hij : (clusterGraph P G ε d).Adj i j
  · have heq : (∑ x ∈ A ∩ S, ∑ y ∈ B ∩ T,
        (indicatorMatrix (G.regularityReduced P ε d) x y - reducedStepMatrix P G ε d x y)) =
        ∑ x ∈ A ∩ S, ∑ y ∈ B ∩ T,
          (indicatorMatrix G x y - pairAverage (indicatorMatrix G) A B) := by
      apply Finset.sum_congr rfl
      intro x hxs
      apply Finset.sum_congr rfl
      intro y hyt
      simp only [indicatorMatrix, regularityReduced_adj_iff_cluster,
        reducedStepMatrix, reducedStepEntry, hx x hxs, hy y hyt, hij, and_true,
        ite_true, i, j]
    rw [heq]
    exact ((isUniform_graph_iff G ε A B).mpr hij.2.1).rectangle_discrepancy
      hε (indicatorMatrix_nonneg G) (indicatorMatrix_le_one G)
      Finset.inter_subset_left Finset.inter_subset_left
  · have hz : (∑ x ∈ A ∩ S, ∑ y ∈ B ∩ T,
        (indicatorMatrix (G.regularityReduced P ε d) x y - reducedStepMatrix P G ε d x y)) = 0 := by
      apply Finset.sum_eq_zero
      intro x hxs
      apply Finset.sum_eq_zero
      intro y hyt
      simp only [indicatorMatrix, regularityReduced_adj_iff_cluster,
        reducedStepMatrix, reducedStepEntry, hx x hxs, hy y hyt, hij, and_false,
        ite_false, sub_self]
    rw [hz, abs_zero]
    positivity

theorem reducedStep_reduced_discrepancy
    (P : Finpartition (Finset.univ : Finset V)) (G : SimpleGraph V)
    [DecidableRel G.Adj] {ε d : ℝ} (hε : 0 ≤ ε) (S T : Finset V) :
    |∑ x ∈ S, ∑ y ∈ T,
      (indicatorMatrix (G.regularityReduced P ε d) x y - reducedStepMatrix P G ε d x y)| ≤
        ε*(Fintype.card V : ℝ)^2 := by
  rw [sum_rectangle_by_parts P]
  have hc : (∑ A ∈ P.parts, (A.card : ℝ)) = Fintype.card V := by
    exact_mod_cast P.sum_card_parts
  calc
    _ ≤ ∑ A ∈ P.parts, |∑ B ∈ P.parts, ∑ x ∈ A ∩ S, ∑ y ∈ B ∩ T,
        (indicatorMatrix (G.regularityReduced P ε d) x y - reducedStepMatrix P G ε d x y)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ A ∈ P.parts, ∑ B ∈ P.parts,
        |∑ x ∈ A ∩ S, ∑ y ∈ B ∩ T,
          (indicatorMatrix (G.regularityReduced P ε d) x y - reducedStepMatrix P G ε d x y)| :=
      Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ A ∈ P.parts, ∑ B ∈ P.parts, ε*A.card*B.card :=
      Finset.sum_le_sum (fun A hA => Finset.sum_le_sum
        (fun B hB => reducedStep_rectangle_on_parts P G hε hA hB S T))
    _ = _ := by rw [← Finset.sum_mul_sum, ← Finset.mul_sum, hc]; ring

theorem subgraph_rectangle_discrepancy (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (hHG : H ≤ G) (S T : Finset V) :
    |∑ x ∈ S, ∑ y ∈ T, (indicatorMatrix G x y - indicatorMatrix H x y)| ≤
      2*((G.edgeFinset.card : ℝ) - H.edgeFinset.card) := by
  have hn (x y : V) : 0 ≤ indicatorMatrix G x y - indicatorMatrix H x y := by
    unfold indicatorMatrix
    by_cases h : H.Adj x y
    · simp [h,hHG h]
    · simp only [h,ite_false,sub_zero]
      split_ifs <;> norm_num
  rw [abs_of_nonneg (Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ => hn x y)))]
  calc
    _ ≤ ∑ x ∈ S, ∑ y : V, (indicatorMatrix G x y - indicatorMatrix H x y) := by
      apply Finset.sum_le_sum
      intro x _
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T) (fun _ _ _ => hn x _)
    _ ≤ ∑ x : V, ∑ y : V, (indicatorMatrix G x y - indicatorMatrix H x y) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        (fun x _ _ => Finset.sum_nonneg (fun y _ => hn x y))
    _ = _ := by simp only [Finset.sum_sub_distrib, sum_indicatorMatrix]; ring

/-- Uniform cut-discrepancy bound for the actual regular dense step model. -/
theorem reducedStep_discrepancy [Nonempty V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : Finpartition (Finset.univ : Finset V)} {ε d η : ℝ}
    (hε : 0 < ε) (hd : 0 ≤ d) (hη : 0 < η)
    (hP : P.IsEquipartition) (hreg : P.IsUniform G ε)
    (hparts : 4/η ≤ P.parts.card) (S T : Finset V) :
    |∑ x ∈ S, ∑ y ∈ T,
      (indicatorMatrix G x y - reducedStepMatrix P G ε d x y)| ≤
        (5*ε+4*d+η/2)*(Fintype.card V : ℝ)^2 := by
  have heq : (∑ x ∈ S, ∑ y ∈ T,
        (indicatorMatrix G x y - reducedStepMatrix P G ε d x y)) =
      (∑ x ∈ S, ∑ y ∈ T,
        (indicatorMatrix G x y - indicatorMatrix (G.regularityReduced P ε d) x y)) +
      (∑ x ∈ S, ∑ y ∈ T,
        (indicatorMatrix (G.regularityReduced P ε d) x y - reducedStepMatrix P G ε d x y)) := by
    simp only [Finset.sum_sub_distrib]
    ring
  rw [heq]
  have hloss := regularity_edge_loss hε hd hη hP hreg hparts
  have hdel := subgraph_rectangle_discrepancy G (G.regularityReduced P ε d)
    SimpleGraph.regularityReduced_le S T
  have havg := reducedStep_reduced_discrepancy P G (d := d) hε.le S T
  exact (abs_add_le _ _).trans (by linarith)

end DensityHS.Regularity
