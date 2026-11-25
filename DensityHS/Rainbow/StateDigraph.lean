module

public import DensityHS.Rainbow.RegularStateModel
public import DensityHS.Rainbow.RegularCounting

/-!
# Retaining exactly the selected regular arc states

On a reduced digon only original double arcs remain.  On a reduced single
arc only the original exclusive direction remains.  Consequently every
constraint graph used by a reduced tile agrees exactly with one of the
two simultaneously regularized matrices on its cluster pairs.

Formalization author and maintainer: Xizhi Liu.
-/

@[expose] public section

open Finset

namespace DensityHS.Rainbow

open MatrixRegularity

attribute [local instance] Classical.propDecidable

variable {V I K : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

theorem cluster_eq_of_common_vertex {S : I → Finset V}
    (hdis : (Set.univ : Set I).PairwiseDisjoint S) {i j : I} {x : V}
    (hi : x ∈ S i) (hj : x ∈ S j) : i = j := by
  by_contra hij
  exact Finset.disjoint_left.mp (hdis (Set.mem_univ _) (Set.mem_univ _) hij) hi hj

def stateDigraph (D : Digraph V) (R : Digraph I) (S : I → Finset V) : Digraph V where
  Arc x y := ∃ i j, x ∈ S i ∧ y ∈ S j ∧ R.Arc i j ∧ D.Arc x y ∧ (R.Arc j i ↔ D.Arc y x)
  loopless x := by
    rintro ⟨i, j, _, _, _, h, _⟩
    exact D.loopless x h

theorem stateDigraph_arc_sub {D : Digraph V} {R : Digraph I} {S : I → Finset V}
    {x y : V} (h : (stateDigraph D R S).Arc x y) : D.Arc x y := by
  obtain ⟨i, j, _, _, _, h, _⟩ := h
  exact h

theorem stateDigraph_base_le (D : Digraph V) (R : Digraph I) (S : I → Finset V) :
    (stateDigraph D R S).baseGraph ≤ D.baseGraph := by
  intro x y h
  exact h.imp stateDigraph_arc_sub stateDigraph_arc_sub

theorem stateDigraph_outgoing_distinct {G : SimpleGraph V} {C : G.EdgeLabeling K}
    {D : Digraph V} (hout : OutgoingColorsDistinct D C) (R : Digraph I) (S : I → Finset V) :
    OutgoingColorsDistinct (stateDigraph D R S) C := by
  intro v x y hx hy hcol
  exact hout (stateDigraph_arc_sub hx) (stateDigraph_arc_sub hy) hcol

theorem stateDigraph_arc_iff (D : Digraph V) (R : Digraph I) {S : I → Finset V}
    (hdis : (Set.univ : Set I).PairwiseDisjoint S) {i j : I} {x y : V}
    (hx : x ∈ S i) (hy : y ∈ S j) :
    (stateDigraph D R S).Arc x y ↔ R.Arc i j ∧ D.Arc x y ∧ (R.Arc j i ↔ D.Arc y x) := by
  constructor
  · rintro ⟨a, b, hxa, hyb, hab, hxy, hrev⟩
    have hai : a = i := cluster_eq_of_common_vertex hdis hxa hx
    have hbj : b = j := cluster_eq_of_common_vertex hdis hyb hy
    subst a
    subst b
    exact ⟨hab, hxy, hrev⟩
  · rintro ⟨hij, hxy, hrev⟩
    exact ⟨i, j, hx, hy, hij, hxy, hrev⟩

theorem stateConstraint_on_pair (D : Digraph V) (R : Digraph I) {S : I → Finset V}
    (hdis : (Set.univ : Set I).PairwiseDisjoint S) {r : ℕ} (e : Fin r ↪ I)
    {i j : Fin r} (hij : i ≠ j) (hR : R.Arc (e i) (e j)) {x y : V}
    (hx : x ∈ S (e i)) (hy : y ∈ S (e j)) :
    (tileConstraintGraph (stateDigraph D R S) (R.comap e) (fun k => S (e k))).Adj x y ↔
      D.Arc x y ∧ (R.Arc (e j) (e i) ↔ D.Arc y x) := by
  constructor
  · intro h
    have hs := ((h.2 i j hx hy).1 hR)
    exact ((stateDigraph_arc_iff D R hdis hx hy).mp hs).2
  · intro h
    have hne : x ≠ y := by
      intro hxy
      have hmem : x ∈ S (e j) := hxy ▸ hy
      exact hij (e.injective (cluster_eq_of_common_vertex hdis hx hmem))
    refine ⟨hne, ?_⟩
    intro a b hxa hyb
    have hai : a = i := e.injective (cluster_eq_of_common_vertex hdis hxa hx)
    have hbj : b = j := e.injective (cluster_eq_of_common_vertex hdis hyb hy)
    subst a
    subst b
    constructor
    · intro _
      exact (stateDigraph_arc_iff D R hdis hx hy).mpr ⟨hR, h⟩
    · intro hrev
      exact (stateDigraph_arc_iff D R hdis hy hx).mpr
        ⟨hrev, h.2.mp hrev, ⟨fun _ => h.1, fun _ => hR⟩⟩

theorem RegularStateModel.constraint_uniform_forward {D : Digraph V} {ε d : ℝ} {k m r : ℕ}
    (Q : RegularStateModel D ε d k m) (e : Fin r ↪ Fin k)
    {i j : Fin r} (hij : i ≠ j) (hR : Q.reduced.Arc (e i) (e j)) :
    let H := tileConstraintGraph (stateDigraph D Q.reduced Q.clusters) (Q.reduced.comap e)
      (fun a => Q.clusters (e a))
    H.IsUniform ε (Q.clusters (e i)) (Q.clusters (e j)) ∧
      d ≤ (H.edgeDensity (Q.clusters (e i)) (Q.clusters (e j)) : ℝ) := by
  classical
  dsimp only
  let H := tileConstraintGraph (stateDigraph D Q.reduced Q.clusters) (Q.reduced.comap e)
    (fun a => Q.clusters (e a))
  have hs := Q.state (e i) (e j) hR
  by_cases hrev : Q.reduced.Arc (e j) (e i)
  · have heq : ∀ x ∈ Q.clusters (e i), ∀ y ∈ Q.clusters (e j),
        (if H.Adj x y then (1 : ℝ) else 0) = doubleMatrix D x y := by
      intro x hx y hy
      have hh := stateConstraint_on_pair D Q.reduced Q.disjoint e hij hR hx hy
      simp only [hrev, true_iff] at hh
      simp only [H, hh, doubleMatrix]
    refine ⟨?_, ?_⟩
    · apply (isUniform_graph_iff H ε _ _).mp
      exact (matrixUniform_congr_on heq).mpr hs.2.1
    · change d ≤ (Rel.edgeDensity H.Adj _ _ : ℝ)
      rw [← pairAverage_indicator, pairAverage_congr_on heq]
      exact hs.2.2.1 hrev
  · have heq : ∀ x ∈ Q.clusters (e i), ∀ y ∈ Q.clusters (e j),
        (if H.Adj x y then (1 : ℝ) else 0) = exclusiveMatrix D x y := by
      intro x hx y hy
      have hh := stateConstraint_on_pair D Q.reduced Q.disjoint e hij hR hx hy
      simp only [hrev, false_iff] at hh
      simp only [H, hh, exclusiveMatrix]
    refine ⟨?_, ?_⟩
    · apply (isUniform_graph_iff H ε _ _).mp
      exact (matrixUniform_congr_on heq).mpr hs.1
    · change d ≤ (Rel.edgeDensity H.Adj _ _ : ℝ)
      rw [← pairAverage_indicator, pairAverage_congr_on heq]
      exact hs.2.2.2 hrev

end DensityHS.Rainbow
