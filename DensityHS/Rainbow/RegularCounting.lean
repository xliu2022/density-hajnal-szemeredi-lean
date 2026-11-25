module

public import DensityHS.Finite.RegularCounting
public import DensityHS.Rainbow.ColorDigraph

/-!
# Rainbow transversal embedding from regular directed constraints

A symmetric constraint graph records the prescribed arcs of a directed tile
between the given clusters.  Regular clique counting in that actual graph
and the explicit bad-rainbow-map bound produce a genuine rainbow transversal.

Formalization author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS.Rainbow

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {V I K : Type*}

theorem tile_image_of_injective [Fintype I] [DecidableEq I]
    [Fintype V] [DecidableEq V] {r : ℕ} {R : Digraph I} {D : Digraph V}
    {S : Finset I} (hS : R.IsTile r S) (f : I → V) (hinj : Function.Injective f)
    (harcs : ∀ i j, R.Arc i j → D.Arc (f i) (f j)) :
    D.IsTile r (S.image f) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, hS.1]
  · intro x hx y hy hxy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    have hij : i ≠ j := fun h => hxy (congrArg f h)
    rcases hS.2.1 hi hj hij with h | h
    · exact Or.inl (harcs i j h)
    · exact Or.inr (harcs j i h)
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hsub : (S.filter (R.Arc i)).image f ⊆ (S.image f).filter (D.Arc (f i)) := by
      intro y hy
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
      rcases Finset.mem_filter.mp hj with ⟨hjS, hij⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨j, hjS, rfl⟩, harcs i j hij⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hinj] at hcard
    exact (hS.2.2 i hi).trans hcard

/-- On the specified cluster pair, adjacency requires every arc prescribed
by the directed pattern, including both arcs when the pattern has a digon. -/
def tileConstraintGraph {r : ℕ} (D : Digraph V) (R : Digraph (Fin r))
    (S : Fin r → Finset V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ ∀ i j, x ∈ S i → y ∈ S j →
    (R.Arc i j → D.Arc x y) ∧ (R.Arc j i → D.Arc y x)
  symm := ⟨by
    intro x y h
    refine ⟨h.1.symm, ?_⟩
    intro i j hxi hyj
    exact ⟨(h.2 j i hyj hxi).2, (h.2 j i hyj hxi).1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem constraint_transversal_isTile [Fintype V] [DecidableEq V]
    {r : ℕ} {D : Digraph V} {R : Digraph (Fin r)} (hR : R.IsTile r Finset.univ)
    {S P : Fin r → Finset V} (hPS : ∀ i, P i ⊆ S i) {f : Fin r → V}
    (hf : f ∈ Regularity.transversalCliqueMaps (tileConstraintGraph D R S) r P) :
    D.IsTile r (Finset.univ.image f) := by
  classical
  have hinj := Regularity.transversalCliqueMaps_injective (tileConstraintGraph D R S) hf
  rcases (Regularity.mem_transversalCliqueMaps (tileConstraintGraph D R S)).mp hf with
    ⟨hmem, hadj⟩
  apply tile_image_of_injective hR f hinj
  intro i j hij
  have hne : i ≠ j := by
    intro h
    subst j
    exact R.loopless i hij
  exact ((hadj i j hne).2 i j (hPS i (hmem i)) (hPS j (hmem j))).1 hij

/-- Quantitative rainbow embedding from actual regular pairs of the
directed constraint graph.  The strict numerical hypothesis compares the
proved regular count with the proved bad-map bound. -/
theorem exists_regular_rainbow_transversal [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {C : G.EdgeLabeling K} {D : Digraph V}
    {r : ℕ} (hr : 3 ≤ r) (R : Digraph (Fin r)) (hR : R.IsTile r Finset.univ)
    (hbase : D.baseGraph ≤ G) (hout : OutgoingColorsDistinct D C)
    (hstar : HasStarColorClasses C) {ε d α : ℝ}
    (hε : 0 < ε) (hd : ε < d) (hd1 : d - ε ≤ 1) (hα : 0 < α)
    (S P : Fin r → Finset V) (hP : ∀ i, P i ⊆ S i)
    (hsize : ∀ i, α * (S i).card ≤ (P i).card)
    (hreg : ∀ i j, i ≠ j → (tileConstraintGraph D R S).IsUniform ε (S i) (S j))
    (hdensity : ∀ i j, i ≠ j →
      d ≤ ((tileConstraintGraph D R S).edgeDensity (S i) (S j) : ℝ))
    (hsmall : 2 * ε * r < α * (d - ε) ^ (r - 1))
    (hlarge : ∀ i, 4 ≤ α * (d - ε) ^ (r - 1) * (S i).card)
    (hgap : (((r ^ 3 + r ^ 4) * Fintype.card V ^ (r - 1) : ℕ) : ℝ) <
      (α * (d - ε) ^ (r - 1) / 4) ^ r * (∏ i, ((S i).card : ℝ))) :
    ∃ f : Fin r → V, (∀ i, f i ∈ P i) ∧
      IsRainbowClique r C (Finset.univ.image f) := by
  classical
  let F := Regularity.transversalCliqueMaps (tileConstraintGraph D R S) r P
  have hcount := Regularity.regular_transversal_count_density (tileConstraintGraph D R S)
    r hε hd hd1 hα S P hP hsize hreg hdensity hsmall hlarge
  have hmany : (r ^ 3 + r ^ 4) * Fintype.card V ^ (r - 1) < F.card := by
    exact_mod_cast hgap.trans_le hcount
  obtain ⟨f, hf, hrainbow⟩ := exists_rainbow_tile_of_many_maps hr hbase hout hstar F
    (fun f hf => ⟨Regularity.transversalCliqueMaps_injective _ hf,
      constraint_transversal_isTile hR hP hf⟩) hmany
  exact ⟨f, ((Regularity.mem_transversalCliqueMaps _).mp hf).1, hrainbow⟩

end DensityHS.Rainbow
