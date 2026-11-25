module

public import DensityHS.Rainbow.ConnectorGraph
public import DensityHS.Rainbow.ProperCounting
public import DensityHS.Rainbow.LocalAbsorbers

/-!
# Proper auxiliary extensions at the two connector roots

Only the concrete root extensions are required to be properly coloured.
Outgoing colour uniqueness and the two removed root colours prove this
property directly.

Formalization author and maintainer: Xizhi Liu.
-/

@[expose] public section

open Finset

namespace DensityHS.Rainbow

attribute [local instance] Classical.propDecidable

variable {V K : Type*} [DecidableEq V] {G : SimpleGraph V}
    {C : G.EdgeLabeling K} {D : Digraph V}

def attachRootGraph (H : SimpleGraph V) (Z : Finset V) (x : V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ((u ∈ Z ∧ v ∈ Z ∧ H.Adj u v) ∨
    (u = x ∧ v ∈ Z) ∨ (v = x ∧ u ∈ Z))
  symm := ⟨by
    intro u v h
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with h | h | h
    · exact Or.inl ⟨h.2.1, h.1, h.2.2.symm⟩
    · exact Or.inr (Or.inr ⟨h.1, h.2⟩)
    · exact Or.inr (Or.inl ⟨h.1, h.2⟩)⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem attachRootGraph_le {H : SimpleGraph V} {Z : Finset V} {x : V}
    (hH : H ≤ G) (hx : ∀ v ∈ Z, G.Adj x v) : attachRootGraph H Z x ≤ G := by
  intro u v h
  rcases h.2 with h | h | h
  · exact hH h.2.2
  · obtain ⟨rfl, hv⟩ := h
    exact hx v hv
  · obtain ⟨rfl, hu⟩ := h
    exact (hx u hu).symm

theorem attachRootGraph_root_neighbor {H : SimpleGraph V} {Z : Finset V} {x v : V}
    (hx : x ∉ Z) (h : (attachRootGraph H Z x).Adj x v) : v ∈ Z := by
  rcases h.2 with h | h | h
  · exact h.2.1
  · exact h.2
  · exact False.elim (hx h.2)

theorem attachRootGraph_nonroot {H : SimpleGraph V} {Z : Finset V} {x u v : V}
    (hu : u ≠ x) (hv : v ≠ x) (h : (attachRootGraph H Z x).Adj u v) :
    u ∈ Z ∧ v ∈ Z ∧ H.Adj u v := by
  rcases h.2 with h | h | h
  · exact h
  · exact False.elim (hu h.1)
  · exact False.elim (hv h.1)

theorem attachRootGraph_proper (hout : OutgoingColorsDistinct D C)
    (H : SimpleGraph V) (Z : Finset V) (x : V) (hx : x ∉ Z)
    (hH : ∀ u v, H.Adj u v → D.Arc u v ∧ edgeColor C u v ≠ edgeColor C u x)
    (hstar : ∀ v ∈ Z, D.Arc x v) (hsub : attachRootGraph H Z x ≤ G) :
    IsProper (restrictColor C hsub) := by
  intro v a b hva hvb hcol
  rw [edgeColor_restrict_of_adj C hsub hva, edgeColor_restrict_of_adj C hsub hvb] at hcol
  by_cases hv : v = x
  · subst v
    exact hout (hstar a (attachRootGraph_root_neighbor hx hva))
      (hstar b (attachRootGraph_root_neighbor hx hvb)) hcol
  by_cases ha : a = x
  · subst a
    by_cases hb : b = x
    · exact hb.symm
    · have hHvb := (attachRootGraph_nonroot hv hb hvb).2.2
      exact False.elim ((hH v b hHvb).2 hcol.symm)
  by_cases hb : b = x
  · subst b
    have hHva := (attachRootGraph_nonroot hv ha hva).2.2
    exact False.elim ((hH v a hHva).2 hcol)
  exact hout (hH v a (attachRootGraph_nonroot hv ha hva).2.2).1
    (hH v b (attachRootGraph_nonroot hv hb hvb).2.2).1 hcol

theorem attachRootGraph_clique {H : SimpleGraph V} {Z S : Finset V} {x : V} {t : ℕ}
    (hS : H.IsNClique t S) (hSZ : S ⊆ Z) (hx : x ∉ Z) :
    (attachRootGraph H Z x).IsNClique (t + 1) (Insert.insert x S) := by
  have hcl : (attachRootGraph H Z x).IsNClique t S := by
    refine ⟨?_, hS.card_eq⟩
    intro u hu v hv huv
    exact ⟨huv, Or.inl ⟨hSZ hu, hSZ hv, hS.isClique hu hv huv⟩⟩
  apply hcl.insert
  intro v hv
  exact ⟨(fun heq => hx (heq ▸ hSZ hv)), Or.inr (Or.inl ⟨rfl, hSZ hv⟩)⟩

variable [Fintype V]

noncomputable def commonLeftGraph (D : Digraph V) (C : G.EdgeLabeling K) (x y : V) : SimpleGraph V :=
  attachRootGraph (rootCompatibleDigraph D C x y).doubleGraph (commonOutSet D x y) x

noncomputable def commonRightGraph (D : Digraph V) (C : G.EdgeLabeling K) (x y : V) : SimpleGraph V :=
  attachRootGraph (rootCompatibleDigraph D C x y).doubleGraph (commonOutSet D x y) y

theorem rootCompatible_double_le (hbase : D.baseGraph ≤ G) (x y : V) :
    (rootCompatibleDigraph D C x y).doubleGraph ≤ G := by
  intro u v h
  exact hbase (Or.inl h.1.1)

theorem commonLeftGraph_le (hbase : D.baseGraph ≤ G) (x y : V) :
    commonLeftGraph D C x y ≤ G := by
  apply attachRootGraph_le (rootCompatible_double_le hbase x y)
  intro v hv
  exact hbase (Or.inl ((D.mem_outNeighbors _ _).mp (mem_inter.mp hv).1))

theorem commonRightGraph_le (hbase : D.baseGraph ≤ G) (x y : V) :
    commonRightGraph D C x y ≤ G := by
  apply attachRootGraph_le (rootCompatible_double_le hbase x y)
  intro v hv
  exact hbase (Or.inl ((D.mem_outNeighbors _ _).mp (mem_inter.mp hv).2))

theorem commonLeftGraph_proper (hbase : D.baseGraph ≤ G)
    (hout : OutgoingColorsDistinct D C) (x y : V) :
    IsProper (restrictColor C (commonLeftGraph_le (C := C) hbase x y)) := by
  apply attachRootGraph_proper hout _ _ x (roots_not_mem_commonOutSet D x y).1
  · intro u v h
    exact ⟨h.1.1, h.1.2.1⟩
  · intro v hv
    exact (D.mem_outNeighbors _ _).mp (mem_inter.mp hv).1

theorem commonRightGraph_proper (hbase : D.baseGraph ≤ G)
    (hout : OutgoingColorsDistinct D C) (x y : V) :
    IsProper (restrictColor C (commonRightGraph_le (C := C) hbase x y)) := by
  apply attachRootGraph_proper hout _ _ y (roots_not_mem_commonOutSet D x y).2
  · intro u v h
    exact ⟨h.1.1, h.1.2.2⟩
  · intro v hv
    exact (D.mem_outNeighbors _ _).mp (mem_inter.mp hv).2

end DensityHS.Rainbow
