module

public import DensityHS.Basic.Tilings
public import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling

/-!
# Edge-coloured graphs and rainbow clique packings

Colours are attached to the actual unordered edges of a simple graph using
mathlib's `EdgeLabeling`.  A rainbow packing only requires distinct colours
within each clique; colours may repeat between different cliques.

Formalization author and maintainer: Xizhi Liu.
-/

@[expose] public section

open Finset

namespace DensityHS.Rainbow

variable {V K : Type*} {G : SimpleGraph V}

/-- A total colour accessor.  The extra value `none` is used exactly on
nonedges and does not enlarge the set of colours of any actual edge. -/
noncomputable def edgeColor (C : G.EdgeLabeling K) (x y : V) : Option K := by
  classical
  exact if h : G.Adj x y then some (C.get x y h) else none

theorem edgeColor_of_adj (C : G.EdgeLabeling K) {x y : V} (h : G.Adj x y) :
    edgeColor C x y = some (C.get x y h) := by
  classical
  simp [edgeColor, h]

theorem edgeColor_comm (C : G.EdgeLabeling K) (x y : V) :
    edgeColor C x y = edgeColor C y x := by
  classical
  by_cases h : G.Adj x y
  · rw [edgeColor_of_adj C h, edgeColor_of_adj C h.symm]
    congr 1
    exact (C.get_comm x y h.symm).symm
  · have hyx : ¬G.Adj y x := fun h' => h h'.symm
    simp [edgeColor, h, hyx]

/-- Properness means that two edges sharing a vertex have different colours. -/
def IsProper (C : G.EdgeLabeling K) : Prop :=
  ∀ ⦃v x y : V⦄, G.Adj v x → G.Adj v y →
    edgeColor C v x = edgeColor C v y → x = y

theorem isProper_iff_get (C : G.EdgeLabeling K) :
    IsProper C ↔ ∀ (v x y : V) (hx : G.Adj v x) (hy : G.Adj v y),
      C.get v x hx = C.get v y hy → x = y := by
  constructor
  · intro h v x y hx hy hc
    apply h hx hy
    rw [edgeColor_of_adj C hx, edgeColor_of_adj C hy, hc]
  · intro h v x y hx hy hc
    rw [edgeColor_of_adj C hx, edgeColor_of_adj C hy] at hc
    exact h v x y hx hy (Option.some.inj hc)

/-- Every two equally coloured edges inside the vertex set are the same
unordered edge. -/
def IsRainbowOn (C : G.EdgeLabeling K) (S : Finset V) : Prop :=
  ∀ ⦃x y u v : V⦄, x ∈ S → y ∈ S → u ∈ S → v ∈ S →
    G.Adj x y → G.Adj u v → edgeColor C x y = edgeColor C u v →
      s(x, y) = s(u, v)

def IsRainbowClique (r : ℕ) (C : G.EdgeLabeling K) (S : Finset V) : Prop :=
  G.IsNClique r S ∧ IsRainbowOn C S

def IsRainbowPacking (r : ℕ) (C : G.EdgeLabeling K)
    (P : Finset (Finset V)) : Prop :=
  IsCliquePacking r G P ∧ ∀ S ∈ P, IsRainbowOn C S

def HasPerfectRainbowPackingOn [DecidableEq V] (r : ℕ)
    (C : G.EdgeLabeling K) (U : Finset V) : Prop :=
  ∃ P : Finset (Finset V), IsRainbowPacking r C P ∧ P.biUnion id = U

theorem IsRainbowOn.mono {C : G.EdgeLabeling K} {S T : Finset V}
    (h : IsRainbowOn C T) (hST : S ⊆ T) : IsRainbowOn C S := by
  intro x y u v hx hy hu hv hxy huv hc
  exact h (hST hx) (hST hy) (hST hu) (hST hv) hxy huv hc

theorem isRainbowOn_empty (C : G.EdgeLabeling K) : IsRainbowOn C ∅ := by
  intro x y u v hx
  simp at hx

theorem isRainbowClique_empty (C : G.EdgeLabeling K) :
    IsRainbowClique 0 C ∅ := by
  exact ⟨⟨by simpa using (SimpleGraph.isClique_empty (G := G)), by simp⟩,
    isRainbowOn_empty C⟩

/-- An extension step for a rainbow clique.  Properness controls the colours
on the new star; the last hypothesis excludes old clique colours. -/
theorem IsRainbowOn.insert [DecidableEq V] {C : G.EdgeLabeling K}
    {S : Finset V} {w : V} (h : IsRainbowOn C S) (hp : IsProper C)
    (hfresh : ∀ y ∈ S, ∀ u ∈ S, ∀ v ∈ S,
      edgeColor C w y ≠ edgeColor C u v) : IsRainbowOn C (Insert.insert w S) := by
  have hincident {y u v : V} (hy : y ∈ S) (hu : u ∈ Insert.insert w S)
      (hv : v ∈ Insert.insert w S) (hwy : G.Adj w y) (huv : G.Adj u v)
      (hc : edgeColor C w y = edgeColor C u v) : s(w, y) = s(u, v) := by
    rcases Finset.mem_insert.mp hu with hu | hu
    · subst u
      have heq := hp hwy huv hc
      subst v
      rfl
    rcases Finset.mem_insert.mp hv with hv | hv
    · subst v
      have heq := hp hwy huv.symm (hc.trans (edgeColor_comm C u w))
      subst u
      exact Sym2.eq_swap
    · exact False.elim (hfresh y hy u hu v hv hc)
  intro x y u v hx hy hu hv hxy huv hc
  rcases Finset.mem_insert.mp hx with hx | hx
  · subst x
    rcases Finset.mem_insert.mp hy with hy | hy
    · subst y
      exact False.elim (hxy.ne rfl)
    · exact hincident hy hu hv hxy huv hc
  rcases Finset.mem_insert.mp hy with hy | hy
  · subst y
    have heq := hincident hx hu hv hxy.symm huv
      ((edgeColor_comm C w x).trans hc)
    exact Sym2.eq_swap.trans heq
  rcases Finset.mem_insert.mp hu with hu | hu
  · subst u
    rcases Finset.mem_insert.mp hv with hv | hv
    · subst v
      exact False.elim (huv.ne rfl)
    · exact (hincident hv (mem_insert_of_mem hx) (mem_insert_of_mem hy)
        huv hxy hc.symm).symm
  rcases Finset.mem_insert.mp hv with hv | hv
  · subst v
    have heq := hincident hu (mem_insert_of_mem hx) (mem_insert_of_mem hy)
      huv.symm hxy ((edgeColor_comm C w u).trans hc.symm)
    exact heq.symm.trans Sym2.eq_swap
  · exact h hx hy hu hv hxy huv hc

/-- The number of distinct colours incident with a vertex. -/
noncomputable def colorDegree (C : G.EdgeLabeling K) (v : V) : ℕ :=
  (edgeColor C v '' G.neighborSet v).ncard

theorem colorDegree_le_degree [Fintype V] [DecidableRel G.Adj]
    (C : G.EdgeLabeling K) (v : V) :
    colorDegree C v ≤ G.degree v := by
  classical
  unfold colorDegree
  exact (Set.ncard_image_le (s := G.neighborSet v) (f := edgeColor C v)).trans_eq
    (G.ncard_neighborSet v)

theorem IsProper.colorDegree_eq_degree [Fintype V] [DecidableRel G.Adj] {C : G.EdgeLabeling K}
    (h : IsProper C) (v : V) : colorDegree C v = G.degree v := by
  classical
  unfold colorDegree
  have hinj : Set.InjOn (edgeColor C v) (G.neighborSet v) := by
    intro x hx y hy hc
    exact h hx hy hc
  rw [hinj.ncard_image, G.ncard_neighborSet v]

end DensityHS.Rainbow
