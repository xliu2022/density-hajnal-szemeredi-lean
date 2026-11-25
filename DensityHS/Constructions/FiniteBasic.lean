module

public import DensityHS.Basic.Tilings
public import DensityHS.Basic.Reindex
public import DensityHS.Basic.Envelope
public import DensityHS.Finite.ReducedGraph
public import Mathlib.Combinatorics.SimpleGraph.Sum
public import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite
public import Mathlib.Data.Nat.Choose.Cast

/-!
# Finite extremal construction tools

Author and maintainer: Xizhi Liu.

The graph constructions below use joins, disjoint sums, and complete
equipartite graphs.  A resource-counting lemma certifies their integral clique
packing obstruction.
-/

@[expose] public section

namespace DensityHS.Constructions

open Finset

variable {V W : Type*}

/-- Join two graphs, keeping their internal edges and adding every cross edge. -/
def joinGraph (G : SimpleGraph V) (H : SimpleGraph W) : SimpleGraph (V ⊕ W) where
  Adj
    | .inl u, .inl v => G.Adj u v
    | .inr u, .inr v => H.Adj u v
    | _, _ => True
  symm := ⟨by
    rintro (u | u) (v | v) h
    · exact h.symm
    · trivial
    · trivial
    · exact h.symm⟩
  loopless := ⟨by rintro (u | u) h <;> exact h.ne rfl⟩

section Finite

variable [Fintype V] [Fintype W]

theorem edgeMass_join (G : SimpleGraph V) (H : SimpleGraph W)
    (p : V → ℝ) (q : W → ℝ) :
    edgeMass (joinGraph G H) (Sum.elim p q) =
      edgeMass G p + edgeMass H q + (∑ v, p v) * (∑ w, q w) := by
  classical
  simp [edgeMass, Fintype.sum_sum_type, joinGraph, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]
  ring_nf
  ac_rfl

theorem edgeMass_sum (G : SimpleGraph V) (H : SimpleGraph W)
    (p : V → ℝ) (q : W → ℝ) :
    edgeMass (G ⊕g H) (Sum.elim p q) = edgeMass G p + edgeMass H q := by
  classical
  simp only [edgeMass, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    SimpleGraph.sum_adj, ite_false, Finset.sum_const_zero, add_zero, zero_add]
  ring

theorem edgeMass_join_one (G : SimpleGraph V) (H : SimpleGraph W) :
    edgeMass (joinGraph G H) (fun _ => 1) = edgeMass G (fun _ => 1) +
      edgeMass H (fun _ => 1) + (Fintype.card V : ℝ) * Fintype.card W := by
  have h := edgeMass_join G H (fun _ => 1) (fun _ => 1)
  have heq : (Sum.elim (fun _ : V => (1 : ℝ)) (fun _ : W => 1)) =
      (fun _ : V ⊕ W => 1) := by funext x; cases x <;> rfl
  simpa only [heq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using h

theorem edgeMass_sum_one (G : SimpleGraph V) (H : SimpleGraph W) :
    edgeMass (G ⊕g H) (fun _ => 1) = edgeMass G (fun _ => 1) +
      edgeMass H (fun _ => 1) := by
  have h := edgeMass_sum G H (fun _ => 1) (fun _ => 1)
  have heq : (Sum.elim (fun _ : V => (1 : ℝ)) (fun _ : W => 1)) =
      (fun _ : V ⊕ W => 1) := by funext x; cases x <;> rfl
  simpa only [heq] using h

theorem edgeMass_top_one : edgeMass (⊤ : SimpleGraph V) (fun _ => 1) =
    (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) / 2 := by
  classical
  rw [Regularity.edgeMass_one, SimpleGraph.card_edgeFinset_top_eq_card_choose_two,
    Nat.cast_choose_two]

theorem edgeMass_bot_one : edgeMass (⊥ : SimpleGraph V) (fun _ => 1) = 0 := by
  classical
  simp [edgeMass]

theorem edgeMass_equipartite_one (s q : ℕ) :
    edgeMass (SimpleGraph.completeEquipartiteGraph s q) (fun _ => 1) =
      (s : ℝ) * ((s : ℝ) - 1) * (q : ℝ) ^ 2 / 2 := by
  rw [Regularity.edgeMass_one, SimpleGraph.card_edgeFinset_completeEquipartiteGraph]
  push_cast
  rw [Nat.cast_choose_two]
  ring

end Finite

section Packing

variable [Fintype V] [DecidableEq V]

/-- If each clique consumes `i` vertices of a resource of size at most `i*k`,
then every vertex-disjoint clique packing has at most `k` members. -/
theorem packing_bound_of_resource {r i k : ℕ} (hi : 0 < i)
    (G : SimpleGraph V) (X : Finset V) (hX : X.card ≤ i * k)
    (hclique : ∀ K, G.IsNClique r K → i ≤ (K ∩ X).card) :
    HasPackingNumberAtMost r G k := by
  intro P hP
  have hdisj : (P : Set (Finset V)).PairwiseDisjoint (fun K => K ∩ X) := by
    intro K hK L hL hKL
    exact (hP.2 hK hL hKL).mono Finset.inter_subset_left Finset.inter_subset_left
  have hsubset : P.biUnion (fun K => K ∩ X) ⊆ X := by
    intro v hv
    obtain ⟨K, _, hvK⟩ := Finset.mem_biUnion.mp hv
    exact (Finset.mem_inter.mp hvK).2
  have hlow : P.card * i ≤ ∑ K ∈ P, (K ∩ X).card := by
    calc
      P.card * i = ∑ _K ∈ P, i := by simp
      _ ≤ _ := Finset.sum_le_sum (fun K hK => hclique K (hP.1 K hK))
  have hhigh : (∑ K ∈ P, (K ∩ X).card) ≤ X.card := by
    rw [← Finset.card_biUnion hdisj]
    exact Finset.card_le_card hsubset
  exact Nat.le_of_mul_le_mul_right
    (hlow.trans (hhigh.trans (by simpa only [Nat.mul_comm i k] using hX))) hi

/-- A proper coloring of the vertices outside a resource bounds the number
of outside vertices in every clique. -/
theorem clique_sdiff_card_le_colors {C : Type*} [Fintype C]
    (G : SimpleGraph V) (X : Finset V) (f : V → C)
    (hcolor : ∀ u v, G.Adj u v → u ∉ X → v ∉ X → f u ≠ f v)
    {K : Finset V} (hK : G.IsClique K) : (K \ X).card ≤ Fintype.card C := by
  classical
  have hinj : Function.Injective (fun v : ↥(K \ X) => f v) := by
    intro u v huv
    apply Subtype.ext
    by_contra hne
    have hu := Finset.mem_sdiff.mp u.property
    have hv := Finset.mem_sdiff.mp v.property
    exact hcolor u v (hK hu.1 hv.1 hne) hu.2 hv.2 huv
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective _ hinj

/-- If a monochromatic edge must have both ends in the resource, a clique
larger than the color set must use at least two resource vertices. -/
theorem clique_resource_card_two {C : Type*} [Fintype C]
    (G : SimpleGraph V) (X : Finset V) (f : V → C)
    (hcolor : ∀ u v, G.Adj u v → f u ≠ f v ∨ (u ∈ X ∧ v ∈ X))
    {r : ℕ} (hr : Fintype.card C < r) {K : Finset V} (hK : G.IsNClique r K) :
    2 ≤ (K ∩ X).card := by
  classical
  by_contra hlarge
  have hsmall : (K ∩ X).card ≤ 1 := by omega
  have hinj : Function.Injective (fun v : K => f v) := by
    intro u v huv
    apply Subtype.ext
    by_contra hne
    rcases hcolor u v (hK.isClique u.property v.property hne) with hneq | hboth
    · exact hneq huv
    · exact hne (Finset.card_le_one.mp hsmall u
        (Finset.mem_inter.mpr ⟨u.property, hboth.1⟩) v
        (Finset.mem_inter.mpr ⟨v.property, hboth.2⟩))
  have hcard := Fintype.card_le_of_injective _ hinj
  rw [Fintype.card_coe, hK.card_eq] at hcard
  exact hr.not_ge hcard

end Packing

section Relabel

variable [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

theorem packing_bound_pullback {r k : ℕ} {G : SimpleGraph V}
    (hG : HasPackingNumberAtMost r G k) (e : W ↪ V) :
    HasPackingNumberAtMost r (G.comap e) k := by
  classical
  intro P hP
  let Q := P.image (fun K => K.map e)
  have hinj : Function.Injective (fun K : Finset W => K.map e) := Finset.map_injective e
  have hQ : IsCliquePacking r G Q := by
    constructor
    · intro K hK
      obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp hK
      exact SimpleGraph.IsNClique.mono (SimpleGraph.map_comap_le e G) (hP.1 L hL).map
    · intro K hK L hL hKL
      obtain ⟨K', hK', rfl⟩ := Finset.mem_image.mp hK
      obtain ⟨L', hL', rfl⟩ := Finset.mem_image.mp hL
      have hdisj := hP.2 hK' hL' (fun h => hKL (congrArg (fun T => T.map e) h))
      apply Finset.disjoint_left.mpr
      intro v hvK hvL
      obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hvK
      obtain ⟨w, hw, heq⟩ := Finset.mem_map.mp hvL
      have hwu : w = u := e.injective heq
      exact Finset.disjoint_left.mp hdisj hu (hwu ▸ hw)
  have hcard : Q.card = P.card := Finset.card_image_of_injective _ hinj
  exact hcard ▸ hG Q hQ

end Relabel

end DensityHS.Constructions
