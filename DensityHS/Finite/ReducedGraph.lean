/-
The edge-loss estimates adapt mathlib's regularity-reduction proofs.
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Modified 2026 by Xizhi Liu for independent regularity/density parameters.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DensityHS.Weighted.UniversalPeeling
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal

/-!
# Reduced graphs and finite edge-loss estimates

Author and maintainer: Xizhi Liu.

The edge-loss proof adapts the proved mathlib regularity-reduction argument
to independent regularity and density parameters. This separation is needed
for clique sizes larger than three.
-/

@[expose] public section

namespace DensityHS.Regularity

open Finset Fintype

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem unreduced_edges_subset {G : SimpleGraph V} [DecidableRel G.Adj]
    (P : Finpartition (Finset.univ : Finset V)) (ε δ : ℝ) :
    (Finset.univ ×ˢ Finset.univ).filter
      (fun xy : V × V => G.Adj xy.1 xy.2 ∧ ¬(G.regularityReduced P ε δ).Adj xy.1 xy.2) ⊆
      (P.nonUniforms G ε).biUnion (fun UV => UV.1 ×ˢ UV.2) ∪
      P.parts.biUnion Finset.offDiag ∪
      (P.sparsePairs G δ).biUnion (fun UV => G.interedges UV.1 UV.2) := by
  rintro ⟨x, y⟩
  simp only [Finset.mem_filter, SimpleGraph.regularityReduced_adj, not_and,
    not_exists, not_le, Finset.mem_biUnion, Finset.mem_union, Finset.mem_product,
    Prod.exists, Finset.mem_offDiag, and_imp, or_assoc, and_assoc,
    Finpartition.mk_mem_nonUniforms, Finpartition.mk_mem_sparsePairs,
    SimpleGraph.mem_interedges_iff]
  intro hx hy h h'
  replace h' := h' h
  obtain ⟨U, hU, hx⟩ := P.exists_mem hx
  obtain ⟨T, hT, hy⟩ := P.exists_mem hy
  obtain rfl | hUT := eq_or_ne U T
  · exact Or.inr (Or.inl ⟨U, hU, hx, hy, G.ne_of_adj h⟩)
  by_cases hreg : G.IsUniform ε U T
  · exact Or.inr (Or.inr ⟨U, T, hU, hT, hUT,
      h' _ hU _ hT hx hy hUT hreg, hx, hy, h⟩)
  · exact Or.inl ⟨U, T, hU, hT, hUT, hreg, hx, hy⟩

/-- The number of deleted edges is controlled independently by the
regularity parameter, the density threshold, and the diagonal blocks. -/
theorem regularity_edge_loss [Nonempty V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : Finpartition (Finset.univ : Finset V)} {ε δ η : ℝ}
    (hε : 0 < ε) (hδ : 0 ≤ δ) (hη : 0 < η)
    (hP : P.IsEquipartition) (hreg : P.IsUniform G ε)
    (hparts : 4 / η ≤ P.parts.card) :
    (G.edgeFinset.card : ℝ) - (G.regularityReduced P ε δ).edgeFinset.card <
      (2 * ε + 2 * δ + η / 4) * (Fintype.card V : ℝ) ^ 2 := by
  let A := (P.nonUniforms G ε).biUnion (fun UV => UV.1 ×ˢ UV.2)
  let B := P.parts.biUnion Finset.offDiag
  let C := (P.sparsePairs G δ).biUnion (fun UV => G.interedges UV.1 UV.2)
  have hcount : 2 * ((G.edgeFinset.card : ℝ) -
      (G.regularityReduced P ε δ).edgeFinset.card) <
      (4 * ε + 4 * δ + η / 2) * (Fintype.card V : ℝ) ^ 2 := by
    calc
      _ = (((Finset.univ ×ˢ Finset.univ).filter (fun xy : V × V =>
          G.Adj xy.1 xy.2 ∧ ¬(G.regularityReduced P ε δ).Adj xy.1 xy.2)).card : ℝ) := by
        rw [Finset.univ_product_univ, mul_sub, Finset.filter_and_not, Finset.cast_card_sdiff]
        · norm_cast
          rw [SimpleGraph.two_mul_card_edgeFinset, SimpleGraph.two_mul_card_edgeFinset]
        · gcongr with xy _
          exact fun hxy => SimpleGraph.regularityReduced_le hxy
      _ ≤ ((A ∪ B ∪ C).card : ℝ) := by
        exact_mod_cast Finset.card_le_card (unreduced_edges_subset P ε δ)
      _ ≤ ((A ∪ B).card : ℝ) + C.card := by exact_mod_cast Finset.card_union_le _ _
      _ ≤ (A.card : ℝ) + B.card + C.card := by
        gcongr
        exact_mod_cast Finset.card_union_le A B
      _ < 4 * ε * (Fintype.card V : ℝ) ^ 2 + B.card + C.card := by
        gcongr
        exact hP.sum_nonUniforms_lt Finset.univ_nonempty hε hreg
      _ ≤ 4 * ε * (Fintype.card V : ℝ) ^ 2 +
          η / 2 * (Fintype.card V : ℝ) ^ 2 +
          4 * δ * (Fintype.card V : ℝ) ^ 2 := by
        gcongr
        · exact hP.card_biUnion_offDiag_le hη hparts
        · exact hP.card_interedges_sparsePairs_le (G := G) hδ
      _ = _ := by ring
  nlinarith

/-- Total weight in a fiber of a finite map. -/
noncomputable def fiberMass {I : Type*} [Fintype I] (f : V → I) (p : V → ℝ)
    (i : I) : ℝ := by
  classical
  exact ∑ v : {v // f v = i}, p v

theorem probability_fiberMass {I : Type*} [Fintype I] (f : V → I)
    {p : V → ℝ} (hp : IsProbabilityWeight p) :
    IsProbabilityWeight (fiberMass f p) := by
  classical
  refine ⟨fun i => Finset.sum_nonneg (fun v _ => hp.1 v), ?_⟩
  unfold fiberMass
  exact (Fintype.sum_fiberwise f p).trans hp.2

/-- A blow-up's weighted edge mass is exactly that of its quotient with
fiber masses; no approximation or positive-fiber assumption is needed. -/
theorem edgeMass_comap {I : Type*} [Fintype I] (R : SimpleGraph I)
    (f : V → I) (p : V → ℝ) :
    edgeMass (R.comap f) p = edgeMass R (fiberMass f p) := by
  classical
  unfold edgeMass
  congr 1
  calc
    (∑ u, ∑ v, if (R.comap f).Adj u v then p u * p v else 0) =
        ∑ i, ∑ u : {u // f u = i},
          ∑ v, if R.Adj i (f v) then p u * p v else 0 := by
      rw [← Fintype.sum_fiberwise f]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro u _
      simp only [SimpleGraph.comap_adj, u.property]
    _ = ∑ i, ∑ u : {u // f u = i}, ∑ j,
        ∑ v : {v // f v = j}, if R.Adj i j then p u * p v else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro u _
      rw [← Fintype.sum_fiberwise f]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro v _
      simp only [v.property]
    _ = ∑ i, ∑ j, if R.Adj i j then fiberMass f p i * fiberMass f p j else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : R.Adj i j
      · simp only [h, ite_true, fiberMass, ← Finset.mul_sum, ← Finset.sum_mul]
      · simp [h]


/-- Uniform probability weights on a finite vertex type. -/
noncomputable def uniformWeight (V : Type*) [Fintype V] : V → ℝ :=
  fun _ => 1 / (Fintype.card V : ℝ)

theorem uniformWeight_probability [Nonempty V] :
    IsProbabilityWeight (uniformWeight V) := by
  have hn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  exact ⟨fun _ => by simp [uniformWeight], by simp [uniformWeight, hn]⟩

theorem edgeMass_one (G : SimpleGraph V) [DecidableRel G.Adj] :
    edgeMass G (fun _ => 1) = (G.edgeFinset.card : ℝ) := by
  classical
  have hsum : (∑ u : V, ∑ v : V, if G.Adj u v then (1 : ℝ) else 0) =
      ((Finset.univ.filter (fun uv : V × V => G.Adj uv.1 uv.2)).card : ℝ) := by
    calc
      _ = ∑ uv : V × V, if G.Adj uv.1 uv.2 then (1 : ℝ) else 0 := by
        simpa only [Finset.univ_product_univ] using
          (Finset.sum_product (Finset.univ : Finset V) (Finset.univ : Finset V)
            (fun uv : V × V => if G.Adj uv.1 uv.2 then (1 : ℝ) else 0)).symm
      _ = _ := by simp
  calc
    edgeMass G (fun _ => 1) =
        (∑ u : V, ∑ v : V, if G.Adj u v then (1 : ℝ) else 0) / 2 := by
      unfold edgeMass
      congr 1
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro v _
      by_cases h : G.Adj u v <;> simp [h]
    _ = _ := by
      rw [hsum, ← G.two_mul_card_edgeFinset]
      push_cast
      ring

theorem edgeMass_uniform (G : SimpleGraph V) [DecidableRel G.Adj] :
    edgeMass G (uniformWeight V) =
      (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ) ^ 2 := by
  have h := edgeMass_scale G (fun _ => 1) (1 / (Fintype.card V : ℝ))
  simp only [mul_one] at h
  change edgeMass G (fun _ => 1 / (Fintype.card V : ℝ)) = _
  rw [h, edgeMass_one]
  ring

/-- The unique cluster containing a vertex. -/
noncomputable def clusterOf (P : Finpartition (Finset.univ : Finset V)) (v : V) :
    P.parts := ⟨P.part v, P.part_mem.mpr (Finset.mem_univ v)⟩

@[simp] theorem clusterOf_eq_iff {P : Finpartition (Finset.univ : Finset V)}
    {v : V} {i : P.parts} : clusterOf P v = i ↔ v ∈ i.val := by
  rw [Subtype.ext_iff]
  exact P.part_eq_iff_mem i.property

/-- The weight of a cluster is its proportion of all vertices. -/
noncomputable def clusterWeight (P : Finpartition (Finset.univ : Finset V)) (i : P.parts) : ℝ :=
  (i.val.card : ℝ) / (Fintype.card V : ℝ)

theorem fiberMass_clusterOf (P : Finpartition (Finset.univ : Finset V)) :
    fiberMass (clusterOf P) (uniformWeight V) = clusterWeight P := by
  classical
  funext i
  have hc : Fintype.card {v // clusterOf P v = i} = i.val.card := by
    let e : {v // clusterOf P v = i} ≃ {v // v ∈ i.val} :=
      { toFun := fun v => ⟨v, clusterOf_eq_iff.mp v.property⟩
        invFun := fun v => ⟨v, clusterOf_eq_iff.mpr v.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact (Fintype.card_congr e).trans (Fintype.card_coe i.val)
  simp [fiberMass, uniformWeight, hc, clusterWeight, div_eq_mul_inv]

theorem clusterWeight_probability [Nonempty V]
    (P : Finpartition (Finset.univ : Finset V)) :
    IsProbabilityWeight (clusterWeight P) := by
  rw [← fiberMass_clusterOf]
  exact probability_fiberMass _ uniformWeight_probability

theorem clusterWeight_pos [Nonempty V]
    (P : Finpartition (Finset.univ : Finset V)) (i : P.parts) :
    0 < clusterWeight P i := by
  apply div_pos
  · exact_mod_cast Finset.card_pos.mpr (P.nonempty_of_mem_parts i.property)
  · exact_mod_cast Fintype.card_pos

/-- The regular, dense quotient graph of a partition. -/
noncomputable def clusterGraph (P : Finpartition (Finset.univ : Finset V))
    (G : SimpleGraph V) [DecidableRel G.Adj] (ε δ : ℝ) : SimpleGraph P.parts where
  Adj i j := i ≠ j ∧ G.IsUniform ε i.val j.val ∧ δ ≤ G.edgeDensity i.val j.val
  symm := ⟨fun i j h => ⟨h.1.symm, h.2.1.symm, by simpa only [SimpleGraph.edgeDensity_comm] using h.2.2⟩⟩
  loopless := ⟨fun i h => h.1 rfl⟩

theorem reduced_le_cluster_comap (P : Finpartition (Finset.univ : Finset V))
    (G : SimpleGraph V) [DecidableRel G.Adj] (ε δ : ℝ) :
    G.regularityReduced P ε δ ≤ (clusterGraph P G ε δ).comap (clusterOf P) := by
  rintro x y ⟨hxy, U, hU, T, hT, hx, hy, hUT, hreg, hd⟩
  have hx' : P.part x = U := P.part_eq_of_mem hU hx
  have hy' : P.part y = T := P.part_eq_of_mem hT hy
  change clusterOf P x ≠ clusterOf P y ∧ _ ∧ _
  refine ⟨?_, ?_, ?_⟩
  · intro heq
    exact hUT (hx'.symm.trans ((congrArg Subtype.val heq).trans hy'))
  · simpa only [clusterOf, hx', hy'] using hreg
  · simpa only [clusterOf, hx', hy'] using hd

theorem edgeMass_mono {G H : SimpleGraph V} {p : V → ℝ}
    (hp : ∀ v, 0 ≤ p v) (hGH : G ≤ H) : edgeMass G p ≤ edgeMass H p := by
  classical
  unfold edgeMass
  gcongr with u _ v _
  by_cases hG : G.Adj u v
  · simp [hG, hGH hG]
  · simp only [hG, ite_false]
    split_ifs
    · exact mul_nonneg (hp _) (hp _)
    · rfl

/-- The original graph's normalized edge count is bounded by the weighted
regular quotient, with three explicit error terms. -/
theorem edgeMass_le_cluster [Nonempty V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {P : Finpartition (Finset.univ : Finset V)} {ε δ η : ℝ}
    (hε : 0 < ε) (hδ : 0 ≤ δ) (hη : 0 < η)
    (hP : P.IsEquipartition) (hreg : P.IsUniform G ε)
    (hparts : 4 / η ≤ P.parts.card) :
    edgeMass G (uniformWeight V) <
      edgeMass (clusterGraph P G ε δ) (clusterWeight P) + (2*ε+2*δ+η/4) := by
  classical
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hloss := regularity_edge_loss hε hδ hη hP hreg hparts
  have he : edgeMass G (uniformWeight V) <
      edgeMass (G.regularityReduced P ε δ) (uniformWeight V) + (2*ε+2*δ+η/4) := by
    rw [edgeMass_uniform, edgeMass_uniform]
    apply (div_lt_iff₀ (sq_pos_of_pos hn)).mpr
    have hc : ((G.regularityReduced P ε δ).edgeFinset.card : ℝ) /
        (Fintype.card V : ℝ)^2 * (Fintype.card V : ℝ)^2 =
        ((G.regularityReduced P ε δ).edgeFinset.card : ℝ) :=
      div_mul_cancel₀ _ (ne_of_gt (sq_pos_of_pos hn))
    nlinarith
  apply he.trans_le
  gcongr
  calc
    edgeMass (G.regularityReduced P ε δ) (uniformWeight V) ≤
        edgeMass ((clusterGraph P G ε δ).comap (clusterOf P)) (uniformWeight V) :=
      edgeMass_mono uniformWeight_probability.1 (reduced_le_cluster_comap P G ε δ)
    _ = _ := by rw [edgeMass_comap, fiberMass_clusterOf]

end DensityHS.Regularity
