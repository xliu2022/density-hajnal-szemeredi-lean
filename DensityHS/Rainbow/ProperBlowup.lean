module

public import DensityHS.Rainbow.ColoredGraph
public import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite
public import Mathlib.Data.Fin.Tuple.Embedding
public import Mathlib.Tactic

/-!
# Rainbow transversals in properly coloured complete multipartite graphs

The proof is a direct finite greedy argument.  A rainbow set of size `j`
forbids at most `j³` vertices of the next class: choose the old endpoint and
an ordered pair defining an old colour, and use properness to get at most one
candidate for that triple.

Formalization author and maintainer: Xizhi Liu.
-/

@[expose] public section

open Finset

namespace DensityHS.Rainbow

variable {V K : Type*} {G : SimpleGraph V}

noncomputable def badCandidates (C : G.EdgeLabeling K) (S T : Finset V) : Finset V := by
  classical
  exact T.filter fun w => ∃ t ∈ S ×ˢ (S ×ˢ S),
    edgeColor C w t.1 = edgeColor C t.2.1 t.2.2

theorem badCandidates_card_le {C : G.EdgeLabeling K} (hp : IsProper C)
    (S T : Finset V) (hcross : ∀ w ∈ T, ∀ v ∈ S, G.Adj w v) :
    (badCandidates C S T).card ≤ S.card ^ 3 := by
  classical
  have hex (w : badCandidates C S T) :
      ∃ t : S ×ˢ (S ×ˢ S), edgeColor C w t.1.1 = edgeColor C t.1.2.1 t.1.2.2 := by
    obtain ⟨_, t, ht, hc⟩ := Finset.mem_filter.mp w.2
    exact ⟨⟨t, ht⟩, hc⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro w w' hww'
    have hv : (f w).1.1 ∈ S := (Finset.mem_product.mp (f w).2).1
    have hw : (w : V) ∈ T := (Finset.mem_filter.mp w.2).1
    have hw' : (w' : V) ∈ T := (Finset.mem_filter.mp w'.2).1
    have hcol : edgeColor C w (f w).1.1 = edgeColor C w' (f w).1.1 := by
      rw [hf w]
      simpa only [hww'] using (hf w').symm
    apply Subtype.ext
    apply hp (hcross w hw (f w).1.1 hv).symm (hcross w' hw' (f w).1.1 hv).symm
    exact (edgeColor_comm C (f w).1.1 w).trans
      (hcol.trans (edgeColor_comm C w' (f w).1.1))
  have hcard := Fintype.card_le_of_injective f hinj
  simpa [Finset.card_product, pow_succ, mul_assoc] using hcard

/-- A class with more than `|S|³` vertices supplies a new vertex with no
collision against any old edge colour. -/
theorem exists_fresh_vertex {C : G.EdgeLabeling K} (hp : IsProper C)
    (S T : Finset V) (hcross : ∀ w ∈ T, ∀ v ∈ S, G.Adj w v)
    (hsize : S.card ^ 3 < T.card) :
    ∃ w ∈ T, w ∉ S ∧ ∀ y ∈ S, ∀ u ∈ S, ∀ v ∈ S,
      edgeColor C w y ≠ edgeColor C u v := by
  classical
  have hlt := (badCandidates_card_le hp S T hcross).trans_lt hsize
  obtain ⟨w, hw, hwbad⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨w, hw, ?_, ?_⟩
  · intro hwS
    exact (hcross w hw w hwS).ne rfl
  · intro y hy u hu v hv hc
    apply hwbad
    exact Finset.mem_filter.mpr ⟨hw, (y, u, v),
      Finset.mem_product.mpr ⟨hy, Finset.mem_product.mpr ⟨hu, hv⟩⟩, hc⟩

/-- The exact greedy extension, preserving the ordinary clique and the
rainbow edge property simultaneously. -/
theorem exists_rainbow_extension [DecidableEq V] {C : G.EdgeLabeling K}
    (hp : IsProper C) {j : ℕ} {S : Finset V} (hS : IsRainbowClique j C S)
    (T : Finset V) (hcross : ∀ w ∈ T, ∀ v ∈ S, G.Adj w v)
    (hsize : j ^ 3 < T.card) :
    ∃ w ∈ T, w ∉ S ∧ IsRainbowClique (j + 1) C (insert w S) := by
  have hcard : S.card = j := hS.1.card_eq
  obtain ⟨w, hw, hwS, hfresh⟩ := exists_fresh_vertex hp S T hcross (by rwa [hcard])
  refine ⟨w, hw, hwS, ⟨?_, ?_⟩, hS.2.insert hp hfresh⟩
  · simpa only [Finset.coe_insert] using hS.1.isClique.insert
      (fun v hv _ => hcross w hw v hv)
  · rw [Finset.card_insert_of_notMem hwS, hcard]

/-- Every properly coloured complete multipartite graph whose `r` classes
each contain at least `r³` vertices has a rainbow transversal `r`-clique. -/
theorem exists_rainbow_transversal {C : G.EdgeLabeling K} (hp : IsProper C)
    (r : ℕ) (P : Fin r → Finset V)
    (hsize : ∀ i, r ^ 3 ≤ (P i).card)
    (hcross : ∀ i j, i ≠ j → ∀ x ∈ P i, ∀ y ∈ P j, G.Adj x y) :
    ∃ e : Fin r ↪ V, (∀ i, e i ∈ P i) ∧
      IsRainbowClique r C (Finset.univ.map e) := by
  classical
  induction r with
  | zero =>
    let e : Fin 0 ↪ V := ⟨Fin.elim0, fun i => Fin.elim0 i⟩
    refine ⟨e, fun i => Fin.elim0 i, ?_⟩
    simpa using isRainbowClique_empty C
  | succ n ih =>
    have hpow : n ^ 3 < (n + 1) ^ 3 :=
      Nat.pow_lt_pow_left (Nat.lt_succ_self n) (by decide)
    obtain ⟨e, he, hS⟩ := ih (fun i => P i.succ)
      (fun i => hpow.le.trans (hsize i.succ))
      (fun i j hij => hcross i.succ j.succ (fun h => hij (Fin.succ_injective n h)))
    have hcross' : ∀ w ∈ P 0, ∀ v ∈ Finset.univ.map e, G.Adj w v := by
      intro w hw v hv
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hv
      exact hcross 0 i.succ (Fin.succ_ne_zero i).symm w hw (e i) (he i)
    obtain ⟨w, hw, hwS, hwcl⟩ := exists_rainbow_extension hp hS (P 0) hcross'
      (hpow.trans_le (hsize 0))
    have hwrange : w ∉ Set.range e := by
      rintro ⟨i, rfl⟩
      exact hwS (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    let E : Fin (n + 1) ↪ V := Fin.Embedding.cons e hwrange
    refine ⟨E, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [E] using hw
      · simpa [E] using he j
    · have hmap : Finset.univ.map E = insert w (Finset.univ.map e) := by
        apply Finset.coe_injective
        simp only [Finset.coe_map, Finset.coe_univ, Set.image_univ, Finset.coe_insert]
        exact Fin.range_cons w e
      rw [hmap]
      exact hwcl

/-- The balanced complete multipartite graph in the usual statement of the
proper-blowup lemma, with an actual rainbow clique in that graph. -/
theorem proper_completeEquipartite_has_rainbow_clique (r : ℕ)
    (C : (SimpleGraph.completeEquipartiteGraph r (r ^ 3)).EdgeLabeling K)
    (hp : IsProper C) :
    ∃ S : Finset (Fin r × Fin (r ^ 3)), IsRainbowClique r C S := by
  classical
  let P : Fin r → Finset (Fin r × Fin (r ^ 3)) :=
    fun i => Finset.univ.image fun j => (i, j)
  obtain ⟨e, _, he⟩ := exists_rainbow_transversal hp r P
    (fun i => by
      have hinj : Function.Injective (fun j : Fin (r ^ 3) => (i, j)) :=
        fun _ _ h => (Prod.mk.inj h).2
      dsimp [P]
      rw [Finset.card_image_of_injective _ hinj]
      simp)
    (by
      intro i j hij x hx y hy
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hy
      exact hij)
  exact ⟨Finset.univ.map e, he⟩

end DensityHS.Rainbow
