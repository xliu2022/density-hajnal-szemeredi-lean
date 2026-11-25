module

public import DensityHS.Rainbow.ColoredGraph
public import DensityHS.Rainbow.Digraph
public import Mathlib.Tactic

/-!
# Direct counting of bad rainbow embeddings

The argument counts transversal embeddings of the original directed tile,
not improperly coloured copies of an entire multipartite blowup.  It uses
only outgoing colour uniqueness and the leaf property of monochromatic
star forests.

Formalization author and maintainer: Xizhi Liu.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace DensityHS.Rainbow

variable {V K I : Type*} {G : SimpleGraph V}

/-- The first endpoint is a leaf in the monochromatic component of the edge. -/
def IsColorLeaf (C : G.EdgeLabeling K) (x y : V) : Prop :=
  ∀ z, G.Adj x z → edgeColor C x z = edgeColor C x y → z = y

/-- The local characterization of a monochromatic star forest: every edge
has an endpoint of monochromatic degree one. -/
def HasStarColorClasses (C : G.EdgeLabeling K) : Prop :=
  ∀ ⦃x y : V⦄, G.Adj x y → IsColorLeaf C x y ∨ IsColorLeaf C y x

def OutgoingColorsDistinct (D : Digraph V) (C : G.EdgeLabeling K) : Prop :=
  ∀ ⦃v x y : V⦄, D.Arc v x → D.Arc v y →
    edgeColor C v x = edgeColor C v y → x = y

noncomputable def mapFamily [Fintype I] [Fintype V]
    (P : (I → V) → Prop) : Finset (I → V) := by
  classical
  exact Finset.univ.filter P

theorem mem_mapFamily [Fintype I] [Fintype V] {P : (I → V) → Prop} {f : I → V} :
    f ∈ mapFamily P ↔ P f := by
  classical
  simp [mapFamily]

/-- A family whose missing coordinate is determined by all the other
coordinates has at most `n^(r−1)` members. -/
theorem mapFamily_card_le_of_coordinate_determined [Fintype I] [Fintype V]
    (P : (I → V) → Prop) (j : I)
    (hdet : ∀ f g, P f → P g → (∀ i, i ≠ j → f i = g i) → f j = g j) :
    (mapFamily P).card ≤ Fintype.card V ^ (Fintype.card I - 1) := by
  classical
  let restrict : mapFamily P → (↥(Finset.univ.erase j : Finset I) → V) :=
    fun f i => f.1 i.1
  have hinj : Function.Injective restrict := by
    intro f g hfg
    have hcoord : ∀ i, i ≠ j → f.1 i = g.1 i := by
      intro i hij
      exact congrFun hfg ⟨i, by simp [hij]⟩
    apply Subtype.ext
    funext i
    by_cases hij : i = j
    · subst i
      exact hdet f g (mem_mapFamily.mp f.2) (mem_mapFamily.mp g.2) hcoord
    · exact hcoord i hij
  have hcard := Fintype.card_le_of_injective restrict hinj
  simpa using hcard

noncomputable def monochromaticPathMaps [Fintype I] [Fintype V]
    (D : Digraph V) (C : G.EdgeLabeling K) (i j k : I) : Finset (I → V) :=
  mapFamily fun f => i ≠ k ∧ j ≠ k ∧ D.Arc (f i) (f j) ∧ D.Arc (f j) (f k) ∧
    edgeColor C (f i) (f j) = edgeColor C (f j) (f k)

theorem monochromaticPathMaps_card_le [Fintype I] [Fintype V]
    {D : Digraph V} {C : G.EdgeLabeling K} (hout : OutgoingColorsDistinct D C)
    (i j k : I) :
    (monochromaticPathMaps D C i j k).card ≤
      Fintype.card V ^ (Fintype.card I - 1) := by
  classical
  apply mapFamily_card_le_of_coordinate_determined _ k
  intro f g hf hg heq
  rcases hf with ⟨hik, hjk, _, hfjk, hfc⟩
  rcases hg with ⟨_, _, _, hgjk, hgc⟩
  have hfi := heq i hik
  have hfj := heq j hjk
  apply hout hfjk (by simpa only [hfj] using hgjk)
  calc
    edgeColor C (f j) (f k) = edgeColor C (f i) (f j) := hfc.symm
    _ = edgeColor C (g i) (g j) := by rw [hfi, hfj]
    _ = edgeColor C (g j) (g k) := hgc
    _ = edgeColor C (f j) (g k) := by rw [hfj]

noncomputable def monochromaticLeafMaps [Fintype I] [Fintype V]
    (C : G.EdgeLabeling K) (i j k l : I) : Finset (I → V) :=
  mapFamily fun f => i ≠ l ∧ j ≠ l ∧ k ≠ l ∧ G.Adj (f k) (f l) ∧
    IsColorLeaf C (f k) (f l) ∧ edgeColor C (f i) (f j) = edgeColor C (f k) (f l)

theorem monochromaticLeafMaps_card_le [Fintype I] [Fintype V]
    (C : G.EdgeLabeling K) (i j k l : I) :
    (monochromaticLeafMaps C i j k l).card ≤
      Fintype.card V ^ (Fintype.card I - 1) := by
  classical
  apply mapFamily_card_le_of_coordinate_determined _ l
  intro f g hf hg heq
  rcases hf with ⟨hil, hjl, hkl, _, hleaf, hfc⟩
  rcases hg with ⟨_, _, _, hgkl, _, hgc⟩
  have hfi := heq i hil
  have hfj := heq j hjl
  have hfk := heq k hkl
  apply (hleaf (g l) (by simpa only [hfk] using hgkl) ?_).symm
  calc
    edgeColor C (f k) (g l) = edgeColor C (g k) (g l) := by rw [hfk]
    _ = edgeColor C (g i) (g j) := hgc.symm
    _ = edgeColor C (f i) (f j) := by rw [hfi, hfj]
    _ = edgeColor C (f k) (f l) := hfc

/-- In an actual `(r,r−2)` tile, a vertex can miss at most one outgoing
arc to the other tile vertices. -/
theorem tile_two_outgoing [Fintype V] [DecidableEq V] {r : ℕ} (hr : 3 ≤ r)
    {D : Digraph V} {S : Finset V} (hS : D.IsTile r S)
    {v x y : V} (hv : v ∈ S) (hx : x ∈ S) (hy : y ∈ S)
    (hvx : v ≠ x) (hvy : v ≠ y) (hxy : x ≠ y) :
    D.Arc v x ∨ D.Arc v y := by
  classical
  by_contra h
  push Not at h
  have hsmall : ({v, x, y} : Finset V).card = 3 := by
    simp [hvx, hvy, hxy]
  have hdisj : Disjoint ({v, x, y} : Finset V) (S.filter (D.Arc v)) := by
    apply Finset.disjoint_left.mpr
    intro z hz hzout
    have hVz := (Finset.mem_filter.mp hzout).2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hz | hz | hz
    · subst z
      exact D.loopless v hVz
    · subst z
      exact h.1 hVz
    · subst z
      exact h.2 hVz
  have hsub : ({v, x, y} : Finset V) ∪ S.filter (D.Arc v) ⊆ S :=
    Finset.union_subset (by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with hz | hz | hz <;> subst z
      · exact hv
      · exact hx
      · exact hy) (Finset.filter_subset _ _)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hsmall, hS.1] at hcard
  have hdegree := hS.2.2 v hv
  omega

noncomputable def badTileMaps [Fintype V] [DecidableEq V]
    (r : ℕ) (D : Digraph V) (C : G.EdgeLabeling K) : Finset (Fin r → V) :=
  mapFamily fun f => Function.Injective f ∧ D.IsTile r (Finset.univ.image f) ∧
    ¬ IsRainbowOn C (Finset.univ.image f)

/-- Every bad transversal tile map has either a directed monochromatic
path collision or a disjoint-edge collision with a monochromatic leaf. -/
theorem badTileMap_has_collision [Fintype V] [DecidableEq V]
    {r : ℕ} (hr : 3 ≤ r) {D : Digraph V} {C : G.EdgeLabeling K}
    (hout : OutgoingColorsDistinct D C) (hstar : HasStarColorClasses C)
    {f : Fin r → V} (hf : f ∈ badTileMaps r D C) :
    (∃ t : Fin r × (Fin r × Fin r),
      f ∈ monochromaticPathMaps D C t.1 t.2.1 t.2.2) ∨
    (∃ q : Fin r × (Fin r × (Fin r × Fin r)),
      f ∈ monochromaticLeafMaps C q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  classical
  rcases mem_mapFamily.mp hf with ⟨hinj, htile, hbad⟩
  have hmem (i : Fin r) : f i ∈ Finset.univ.image f :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hwedge (i j k : Fin r) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
      (hc : edgeColor C (f i) (f j) = edgeColor C (f i) (f k)) :
      ∃ t : Fin r × (Fin r × Fin r),
        f ∈ monochromaticPathMaps D C t.1 t.2.1 t.2.2 := by
    have hvo := tile_two_outgoing hr htile (hmem i) (hmem j) (hmem k)
      (hinj.ne hij) (hinj.ne hik) (hinj.ne hjk)
    rcases hvo with hijout | hikout
    · have hnik : ¬D.Arc (f i) (f k) := fun h => (hinj.ne hjk) (hout hijout h hc)
      have hki : D.Arc (f k) (f i) := by
        rcases htile.2.1 (hmem i) (hmem k) (hinj.ne hik) with h | h
        · exact False.elim (hnik h)
        · exact h
      refine ⟨(k, i, j), mem_mapFamily.mpr ⟨hjk.symm, hij, hki, hijout, ?_⟩⟩
      exact (edgeColor_comm C (f k) (f i)).trans hc.symm
    · have hnij : ¬D.Arc (f i) (f j) := fun h => (hinj.ne hjk) (hout h hikout hc)
      have hji : D.Arc (f j) (f i) := by
        rcases htile.2.1 (hmem i) (hmem j) (hinj.ne hij) with h | h
        · exact False.elim (hnij h)
        · exact h
      refine ⟨(j, i, k), mem_mapFamily.mpr ⟨hjk, hik, hji, hikout, ?_⟩⟩
      exact (edgeColor_comm C (f j) (f i)).trans hc
  unfold IsRainbowOn at hbad
  push Not at hbad
  obtain ⟨x, y, u, v, hx, hy, hu, hv, hxy, huv, hc, hne⟩ := hbad
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hv
  have hij : i ≠ j := fun h => hxy.ne (congrArg f h)
  have hkl : k ≠ l := fun h => huv.ne (congrArg f h)
  by_cases hik : i = k
  · subst k
    have hjl : j ≠ l := by
      intro h
      subst l
      exact hne rfl
    exact Or.inl (hwedge i j l hij hkl hjl hc)
  by_cases hil : i = l
  · subst l
    have hjk : j ≠ k := by
      intro h
      subst k
      exact hne Sym2.eq_swap
    exact Or.inl (hwedge i j k hij hik hjk
      (hc.trans (edgeColor_comm C (f k) (f i))))
  by_cases hjk : j = k
  · subst k
    exact Or.inl (hwedge j i l hij.symm hkl hil
      ((edgeColor_comm C (f j) (f i)).trans hc))
  by_cases hjl : j = l
  · subst l
    exact Or.inl (hwedge j i k hij.symm hjk hik
      ((edgeColor_comm C (f j) (f i)).trans
        (hc.trans (edgeColor_comm C (f k) (f j)))))
  rcases hstar huv with hleaf | hleaf
  · exact Or.inr ⟨(i, j, k, l), mem_mapFamily.mpr ⟨hil, hjl, hkl, huv, hleaf, hc⟩⟩
  · exact Or.inr ⟨(i, j, l, k), mem_mapFamily.mpr
      ⟨hik, hjk, hkl.symm, huv.symm, hleaf, hc.trans (edgeColor_comm C (f k) (f l))⟩⟩

/-- Explicit corrected bad-embedding bound, valid for every finite coloured
graph and every supporting digraph with outgoing colour uniqueness. -/
theorem badTileMaps_card_le [Fintype V] [DecidableEq V]
    {r : ℕ} (hr : 3 ≤ r) {D : Digraph V} {C : G.EdgeLabeling K}
    (hout : OutgoingColorsDistinct D C) (hstar : HasStarColorClasses C) :
    (badTileMaps r D C).card ≤ (r ^ 3 + r ^ 4) * Fintype.card V ^ (r - 1) := by
  classical
  let paths := Finset.univ.biUnion fun t : Fin r × (Fin r × Fin r) =>
    monochromaticPathMaps D C t.1 t.2.1 t.2.2
  let leaves := Finset.univ.biUnion fun q : Fin r × (Fin r × (Fin r × Fin r)) =>
    monochromaticLeafMaps C q.1 q.2.1 q.2.2.1 q.2.2.2
  have hsub : badTileMaps r D C ⊆ paths ∪ leaves := by
    intro f hf
    rcases badTileMap_has_collision hr hout hstar hf with ⟨t, ht⟩ | ⟨q, hq⟩
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨t, Finset.mem_univ _, ht⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨q, Finset.mem_univ _, hq⟩)
  have hpaths : paths.card ≤ r ^ 3 * Fintype.card V ^ (r - 1) := by
    apply Finset.card_biUnion_le.trans
    calc
      _ ≤ ∑ _t : Fin r × (Fin r × Fin r), Fintype.card V ^ (r - 1) := by
        apply Finset.sum_le_sum
        intro t _
        simpa using monochromaticPathMaps_card_le hout t.1 t.2.1 t.2.2
      _ = r ^ 3 * Fintype.card V ^ (r - 1) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
        ring
  have hleaves : leaves.card ≤ r ^ 4 * Fintype.card V ^ (r - 1) := by
    apply Finset.card_biUnion_le.trans
    calc
      _ ≤ ∑ _q : Fin r × (Fin r × (Fin r × Fin r)), Fintype.card V ^ (r - 1) := by
        apply Finset.sum_le_sum
        intro q _
        simpa using monochromaticLeafMaps_card_le C q.1 q.2.1 q.2.2.1 q.2.2.2
      _ = r ^ 4 * Fintype.card V ^ (r - 1) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
        ring
  calc
    _ ≤ (paths ∪ leaves).card := Finset.card_le_card hsub
    _ ≤ paths.card + leaves.card := Finset.card_union_le _ _
    _ ≤ r ^ 3 * Fintype.card V ^ (r - 1) + r ^ 4 * Fintype.card V ^ (r - 1) :=
      Nat.add_le_add hpaths hleaves
    _ = _ := by ring

/-- A concrete family of more embeddings than the bad-embedding bound
contains a genuine rainbow clique in the original coloured graph. -/
theorem exists_rainbow_tile_of_many_maps [Fintype V] [DecidableEq V]
    {r : ℕ} (hr : 3 ≤ r) {D : Digraph V} {C : G.EdgeLabeling K}
    (hbase : D.baseGraph ≤ G) (hout : OutgoingColorsDistinct D C)
    (hstar : HasStarColorClasses C) (F : Finset (Fin r → V))
    (hF : ∀ f ∈ F, Function.Injective f ∧ D.IsTile r (Finset.univ.image f))
    (hmany : (r ^ 3 + r ^ 4) * Fintype.card V ^ (r - 1) < F.card) :
    ∃ f ∈ F, IsRainbowClique r C (Finset.univ.image f) := by
  classical
  have hlt := (badTileMaps_card_le hr hout hstar).trans_lt hmany
  obtain ⟨f, hf, hfnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  obtain ⟨hinj, htile⟩ := hF f hf
  refine ⟨f, hf, ⟨htile.2.1.mono hbase, htile.1⟩, ?_⟩
  by_contra hbad
  exact hfnot (mem_mapFamily.mpr ⟨hinj, htile, hbad⟩)

end DensityHS.Rainbow
