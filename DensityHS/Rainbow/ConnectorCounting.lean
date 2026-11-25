module

public import DensityHS.Rainbow.ConnectorProper

/-!
# Quantitative common rainbow connectors

The dense auxiliary double graph supplies many labelled cliques.  The two
proper root extensions have only a lower-order number of colour collisions,
so deleting these collisions leaves actual common rainbow connectors.

Formalization author and maintainer: Xizhi Liu.
-/

@[expose] public section

open Finset

namespace DensityHS.Rainbow

attribute [local instance] Classical.propDecidable

variable {V K : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {C : G.EdgeLabeling K} {D : Digraph V}

noncomputable def commonConnectorMaps (t : ℕ) (C : G.EdgeLabeling K) (x y : V) :
    Finset (Fin t → V) :=
  mapFamily fun f => Function.Injective f ∧
    IsCommonConnector (t + 1) C x y (univ.image f)

theorem commonConnectorMaps_card_lower {t s : ℕ} (ht : 2 ≤ t) (hs : 0 < s)
    (hbase : D.baseGraph ≤ G) (hout : OutgoingColorsDistinct D C)
    (x y : V) {ε : ℝ} (hε : 0 < ε)
    (hsε : (s : ℝ)⁻¹ ≤ ε / 2) (hlarge : 4 ≤ ε * Fintype.card V)
    (hdeg : ∀ v, (1 - 1 / (2 * (t : ℝ)) + ε) * Fintype.card V ≤
      (D.outDegree v : ℝ)) :
    (ε / 2) / (s : ℝ) ^ t * ((commonOutSet D x y).card : ℝ) ^ t -
      (2 * (t + 1) ^ 3 * t * Fintype.card V ^ (t - 1) : ℕ) ≤
      ((commonConnectorMaps t C x y).card : ℝ) := by
  classical
  let Z := commonOutSet D x y
  let H := ((rootCompatibleDigraph D C x y).induce Z).doubleGraph
  obtain ⟨hZ, hdensity⟩ := commonConnector_density ht hout x y hε hlarge hdeg
  letI : Nonempty Z := ⟨⟨hZ.choose, hZ.choose_spec⟩⟩
  have hsup := finite_clique_supersaturation ht hs (by linarith : 0 < ε / 2) hsε H
    (by simpa only [H, Z, Fintype.card_coe] using hdensity)
  simp only [Fintype.card_coe] at hsup
  let liftMap : (Fin t → Z) → (Fin t → V) := fun f i => (f i).1
  have hlift : Function.Injective liftMap := by
    intro f g hfg
    funext i
    exact Subtype.ext (congrFun hfg i)
  let F := (labelledCliqueMaps t H).image liftMap
  have hFcard : F.card = (labelledCliqueMaps t H).card := card_image_of_injective _ hlift
  have hFproperty (f : Fin t → V) (hf : f ∈ F) : Function.Injective f ∧
      univ.image f ⊆ Z ∧
      (rootCompatibleDigraph D C x y).doubleGraph.IsNClique t (univ.image f) := by
    obtain ⟨g, hg, rfl⟩ := mem_image.mp hf
    have hpair : ∀ i j, i ≠ j →
        (rootCompatibleDigraph D C x y).doubleGraph.Adj (liftMap g i) (liftMap g j) := by
      intro i j hij
      exact mem_labelledCliqueMaps.mp hg i j hij
    refine ⟨cliqueMap_injective hpair, ?_, isNClique_image_of_pairwise_adj hpair⟩
    intro v hv
    obtain ⟨i, _, rfl⟩ := mem_image.mp hv
    exact (g i).2
  let CX := restrictColor C (commonLeftGraph_le (C := C) hbase x y)
  let CY := restrictColor C (commonRightGraph_le (C := C) hbase x y)
  let BX := rootedNonRainbowMaps t CX x
  let BY := rootedNonRainbowMaps t CY y
  have hBX := rootedNonRainbowMaps_card_le (r := t) (commonLeftGraph_proper hbase hout x y) x
  have hBY := rootedNonRainbowMaps_card_le (r := t) (commonRightGraph_proper hbase hout x y) y
  have hsub : F ⊆ commonConnectorMaps t C x y ∪ (BX ∪ BY) := by
    intro f hf
    obtain ⟨hinj, hSZ, hcl⟩ := hFproperty f hf
    have hxS : x ∉ univ.image f := fun hx => (roots_not_mem_commonOutSet D x y).1 (hSZ hx)
    have hyS : y ∉ univ.image f := fun hy => (roots_not_mem_commonOutSet D x y).2 (hSZ hy)
    have hclX : (commonLeftGraph D C x y).IsNClique (t + 1)
        (Insert.insert x (univ.image f)) :=
      attachRootGraph_clique hcl hSZ (roots_not_mem_commonOutSet D x y).1
    have hclY : (commonRightGraph D C x y).IsNClique (t + 1)
        (Insert.insert y (univ.image f)) :=
      attachRootGraph_clique hcl hSZ (roots_not_mem_commonOutSet D x y).2
    by_cases hx : IsRainbowOn CX (Insert.insert x (univ.image f))
    · by_cases hy : IsRainbowOn CY (Insert.insert y (univ.image f))
      · apply mem_union_left
        apply mem_mapFamily.mpr
        exact ⟨hinj, hxS, hyS,
          (show IsRainbowClique (t + 1) CX _ from ⟨hclX, hx⟩).of_restrict,
          (show IsRainbowClique (t + 1) CY _ from ⟨hclY, hy⟩).of_restrict⟩
      · apply mem_union_right
        apply mem_union_right
        apply mem_mapFamily.mpr
        simpa only [rootedValue_image] using hy
    · apply mem_union_right
      apply mem_union_left
      apply mem_mapFamily.mpr
      simpa only [rootedValue_image] using hx
  have hnat : F.card ≤ (commonConnectorMaps t C x y).card +
      2 * (t + 1) ^ 3 * t * Fintype.card V ^ (t - 1) := by
    have h₁ := (card_le_card hsub).trans (card_union_le _ _)
    have h₂ := card_union_le BX BY
    change BX.card ≤ (t + 1) ^ 3 * t * Fintype.card V ^ (t - 1) at hBX
    change BY.card ≤ (t + 1) ^ 3 * t * Fintype.card V ^ (t - 1) at hBY
    calc
      F.card ≤ (commonConnectorMaps t C x y).card +
          (t + 1) ^ 3 * t * Fintype.card V ^ (t - 1) +
          (t + 1) ^ 3 * t * Fintype.card V ^ (t - 1) := by omega
      _ = _ := by ring
  have hreal : (F.card : ℝ) ≤ ((commonConnectorMaps t C x y).card : ℝ) +
      ((2 * (t + 1) ^ 3 * t * Fintype.card V ^ (t - 1) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  rw [hFcard] at hreal
  dsimp only [Z] at hsup
  linarith

end DensityHS.Rainbow
