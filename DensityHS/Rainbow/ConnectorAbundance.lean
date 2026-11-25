module

public import DensityHS.Rainbow.ConnectorCounting

/-!
# Uniform abundance of common connectors and rainbow base cliques

The explicit lower-order collision loss is absorbed into a fixed positive
coefficient once the graph order satisfies a concrete linear inequality.

Formalization author and maintainer: Xizhi Liu.
-/

@[expose] public section

open Finset

namespace DensityHS.Rainbow

attribute [local instance] Classical.propDecidable

variable {V K : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {C : G.EdgeLabeling K} {D : Digraph V}

theorem commonOutSet_half_card {t : ℕ} (ht : 2 ≤ t) {ε : ℝ} (hε : 0 ≤ ε)
    (hdeg : ∀ v, (1 - 1 / (2 * (t : ℝ)) + ε) * Fintype.card V ≤
      (D.outDegree v : ℝ)) (x y : V) :
    (Fintype.card V : ℝ) / 2 ≤ ((commonOutSet D x y).card : ℝ) := by
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have hfrac : 1 / (2 * (t : ℝ)) ≤ (1 : ℝ) / 4 := by
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    linarith
  have hcoef : (3 : ℝ) / 4 ≤ 1 - 1 / (2 * (t : ℝ)) + ε := by linarith
  have hmul := mul_le_mul_of_nonneg_right hcoef (show (0 : ℝ) ≤ Fintype.card V by positivity)
  have hx := hdeg x
  have hy := hdeg y
  have hz := commonOutSet_card_lower D x y
  linarith

noncomputable def connectorCoefficient (t s : ℕ) (ε : ℝ) : ℝ :=
  ε / (4 * (2 * (s : ℝ)) ^ t)

theorem connectorCoefficient_pos {t s : ℕ} (hs : 0 < s) {ε : ℝ} (hε : 0 < ε) :
    0 < connectorCoefficient t s ε := by unfold connectorCoefficient; positivity

theorem commonConnectorMaps_abundant {t s : ℕ} (ht : 2 ≤ t) (hs : 0 < s)
    (hbase : D.baseGraph ≤ G) (hout : OutgoingColorsDistinct D C)
    (x y : V) {ε : ℝ} (hε : 0 < ε)
    (hsε : (s : ℝ)⁻¹ ≤ ε / 2) (hlarge : 4 ≤ ε * Fintype.card V)
    (herror : (2 * (t + 1) ^ 3 * t : ℕ) ≤
      connectorCoefficient t s ε * (Fintype.card V : ℝ))
    (hdeg : ∀ v, (1 - 1 / (2 * (t : ℝ)) + ε) * Fintype.card V ≤
      (D.outDegree v : ℝ)) :
    connectorCoefficient t s ε * (Fintype.card V : ℝ) ^ t ≤
      ((commonConnectorMaps t C x y).card : ℝ) := by
  have hlower := commonConnectorMaps_card_lower ht hs hbase hout x y hε hsε hlarge hdeg
  have hhalf := commonOutSet_half_card ht hε.le hdeg x y
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ Fintype.card V / 2) hhalf t
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hcoef : 0 ≤ (ε / 2) / (s : ℝ) ^ t := by positivity
  have hmain := mul_le_mul_of_nonneg_left hpow hcoef
  have hid : (ε / 2) / (s : ℝ) ^ t * ((Fintype.card V : ℝ) / 2) ^ t =
      2 * connectorCoefficient t s ε * (Fintype.card V : ℝ) ^ t := by
    unfold connectorCoefficient
    rw [div_pow, mul_pow]
    field_simp
    ring
  rw [hid] at hmain
  have ht1 : 1 ≤ t := by omega
  have hnpow : (Fintype.card V : ℝ) * (Fintype.card V : ℝ) ^ (t - 1) =
      (Fintype.card V : ℝ) ^ t := by
    rw [← pow_succ', Nat.sub_add_cancel ht1]
  have herror' := mul_le_mul_of_nonneg_right herror
    (show 0 ≤ (Fintype.card V : ℝ) ^ (t - 1) by positivity)
  have herr : ((2 * (t + 1) ^ 3 * t * Fintype.card V ^ (t - 1) : ℕ) : ℝ) ≤
      connectorCoefficient t s ε * (Fintype.card V : ℝ) ^ t := by
    simpa only [Nat.cast_mul, Nat.cast_pow, mul_assoc, hnpow] using herror'
  linarith

noncomputable def rainbowCliqueMaps (r : ℕ) (C : G.EdgeLabeling K) : Finset (Fin r → V) :=
  mapFamily fun f => Function.Injective f ∧ IsRainbowClique r C (univ.image f)

theorem rainbowCliqueMaps_card_lower_of_connectors {t : ℕ} {β : ℝ}
    (hconn : ∀ x : V, β * (Fintype.card V : ℝ) ^ t ≤
      ((commonConnectorMaps t C x x).card : ℝ)) :
    β * (Fintype.card V : ℝ) ^ (t + 1) ≤
      ((rainbowCliqueMaps (t + 1) C).card : ℝ) := by
  classical
  let F := univ.sigma fun x : V => commonConnectorMaps t C x x
  let prepend : (Σ _x : V, Fin t → V) → (Fin (t + 1) → V) :=
    fun xf => rootedValue xf.1 xf.2
  have hp : Function.Injective prepend := by
    rintro ⟨x, f⟩ ⟨y, g⟩ hfg
    have hxy : x = y := congrFun hfg 0
    subst y
    have htail : f = g := funext fun i => congrFun hfg i.succ
    subst g
    rfl
  have hsub : F.image prepend ⊆ rainbowCliqueMaps (t + 1) C := by
    intro f hf
    obtain ⟨⟨x, g⟩, hxg, rfl⟩ := mem_image.mp hf
    have hg : g ∈ commonConnectorMaps t C x x := (mem_sigma.mp hxg).2
    obtain ⟨hginj, hgconn⟩ := mem_mapFamily.mp hg
    apply mem_mapFamily.mpr
    refine ⟨?_, ?_⟩
    · exact Fin.cons_injective_of_injective (by
        rintro ⟨i, hi⟩
        exact hgconn.1 (mem_image.mpr ⟨i, mem_univ _, hi⟩)) hginj
    · simpa only [prepend, rootedValue_image] using hgconn.2.2.1
  have hcard : F.card ≤ (rainbowCliqueMaps (t + 1) C).card := by
    rw [← card_image_of_injective F hp]
    exact card_le_card hsub
  have hsum : β * (Fintype.card V : ℝ) ^ (t + 1) ≤ (F.card : ℝ) := by
    dsimp only [F]
    rw [card_sigma, Nat.cast_sum]
    calc
      _ = ∑ _x : V, β * (Fintype.card V : ℝ) ^ t := by simp [pow_succ]; ring
      _ ≤ _ := sum_le_sum fun x _ => hconn x
  exact hsum.trans (by exact_mod_cast hcard)

end DensityHS.Rainbow
