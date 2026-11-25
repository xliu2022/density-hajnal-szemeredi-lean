module

public import DensityHS.Rainbow.NearPerfectParameters
public import DensityHS.Rainbow.Rounding
public import DensityHS.Rainbow.Fractional
public import DensityHS.Rainbow.MapCounting

/-!
# Near-perfect rainbow clique packings at the new threshold

This theorem constructs the regular reduced digraph, applies the proved
fractional directed tiling theorem, rounds all requests using actual rainbow
extraction, and lifts the result through the palette-preserving reduction.
No regularity, rounding, or transfer theorem is left as a hypothesis.

Formalization author and maintainer: Xizhi Liu.
-/

@[expose] public section

set_option maxHeartbeats 1000000

open Finset
open scoped BigOperators

universe u v

namespace DensityHS.Rainbow

attribute [local instance] Classical.propDecidable

theorem tileFamily_card_le_pow {I : Type*} [Fintype I] [DecidableEq I]
    (D : Digraph I) (r : ℕ) : (D.tileFamily r).card ≤ Fintype.card I ^ r := by
  classical
  let f : D.tileFamily r → {T : Finset I // T.card = r} := fun T =>
    ⟨T.1, ((D.mem_tileFamily r T.1).mp T.2).1⟩
  have hf : Function.Injective f := by
    intro T T' h
    exact Subtype.ext (congrArg (fun X : {T : Finset I // T.card = r} => X.1) h)
  have hh := Fintype.card_le_of_injective f hf
  have hh' : (D.tileFamily r).card ≤ Fintype.card {T : Finset I // T.card = r} := by
    simpa only [Fintype.card_coe] using hh
  exact hh'.trans (card_rsets_le_pow (V := I) r)

theorem directed_rainbow_near_perfect {r : ℕ} (hr : 4 ≤ r) {δ η : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V] {K : Type v}
      (G : SimpleGraph V) (C : G.EdgeLabeling K) (D : Digraph V),
      D.baseGraph ≤ G → OutgoingColorsDistinct D C → HasStarColorClasses C →
      N ≤ Fintype.card V →
      (∀ x, (rainbowThreshold r + δ) * Fintype.card V ≤ (D.outDegree x : ℝ)) →
      ∃ P : Finset (Finset V), IsRainbowPacking r C P ∧
        (1 - η) * Fintype.card V ≤ (r : ℝ) * P.card := by
  classical
  have hr0 : 0 < r := by omega
  have hρ := (rainbowThreshold_pos hr).le
  have hρ1 := (rainbowThreshold_lt_one hr).le
  obtain ⟨α, q, ε, hα, hα1, hαη, hq, hqhalf, hε, hεq, hqε1,
    hregsmall, hcoverloss, hmargin, hsmall⟩ := exists_nearPerfect_parameters hr0 hδ hη
  obtain ⟨M, N₀, hN₀⟩ := exists_regular_state_model.{u} hρ hρ1 (show 0 < δ / 4 by positivity)
    hε hq.le hq hqhalf hregsmall hcoverloss
    (show rainbowThreshold r + δ / 4 + 2 * q + 3 * q ≤ rainbowThreshold r + δ - ε by linarith) 1
  let A := α * (q - ε) ^ (r - 1)
  have hA : 0 < A := by dsimp [A]; positivity
  obtain ⟨N₁, hN₁pos, hN₁⟩ := exists_rainbow_counting_order hr0 hA
    (show (0 : ℝ) < M + 1 by positivity) (((r ^ 3 + r ^ 4 : ℕ) : ℝ))
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt ((r : ℝ) * (M : ℝ) ^ r / α)
  refine ⟨max N₀ (max N₁ N₂), ?_⟩
  intro V _ _ K G C D hbase hout hstar hn hdeg
  have hn₀ : N₀ ≤ Fintype.card V := by omega
  have hn₁ : N₁ ≤ Fintype.card V := by omega
  have hn₂ : N₂ ≤ Fintype.card V := by omega
  obtain ⟨k, m, Q, hm, _, hkM, hcover, hRdeg⟩ := hN₀ V D hn₀ hdeg
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hkMR : (k : ℝ) ≤ M := by exact_mod_cast hkM
  have hmcoverage : (Fintype.card V : ℝ) ≤ 2 * ((M : ℝ) + 1) * m := by
    have hh := mul_le_mul_of_nonneg_right hkMR hmR.le
    nlinarith
  obtain ⟨hlarge, hgap⟩ := hN₁ (Fintype.card V) hn₁ m hmcoverage
  have hfrac : Q.reduced.HasPerfectFractionalTiling r :=
    Q.reduced.perfect_fractional_tiling_of_outDegree hr (fun i => by
      simpa only [Fintype.card_fin] using (hRdeg i).le)
  have hembed : ∀ (T : Q.reduced.tileFamily r) (U : Finset V),
      (∀ i ∈ (T : Finset (Fin k)), α * (Q.clusters i).card ≤ ((Q.clusters i \ U).card : ℝ)) →
      ∃ B : Finset V, IsRainbowClique r C B ∧ Disjoint B U ∧
        ∀ i, (B ∩ Q.clusters i).card = if i ∈ (T : Finset (Fin k)) then 1 else 0 := by
    intro T U hpools
    exact Q.exists_rainbow_clique_avoiding (by omega) hbase hout hstar hε hεq hqε1 hα
      hsmall hlarge (by simpa only [Nat.cast_mul, Nat.cast_pow, A] using hgap)
      T U ((Q.reduced.mem_tileFamily r T).mp T.2) hpools
  obtain ⟨P, hP, hround⟩ := round_perfect_fractional_tiles hr0 G C Q.reduced Q.clusters
    (show α ≤ 1 by linarith) m Q.cluster_card hembed hfrac
  have hfamily : (Q.reduced.tileFamily r).card ≤ M ^ r := by
    have hh := tileFamily_card_le_pow Q.reduced r
    simp only [Fintype.card_fin] at hh
    exact hh.trans (by gcongr)
  have hroundloss : (r : ℝ) * (Q.reduced.tileFamily r).card ≤ α * Fintype.card V := by
    have hN₂R : (N₂ : ℝ) ≤ Fintype.card V := by exact_mod_cast hn₂
    have hbig := (div_le_iff₀ hα).mp (hN₂.le.trans hN₂R)
    have hfamilyR : ((Q.reduced.tileFamily r).card : ℝ) ≤ (M : ℝ) ^ r := by exact_mod_cast hfamily
    have hmul := mul_le_mul_of_nonneg_left hfamilyR (show (0 : ℝ) ≤ r by positivity)
    nlinarith
  have hcover' := mul_le_mul_of_nonneg_left hcover (show 0 ≤ 1 - α by linarith)
  have hηn := mul_le_mul_of_nonneg_right hαη hnR.le
  have hsq : 0 ≤ α ^ 2 * Fintype.card V := by positivity
  simp only [Fintype.card_fin] at hround
  refine ⟨P, hP, ?_⟩
  nlinarith

theorem rainbow_near_perfect {r : ℕ} (hr : 4 ≤ r) {δ η : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V] {K : Type v}
      (G : SimpleGraph V) (C : G.EdgeLabeling K), N ≤ Fintype.card V →
      (∀ x, (rainbowThreshold r + δ) * Fintype.card V ≤ (colorDegree C x : ℝ)) →
      ∃ P : Finset (Finset V), IsRainbowPacking r C P ∧
        (1 - η) * Fintype.card V ≤ (r : ℝ) * P.card := by
  obtain ⟨N, hN⟩ := directed_rainbow_near_perfect.{u, v} hr hδ hη
  refine ⟨N, ?_⟩
  intro V _ _ K G C hn hdeg
  obtain ⟨H, hHG, D, hbase, hstar, hout, _, hexact⟩ := exists_exact_color_digraph_reduction C
  have hdegree : ∀ x, (rainbowThreshold r + δ) * Fintype.card V ≤ (D.outDegree x : ℝ) := by
    intro x
    rw [hexact x]
    exact hdeg x
  obtain ⟨P, hP, hsize⟩ := hN H (restrictColor C hHG) D hbase hout hstar hn hdegree
  exact ⟨P, hP.of_restrict, hsize⟩

end DensityHS.Rainbow
