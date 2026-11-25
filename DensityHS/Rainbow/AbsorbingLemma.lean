module

public import DensityHS.Rainbow.AbsorbingSet
public import DensityHS.Rainbow.AbsorberParameters
public import DensityHS.Rainbow.ColorDigraph

/-!
# The rainbow absorbing lemma

For every positive degree margin and prescribed small size, a sufficiently
large edge-coloured graph has a concrete set that absorbs every sufficiently
small divisible leftover.  All local absorbers, their abundance, and the
simultaneous random selection are constructed in the preceding modules.

Formalization author and maintainer: Xizhi Liu.
-/

@[expose] public section

open Finset

universe u v

namespace DensityHS.Rainbow

theorem exists_nat_mul_threshold {d : ℝ} (hd : 0 < d) (c : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → c ≤ d * n := by
  obtain ⟨N, hN⟩ := exists_nat_gt (c / d)
  refine ⟨N, ?_⟩
  intro n hn
  have hnn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hh := (div_le_iff₀ hd).mp (hN.le.trans hnn)
  simpa only [mul_comm d] using hh

theorem rainbow_absorbing_lemma_of_outDegree {t : ℕ} (ht : 2 ≤ t)
    {ε ζ : ℝ} (hε : 0 < ε) (hζ : 0 < ζ) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ N : ℕ,
      ∀ {V : Type u} [Fintype V] [DecidableEq V] {K : Type v}
        (G : SimpleGraph V) (C : G.EdgeLabeling K) (D : Digraph V),
        D.baseGraph ≤ G → OutgoingColorsDistinct D C → N ≤ Fintype.card V →
        (∀ w : V, (1 - 1 / (2 * (t : ℝ)) + ε) * Fintype.card V ≤
          (D.outDegree w : ℝ)) →
        ∃ W : Finset V, (W.card : ℝ) < ζ * Fintype.card V ∧
          HasPerfectRainbowPackingOn (t + 1) C W ∧
          ∀ U : Finset V, Disjoint W U → (t + 1) ∣ U.card →
            (U.card : ℝ) ≤ γ * Fintype.card V →
            HasPerfectRainbowPackingOn (t + 1) C (W ∪ U) := by
  obtain ⟨s₀, hs₀⟩ := exists_nat_one_div_lt (half_pos hε)
  let s := s₀ + 1
  have hs : 0 < s := Nat.zero_lt_succ _
  have hsε : (s : ℝ)⁻¹ ≤ ε / 2 := by
    simpa only [s, Nat.cast_add, Nat.cast_one, one_div] using hs₀.le
  let β := connectorCoefficient t s ε
  have hβ : 0 < β := connectorCoefficient_pos hs hε
  let η : ℝ := (β / 2) ^ (t + 2)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨γ, hγ, N₀, _, hN₀⟩ := exists_selection_parameters
    (a := (t + 1) ^ 2) (r := t + 1) (by positivity) (by omega) hη hζ
  obtain ⟨N₁, hN₁⟩ := exists_nat_mul_threshold hε 4
  obtain ⟨N₂, hN₂⟩ := exists_nat_mul_threshold hβ ((2 * (t + 1) ^ 3 * t : ℕ) : ℝ)
  obtain ⟨N₃, hN₃⟩ := exists_nat_mul_threshold hβ ((2 * (t + 1) ^ 3 : ℕ) : ℝ)
  refine ⟨γ, hγ, max N₀ (max N₁ (max N₂ N₃)), ?_⟩
  intro V _ _ K G C D hbase hout hn hdeg
  have hn₀ : N₀ ≤ Fintype.card V := by omega
  have hn₁ : N₁ ≤ Fintype.card V := by omega
  have hn₂ : N₂ ≤ Fintype.card V := by omega
  have hn₃ : N₃ ≤ Fintype.card V := by omega
  have hconn : ∀ x y : V, β * (Fintype.card V : ℝ) ^ t ≤
      ((commonConnectorMaps t C x y).card : ℝ) := by
    intro x y
    exact commonConnectorMaps_abundant ht hs hbase hout x y hε hsε
      (hN₁ _ hn₁) (hN₂ _ hn₂) hdeg
  obtain ⟨p, L, S, T, hS, hT, hsize, hcap, hL, hpotential⟩ := hN₀ _ hn₀
  obtain ⟨W, hW, hAbs⟩ := exists_absorbingSet_of_connector_supply
    (by omega : 0 < t) hβ.le hconn (hN₃ _ hn₃) p hS hT hL hpotential
  refine ⟨W, hW.trans_le hsize, hAbs.1, ?_⟩
  intro U hWU hdiv hU
  apply hAbs.2 U hWU hdiv
  exact_mod_cast hU.trans hcap

theorem rainbow_absorbing_lemma {t : ℕ} (ht : 2 ≤ t)
    {ε ζ : ℝ} (hε : 0 < ε) (hζ : 0 < ζ) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ N : ℕ,
      ∀ {V : Type u} [Fintype V] [DecidableEq V] {K : Type v}
        (G : SimpleGraph V) (C : G.EdgeLabeling K),
        N ≤ Fintype.card V →
        (∀ w : V, (1 - 1 / (2 * (t : ℝ)) + ε) * Fintype.card V ≤
          (colorDegree C w : ℝ)) →
        ∃ W : Finset V, (W.card : ℝ) < ζ * Fintype.card V ∧
          HasPerfectRainbowPackingOn (t + 1) C W ∧
          ∀ U : Finset V, Disjoint W U → (t + 1) ∣ U.card →
            (U.card : ℝ) ≤ γ * Fintype.card V →
            HasPerfectRainbowPackingOn (t + 1) C (W ∪ U) := by
  obtain ⟨γ, hγ, N, hN⟩ := rainbow_absorbing_lemma_of_outDegree.{u, v} ht hε hζ
  refine ⟨γ, hγ, N, ?_⟩
  intro V _ _ K G C hn hdeg
  apply hN G C (representativeDigraph C) (representativeDigraph_base_le C)
    (representativeDigraph_outgoing_distinct C) hn
  intro w
  simpa only [representativeDigraph_outDegree] using hdeg w

end DensityHS.Rainbow
