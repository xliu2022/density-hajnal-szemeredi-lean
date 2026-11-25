module

public import DensityHS.Basic.FiniteDuality
public import DensityHS.Finite.AsymptoticParameters
public import DensityHS.Finite.Rounding
public import DensityHS.Weighted.Main

/-!
# Density of a regular reduced model

Author and maintainer: Xizhi Liu.

Finite strong duality, actual regular-pair packing, and the weighted density
inequality imply the envelope bound for the reduced model. The quantified
hypotheses below are the data later supplied by Szemerédi regularity.
-/

@[expose] public section

namespace DensityHS.Regularity

open Finset

variable {I V : Type*} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]

/-- A reduced model of a graph with packing number at most `k` has density at
most the envelope at `k/N`, up to the chosen continuity error. -/
theorem reduced_density_bound {r k M : ℕ} (hr : 3 ≤ r)
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph I) (S : I → Finset V)
    {α d β N δ τ : ℝ}
    (hα : 0 < α) (hd : α < d) (hd1 : d - α ≤ 1)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hN : 0 < N)
    (hδ : 0 < δ) (hτ : 0 < τ) (hβδ : β ≤ δ / 4)
    (hmod : ∀ x ∈ Set.Icc 0 (1 / (r : ℝ)), ∀ y ∈ Set.Icc 0 (1 / (r : ℝ)),
      |x - y| < δ → |Phi r x - Phi r y| < τ)
    (hx : (k : ℝ) / N ∈ Set.Icc 0 (1 / (r : ℝ)))
    (hM : Fintype.card I ≤ M) (hlarge : (2 : ℝ) ^ M / N ≤ δ / 4)
    (hprob : IsProbabilityWeight (fun i => (S i).card / N))
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (hne : ∀ i, (S i).Nonempty)
    (hreg : ∀ i j, H.Adj i j → G.IsUniform α (S i) (S j))
    (hdensity : ∀ i j, H.Adj i j → d ≤ (G.edgeDensity (S i) (S j) : ℝ))
    (hsmall : α * r < β * (d - α) ^ (r - 1))
    (hpack : HasPackingNumberAtMost r G k) :
    edgeMass H (fun i => (S i).card / N) ≤ Phi r ((k : ℝ) / N) + τ := by
  classical
  have hrpos : 0 < r := by omega
  obtain ⟨c, t, hc, ht, heq⟩ := fractional_strong_duality r H hrpos
    (fun i => (S i).card / N) hprob.1
  let z : ℝ := tilingSize r H t
  have hz0 : 0 ≤ z := tilingSize_nonneg ht.1
  have hz : z ≤ 1 / (r : ℝ) := tilingSize_le_inv hrpos hprob ht.1
  have hz1 : z ≤ 1 := hz.trans ((div_le_one (by positivity)).2 (by exact_mod_cast hrpos))
  have hround := reduced_tiling_bound_of_packing_bound hrpos G H S hα hd hd1 hβ hβ1 hN
    hdisj hne hreg hdensity hsmall hpack ht.1
  have hcount : ((cliqueFamily r H).card : ℝ) ≤ (2 : ℝ) ^ M := by
    exact_mod_cast card_cliqueFamily_le_two_pow r H hM
  have hC : ((cliqueFamily r H).card : ℝ) / N ≤ δ / 4 :=
    (div_le_div_of_nonneg_right hcount hN.le).trans hlarge
  have hgap : z ≤ (k : ℝ) / N + δ / 2 :=
    fractional_gap_of_rounding hN hβ.le hβδ hz1 hC hround
  have hPhi := Phi_le_of_one_sided_close hr hτ hδ hmod hx ⟨hz0, hz⟩ hgap
  have hweighted : edgeMass H (fun i => (S i).card / N) ≤ Phi r z := by
    dsimp [z]
    rw [heq]
    exact weighted_clique_cover_bound (by omega) hprob hc.1
      (by rw [← heq]; exact hz)
  exact hweighted.trans hPhi

end DensityHS.Regularity
