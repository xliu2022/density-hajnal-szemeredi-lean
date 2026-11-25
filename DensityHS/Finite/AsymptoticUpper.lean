module

public import DensityHS.Finite.ReducedDensity
public import DensityHS.Finite.ReducedGraph

/-!
# Uniform finite density upper bound

Author and maintainer: Xizhi Liu.

For every fixed clique size, the envelope gives an asymptotic upper bound
uniformly over the allowed packing number. This proof uses the proved finite
regularity lemma, regular-clique embedding and rounding, and finite weighted
duality. It does not invoke a graphon transference theorem.
-/

@[expose] public section

namespace DensityHS.Regularity

open Finset Fintype

universe u

/-- The upper-bound direction of the density Hajnal–Szemerédi theorem,
uniformly for every packing parameter `k` in the full interval. -/
theorem finite_density_upper_bound {r : ℕ} (hr : 3 ≤ r) {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → ∀ k : ℕ, r * k ≤ Fintype.card V →
      HasPackingNumberAtMost r G k →
      (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ) ^ 2 ≤
        Phi r ((k : ℝ) / Fintype.card V) + ε := by
  obtain ⟨δ, hδ, hmod⟩ := exists_Phi_uniform_radius hr (show 0 < ε / 2 by linarith)
  obtain ⟨β, d, α, hβ, hβ1, hβδ, hα, hαd, hd1, hsmall, hloss⟩ :=
    exists_regular_rounding_parameters hr hε hδ
  let l : ℕ := ⌈4 / ε⌉₊
  let M : ℕ := SzemerediRegularity.bound α l
  obtain ⟨n₀, hln₀, hn₀pos, hlarge⟩ := exists_order_bound l M hδ
  refine ⟨n₀, ?_⟩
  intro V instV instDecV G instAdj hn k hk hpack
  classical
  have hnpos : 0 < Fintype.card V := hn₀pos.trans_le hn
  haveI : Nonempty V := Fintype.card_pos_iff.mp hnpos
  have hN : 0 < (Fintype.card V : ℝ) := by exact_mod_cast hnpos
  have hrR : 0 < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  obtain ⟨P, hP, hPl, hPM, hPreg⟩ := szemeredi_regularity G hα (hln₀.trans hn)
  have hparts : 4 / ε ≤ (P.parts.card : ℝ) := by
    calc
      4 / ε ≤ (l : ℝ) := Nat.le_ceil _
      _ ≤ P.parts.card := by exact_mod_cast hPl
  have hM : Fintype.card P.parts ≤ M := by simpa only [Fintype.card_coe] using hPM
  have hx : (k : ℝ) / Fintype.card V ∈ Set.Icc 0 (1 / (r : ℝ)) := by
    refine ⟨div_nonneg (Nat.cast_nonneg k) hN.le, ?_⟩
    apply (div_le_div_iff₀ hN hrR).2
    have hkr : (r : ℝ) * k ≤ Fintype.card V := by exact_mod_cast hk
    nlinarith only [hkr]
  have hdisj : ∀ i j : P.parts, i ≠ j → Disjoint (i : Finset V) (j : Finset V) := by
    intro i j hij
    exact P.disjoint i.property j.property (fun h => hij (Subtype.ext h))
  have hne : ∀ i : P.parts, (i : Finset V).Nonempty :=
    fun i => P.nonempty_of_mem_parts i.property
  have hred := reduced_density_bound hr G (clusterGraph P G α d)
    (fun i : P.parts => (i : Finset V)) hα hαd hd1 hβ hβ1.le hN hδ
    (show 0 < ε / 2 by linarith) hβδ hmod hx hM (hlarge _ hn)
    (clusterWeight_probability P) hdisj hne
    (fun i j hij => hij.2.1) (fun i j hij => hij.2.2) hsmall hpack
  have hgraph := edgeMass_le_cluster hα (le_of_lt (hα.trans hαd)) hε hP hPreg hparts
  have hbound : edgeMass G (uniformWeight V) ≤
      Phi r ((k : ℝ) / Fintype.card V) + ε := by
    change edgeMass (clusterGraph P G α d) (clusterWeight P) ≤
      Phi r ((k : ℝ) / Fintype.card V) + ε / 2 at hred
    linarith
  simpa only [edgeMass_uniform] using hbound

/-- A version on the standard labelled vertex set of order `n`. -/
theorem finite_density_upper_bound_fin {r : ℕ} (hr : 3 ≤ r) {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      ∀ k : ℕ, r * k ≤ n → HasPackingNumberAtMost r G k →
      (G.edgeFinset.card : ℝ) ≤ (Phi r ((k : ℝ) / n) + ε) * (n : ℝ) ^ 2 := by
  obtain ⟨n₀, hbound⟩ := finite_density_upper_bound.{0} hr hε
  refine ⟨n₀ + 1, ?_⟩
  intro n hn G instAdj k hk hpack
  have hn0 : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn0
  have h := hbound G (by simpa using (show n₀ ≤ n by omega)) k (by simpa using hk) hpack
  simp only [Fintype.card_fin] at h
  exact (div_le_iff₀ (sq_pos_of_pos hnR)).mp h

end DensityHS.Regularity
