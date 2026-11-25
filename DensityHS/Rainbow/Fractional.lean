module

public import DensityHS.Rainbow.Digraph
public import DensityHS.Rainbow.Branch
public import DensityHS.Rainbow.DigraphAlgebra
public import DensityHS.Weighted.Main

/-!
# Perfect fractional tilings in dense finite digraphs

This is the directed Proposition 5.2. Its proof uses finite packing duality,
a normalized minimum cover, actual arc counts in an out-neighborhood, and
the proved weighted density theorem.

Author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS

open Finset

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A normalized tile cover restricts to a clique cover on the double-edge
graph of the zero vertex's out-neighborhood. -/
theorem Digraph.zero_cover_doubleNeighbors {r : ℕ} (hr : 2 ≤ r)
    (D : Digraph V) {c : V → ℝ} (hc : IsFamilyCover (D.tileFamily r) c)
    {v₀ : V} (hz : c v₀ = 0) :
    IsCliqueCover (r - 1) ((D.induce (D.outNeighbors v₀)).doubleGraph)
      (fun w => c w) := by
  classical
  refine ⟨fun w => hc.1 w, ?_⟩
  intro K hK
  let e : D.outNeighbors v₀ ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  have hK' : D.doubleGraph.IsNClique (r - 1) (K.map e) := by
    refine ⟨?_, by simpa using hK.card_eq⟩
    intro u hu v hv huv
    obtain ⟨u', hu', rfl⟩ := Finset.mem_map.mp hu
    obtain ⟨v', hv', rfl⟩ := Finset.mem_map.mp hv
    exact hK.isClique hu' hv' (fun h => huv (congrArg e h))
  have hN : ∀ w ∈ K.map e, D.Arc v₀ w := by
    intro w hw
    obtain ⟨w', _hw', rfl⟩ := Finset.mem_map.mp hw
    exact (D.mem_outNeighbors v₀ w').mp w'.property
  have hvK : v₀ ∉ K.map e := fun h => D.loopless v₀ (hN v₀ h)
  have htile := D.insert_isTile hr hK' hN
  have hcover := hc.2 _ ((D.mem_tileFamily r _).mpr htile)
  rw [Finset.sum_insert hvK, hz, zero_add, Finset.sum_map] at hcover
  exact hcover

/-- Cover cost under uniform vertex weights. -/
theorem coverCost_uniform_eq {W : Type*} [Fintype W] (c : W → ℝ) :
    coverCost (fun _ => 1 / (Fintype.card W : ℝ)) c =
      (∑ v, c v) / (Fintype.card W : ℝ) := by
  unfold coverCost
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro v _
  ring

/-- The parameter at the directed threshold lies inside the weighted theorem's
cover interval. -/
theorem rainbow_parameter_le_cover_endpoint {r : ℕ} (hr : 4 ≤ r) :
    1 / ((r : ℝ) * rainbowThreshold r) ≤ 1 / ((r - 1 : ℕ) : ℝ) := by
  have hrR : (4 : ℝ) ≤ r := by exact_mod_cast hr
  have hρ := rainbowThreshold_ge_baseline hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hbase := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * r)).mp hρ
  rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
  apply one_div_le_one_div_of_le (by linarith)
  nlinarith

/-- The cover mass on the out-neighborhood is small enough to invoke the
threshold envelope. -/
theorem Digraph.uniform_neighbor_cover_cost_le {r : ℕ} (hr : 4 ≤ r)
    (D : Digraph V) [Nonempty V] {v₀ : V} {c : V → ℝ}
    (hc : ∀ v, 0 ≤ c v) (hcost : ∑ v, c v < (Fintype.card V : ℝ) / r)
    (hdegree : rainbowThreshold r * (Fintype.card V : ℝ) ≤ D.outDegree v₀) :
    coverCost (fun _ : D.outNeighbors v₀ => 1 / (Fintype.card (D.outNeighbors v₀) : ℝ))
      (fun w => c w) ≤ 1 / ((r : ℝ) * rainbowThreshold r) := by
  classical
  let S := D.outNeighbors v₀
  change rainbowThreshold r * (Fintype.card V : ℝ) ≤ (S.card : ℝ) at hdegree
  have hN : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hρ : 0 < rainbowThreshold r := rainbowThreshold_pos hr
  have hrR : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hm : (0 : ℝ) < S.card := (mul_pos hρ hN).trans_le hdegree
  have hsub : (∑ w : S, c w) ≤ ∑ v, c v := by
    rw [Finset.sum_coe_sort]
    exact Finset.sum_le_univ_sum_of_nonneg hc
  rw [coverCost_uniform_eq, Fintype.card_coe]
  apply (div_le_iff₀ hm).mpr
  calc
    (∑ w : S, c w) ≤ (Fintype.card V : ℝ) / r := hsub.trans hcost.le
    _ ≤ 1 / ((r : ℝ) * rainbowThreshold r) * S.card := by
      have hh : (Fintype.card V : ℝ) / r ≤ S.card / ((r : ℝ) * rainbowThreshold r) := by
        apply (div_le_div_iff₀ hrR (mul_pos hrR hρ)).mpr
        have hmul := mul_le_mul_of_nonneg_left hdegree hrR.le
        nlinarith
      simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hh

/-- The induced out-neighborhood contains enough arcs for the strict
finite-order lower bound. -/
theorem Digraph.neighbor_arc_lower_bound {r : ℕ} (D : Digraph V)
    (hdegree : ∀ v, rainbowThreshold r * (Fintype.card V : ℝ) ≤ D.outDegree v)
    (v₀ : V) :
    ((D.outNeighbors v₀).card : ℝ) *
        (rainbowThreshold r * (Fintype.card V : ℝ) - Fintype.card V + (D.outNeighbors v₀).card) ≤
      (D.induce (D.outNeighbors v₀)).arcCount := by
  classical
  let S := D.outNeighbors v₀
  rw [Digraph.arcCount_eq_sum_outDegree]
  calc
    _ = ∑ _w : S, (rainbowThreshold r * (Fintype.card V : ℝ) - Fintype.card V + S.card) := by
      simp [Fintype.card_coe, S]
      ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro w _
      have hglobal := hdegree w
      have hrestrict := D.outDegree_le_induce_add_complement S w
      linarith

/-- Proposition 5.2: every finite loopless digraph at the new out-degree
threshold has a perfect fractional `(r,r-2)`-tiling. -/
theorem Digraph.perfect_fractional_tiling_of_outDegree {r : ℕ} (hr : 4 ≤ r)
    (D : Digraph V)
    (hdegree : ∀ v, rainbowThreshold r * (Fintype.card V : ℝ) ≤ D.outDegree v) :
    D.HasPerfectFractionalTiling r := by
  classical
  by_cases hV : Nonempty V
  · letI : Nonempty V := hV
    by_contra hnone
    have hcard : ∀ K ∈ D.tileFamily r, K.card = r :=
      fun K hK => ((D.mem_tileFamily r K).mp hK).1
    obtain ⟨c, hc, hcost, v₀, hz⟩ := normalized_family_cover_certificate
      (by omega : 0 < r) hcard hnone
    let S := D.outNeighbors v₀
    let H : SimpleGraph S := (D.induce S).doubleGraph
    let p : S → ℝ := fun _ => 1 / (Fintype.card S : ℝ)
    let d : S → ℝ := fun w => c w
    have hN : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
    have hρ : 0 < rainbowThreshold r := rainbowThreshold_pos hr
    have hmass : rainbowThreshold r * (Fintype.card V : ℝ) ≤ (S.card : ℝ) := hdegree v₀
    have hm : (0 : ℝ) < S.card := (mul_pos hρ hN).trans_le hmass
    obtain ⟨w, hw⟩ : S.Nonempty := Finset.card_pos.mp (by exact_mod_cast hm)
    letI : Nonempty S := ⟨⟨w, hw⟩⟩
    have hp : IsProbabilityWeight p := probabilityWeight_uniform
    have hcover : IsCliqueCover (r - 1) H d := D.zero_cover_doubleNeighbors (by omega) hc hz
    have hcostH : coverCost p d ≤ 1 / ((r : ℝ) * rainbowThreshold r) :=
      D.uniform_neighbor_cover_cost_le hr hc.1 hcost (hdegree v₀)
    have hendpoint := rainbow_parameter_le_cover_endpoint hr
    have hbound := weighted_clique_cover_bound (by omega : 2 ≤ r - 1) hp hcover
      (hcostH.trans hendpoint)
    have hmono := Phi_monotoneOn (by omega : 3 ≤ r - 1)
      ⟨coverCost_nonneg hp.1 hcover.1, hcostH.trans hendpoint⟩
      ⟨by positivity, hendpoint⟩ hcostH
    have hupper : edgeMass H p ≤ (3 * rainbowThreshold r - 2) / (2 * rainbowThreshold r) := by
      have h := hbound.trans hmono
      rwa [rainbow_envelope_threshold hr] at h
    have hraw := (D.induce S).arcCount_le_pairs_add_doubleEdges
    have hscale := edgeMass_uniform_rescale H
    rw [Fintype.card_coe] at hscale
    rw [Fintype.card_coe] at hraw
    change 2 * (D.induce S).arcCount ≤ (S.card : ℝ) * ((S.card : ℝ) - 1) +
      2 * edgeMass H (fun _ => 1) at hraw
    rw [hscale] at hraw
    have hlower := D.neighbor_arc_lower_bound hdegree v₀
    have harcs : (S.card : ℝ) *
        (rainbowThreshold r * (Fintype.card V : ℝ) - Fintype.card V + S.card) ≤
          (S.card : ℝ) * ((S.card : ℝ) - 1) / 2 + (S.card : ℝ) ^ 2 * edgeMass H p := by
      change (S.card : ℝ) *
        (rainbowThreshold r * (Fintype.card V : ℝ) - Fintype.card V + S.card) ≤
          (D.induce S).arcCount at hlower
      dsimp [p]
      rw [Fintype.card_coe]
      linarith
    have hstrict := directed_arc_strict_density_gap hm hρ
      (rainbowThreshold_lt_one hr).le hmass harcs
    exact (not_lt_of_ge hupper) hstrict
  · haveI : IsEmpty V := not_nonempty_iff.mp hV
    refine ⟨0, ?_, ?_⟩
    · intro K
      simp
    · intro v
      exact isEmptyElim v

end DensityHS
