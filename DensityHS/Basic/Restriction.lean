module

public import DensityHS.Basic.WeightedGraph

/-!
# Restriction to the positive support

Author and maintainer: Xizhi Liu.

Removing zero-weight vertices preserves cover cost and weighted edge mass.
The restricted probability vector is strictly positive, so theorems stated
with the manuscript's positive-support convention apply to nonnegative vectors.
-/

@[expose] public section

namespace DensityHS

open Finset Set

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

/-- Vertices having positive probability mass. -/
abbrev PositiveSupport (p : V → ℝ) := {v : V // 0 < p v}

/-- Restricting a clique cover to an induced subgraph preserves feasibility. -/
theorem IsCliqueCover.restrict {r : ℕ} {G : SimpleGraph V} {c : V → ℝ}
    (hc : IsCliqueCover r G c) (S : Set V) :
    IsCliqueCover r (G.induce S) (fun v : S => c v) := by
  classical
  refine ⟨fun v => hc.1 v, ?_⟩
  intro K hK
  have hK' := (G.isNClique_induce_iff S K r).mp hK
  simpa only [Finset.sum_map, Function.Embedding.coe_subtype] using hc.2 _ hK'

/-- A finite sum is unchanged when the summands outside a subtype vanish. -/
theorem sum_restrict_eq (S : Set V) [Fintype S] (f : V → ℝ)
    (hzero : ∀ v ∉ S, f v = 0) :
    (∑ v : S, f v) = ∑ v, f v := by
  classical
  rw [← Finset.sum_subtype S.toFinset (fun v => Set.mem_toFinset) f]
  exact Finset.sum_subset (Finset.subset_univ S.toFinset)
    (fun v _ hv => hzero v (by simpa using hv))

theorem IsProbabilityWeight.restrict {p : V → ℝ} (hp : IsProbabilityWeight p)
    (S : Set V) [Fintype S] (hzero : ∀ v ∉ S, p v = 0) :
    IsProbabilityWeight (fun v : S => p v) := by
  refine ⟨fun v => hp.1 v, ?_⟩
  rw [sum_restrict_eq S p hzero, hp.2]

/-- Cover cost is invariant under removing zero-weight vertices. -/
theorem coverCost_restrict (S : Set V) [Fintype S] (p c : V → ℝ)
    (hzero : ∀ v ∉ S, p v = 0) :
    coverCost (fun v : S => p v) (fun v : S => c v) = coverCost p c := by
  apply sum_restrict_eq S (fun v => p v * c v)
  intro v hv
  simp [hzero v hv]

/-- Edge mass is invariant under removing zero-weight vertices. -/
theorem edgeMass_restrict (S : Set V) [Fintype S] (G : SimpleGraph V) (p : V → ℝ)
    (hzero : ∀ v ∉ S, p v = 0) :
    edgeMass (G.induce S) (fun v : S => p v) = edgeMass G p := by
  classical
  unfold edgeMass
  congr 1
  calc
    (∑ u : S, ∑ v : S, if (G.induce S).Adj u v then p u * p v else 0) =
        ∑ u : S, ∑ v : V, if G.Adj u v then p u * p v else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      apply sum_restrict_eq S (fun v => if G.Adj u v then p u * p v else 0)
      intro v hv
      simp [hzero v hv]
    _ = ∑ u : V, ∑ v : V, if G.Adj u v then p u * p v else 0 := by
      apply sum_restrict_eq S (fun u => ∑ v, if G.Adj u v then p u * p v else 0)
      intro u hu
      simp [hzero u hu]

theorem zero_of_not_positive {p : V → ℝ} (hp : ∀ v, 0 ≤ p v)
    {v : V} (hv : ¬0 < p v) : p v = 0 :=
  le_antisymm (le_of_not_gt hv) (hp v)

theorem probabilityWeight_positiveSupport {p : V → ℝ} (hp : IsProbabilityWeight p) :
    IsProbabilityWeight (fun v : PositiveSupport p => p v) := by
  apply hp.restrict {v | 0 < p v}
  intro v hv
  exact zero_of_not_positive hp.1 hv

theorem coverCost_positiveSupport {p : V → ℝ} (hp : ∀ v, 0 ≤ p v) (c : V → ℝ) :
    coverCost (fun v : PositiveSupport p => p v) (fun v : PositiveSupport p => c v) =
      coverCost p c := by
  apply coverCost_restrict {v | 0 < p v} p c
  intro v hv
  exact zero_of_not_positive hp hv

theorem edgeMass_positiveSupport {p : V → ℝ} (hp : ∀ v, 0 ≤ p v)
    (G : SimpleGraph V) :
    edgeMass (G.induce {v | 0 < p v}) (fun v : PositiveSupport p => p v) =
      edgeMass G p := by
  apply edgeMass_restrict {v | 0 < p v} G p
  intro v hv
  exact zero_of_not_positive hp hv

/-- If there is a zero-weight vertex, restriction strictly decreases the
finite number of vertices, as required in support-minimal induction. -/
theorem positiveSupport_card_lt {p : V → ℝ} (hz : ∃ v, p v = 0) :
    Fintype.card (PositiveSupport p) < Fintype.card V := by
  obtain ⟨v, hv⟩ := hz
  apply Fintype.card_subtype_lt (x := v)
  simpa [hv]

theorem positiveSupport_card_le (p : V → ℝ) :
    Fintype.card (PositiveSupport p) ≤ Fintype.card V :=
  Fintype.card_subtype_le (fun v => 0 < p v)

/-- Extend an induced-subgraph cover by assigning price one outside it. -/
noncomputable def extendCover (S : Set V) (c : S → ℝ) (v : V) : ℝ := by
  classical
  exact if h : v ∈ S then c ⟨v, h⟩ else 1

@[simp] theorem extendCover_coe (S : Set V) (c : S → ℝ) (v : S) :
    extendCover S c v = c v := by simp [extendCover]

/-- Extension by price one is a cover on the whole original graph. -/
theorem IsCliqueCover.extend {r : ℕ} {G : SimpleGraph V} {S : Set V} {c : S → ℝ}
    (hc : IsCliqueCover r (G.induce S) c) :
    IsCliqueCover r G (extendCover S c) := by
  classical
  have hnonneg : ∀ v, 0 ≤ extendCover S c v := by
    intro v
    unfold extendCover
    split_ifs with hv
    · exact hc.1 ⟨v, hv⟩
    · norm_num
  refine ⟨hnonneg, ?_⟩
  intro K hK
  by_cases hout : ∃ v ∈ K, v ∉ S
  · obtain ⟨v, hvK, hvS⟩ := hout
    have hsingle := Finset.single_le_sum (fun w (_ : w ∈ K) => hnonneg w) hvK
    simpa [extendCover, hvS] using hsingle
  · have hall : ∀ v ∈ K, v ∈ S := by
      intro v hv
      by_contra hn
      exact hout ⟨v, hv, hn⟩
    let L : Finset S := K.subtype (fun v => v ∈ S)
    have hmap : L.map (Function.Embedding.subtype (fun v => v ∈ S)) = K :=
      Finset.subtype_map_of_mem hall
    have hL : (G.induce S).IsNClique r L := by
      apply (G.isNClique_induce_iff S L r).mpr
      rwa [hmap]
    have hsum : (∑ v ∈ K, extendCover S c v) = ∑ v ∈ L, c v := by
      rw [← hmap, Finset.sum_map]
      apply Finset.sum_congr rfl
      intro v _
      exact extendCover_coe S c v
    rw [hsum]
    exact hc.2 L hL

theorem coverCost_extend (S : Set V) [Fintype S] (p : V → ℝ) (c : S → ℝ)
    (hzero : ∀ v ∉ S, p v = 0) :
    coverCost p (extendCover S c) = coverCost (fun v : S => p v) c := by
  simpa only [extendCover_coe] using (coverCost_restrict S p (extendCover S c) hzero).symm

/-- Optimality also survives deleting zero-weight vertices. -/
theorem IsOptimalCover.restrict {r : ℕ} {G : SimpleGraph V} {p c : V → ℝ}
    (hc : IsOptimalCover r G p c) (S : Set V) [Fintype S]
    (hzero : ∀ v ∉ S, p v = 0) :
    IsOptimalCover r (G.induce S) (fun v : S => p v) (fun v : S => c v) := by
  refine ⟨hc.1.restrict S, ?_⟩
  intro d hd
  have h := hc.2 (extendCover S d) hd.extend
  rw [← coverCost_restrict S p c hzero, coverCost_extend S p d hzero] at h
  exact h

/-- Conversely, an optimal cover of the positive-mass induced subgraph extends
to an optimal cover of the original graph when all discarded weights vanish. -/
theorem IsOptimalCover.extend {r : ℕ} {G : SimpleGraph V} {p : V → ℝ}
    {S : Set V} [Fintype S] {c : S → ℝ}
    (hc : IsOptimalCover r (G.induce S) (fun v : S => p v) c)
    (hzero : ∀ v ∉ S, p v = 0) :
    IsOptimalCover r G p (extendCover S c) := by
  refine ⟨hc.1.extend, ?_⟩
  intro d hd
  have h := hc.2 (fun v : S => d v) (hd.restrict S)
  rw [coverCost_restrict S p d hzero] at h
  rwa [coverCost_extend S p c hzero]

end DensityHS
