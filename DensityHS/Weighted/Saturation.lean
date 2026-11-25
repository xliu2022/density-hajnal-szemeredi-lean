module

public import DensityHS.Weighted.CompactOptimization
public import DensityHS.Weighted.SupportP3

/-!+# Saturation certificates at a global weight maximum

Author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS

open Finset

variable {V : Type*} [Fintype V]

theorem edgeMass_lt_of_le_of_new_edge {G H : SimpleGraph V} {p : V → ℝ}
    (hp : ∀ v, 0 < p v) (hle : G ≤ H) {u v : V}
    (hn : ¬ G.Adj u v) (he : H.Adj u v) : edgeMass G p < edgeMass H p := by
  classical
  have hterm (a b : V) :
      (if G.Adj a b then p a * p b else 0) ≤
      (if H.Adj a b then p a * p b else 0) := by
    by_cases hg : G.Adj a b
    · simp [hg, hle hg]
    · simp only [hg, ite_false]
      split_ifs
      · exact (mul_pos (hp a) (hp b)).le
      · rfl
  have hrow (a : V) :
      (∑ b, if G.Adj a b then p a * p b else 0) ≤
      ∑ b, if H.Adj a b then p a * p b else 0 :=
    Finset.sum_le_sum (fun b _ => hterm a b)
  have hstrict : (∑ b, if G.Adj u b then p u * p b else 0) <
      ∑ b, if H.Adj u b then p u * p b else 0 := by
    apply Finset.sum_lt_sum (fun b _ => hterm u b)
    exact ⟨v, Finset.mem_univ v, by simpa [hn, he] using mul_pos (hp u) (hp v)⟩
  have hs := Finset.sum_lt_sum (fun a _ => hrow a) ⟨u, Finset.mem_univ u, hstrict⟩
  unfold edgeMass
  linarith

theorem globalWeightMaximum_not_cover_after_add_edge
    {r : ℕ} {x : ℝ} {G : SimpleGraph V} {p c : V → ℝ}
    (hp : IsProbabilityWeight p) (hpos : ∀ v, 0 < p v)
    (hcost : coverCost p c ≤ x) (hmax : IsGlobalWeightMaximum r x G p)
    {u v : V} (hne : u ≠ v) (hn : ¬ G.Adj u v) :
    ¬ IsCliqueCover r (G ⊔ SimpleGraph.edge u v) c := by
  intro hc
  have hle := hmax _ p c hp hc hcost
  have he : (G ⊔ SimpleGraph.edge u v).Adj u v := Or.inr
    ((SimpleGraph.edge_adj ..).mpr ⟨Or.inl ⟨rfl, rfl⟩, hne⟩)
  exact not_lt_of_ge hle (edgeMass_lt_of_le_of_new_edge hpos le_sup_left hn he)

theorem old_clique_of_added_edge_endpoint_absent [DecidableEq V]
    {G : SimpleGraph V} {u v : V} {K : Finset V} {r : ℕ}
    (hK : (G ⊔ SimpleGraph.edge u v).IsNClique r K) (hu : u ∉ K) :
    G.IsNClique r K := by
  refine ⟨?_, hK.card_eq⟩
  intro a ha b hb hab
  rcases hK.isClique ha hb hab with h | h
  · exact h
  · rcases (SimpleGraph.edge_adj ..).mp h with ⟨h | h, _⟩
    · exact False.elim (hu (h.1 ▸ ha))
    · exact False.elim (hu (h.2 ▸ hb))

/-- A violated clique created by one edge yields the explicit common-neighbor
certificate, including the strict cover inequality. -/
theorem edgeSaturatedCover_of_not_cover_after_add_edge
    {r : ℕ} (hr : 2 ≤ r) {G : SimpleGraph V} {c : V → ℝ}
    (hc : IsCliqueCover r G c)
    (hadd : ∀ u v, u ≠ v → ¬ G.Adj u v →
      ¬ IsCliqueCover r (G ⊔ SimpleGraph.edge u v) c) :
    Weighted.Support.EdgeSaturatedCover r G c := by
  classical
  intro u v huv hn
  have hnew := hadd u v huv hn
  have hbad : ∃ K : Finset V, (G ⊔ SimpleGraph.edge u v).IsNClique r K ∧
      (∑ q ∈ K, c q) < 1 := by
    by_contra hh
    push Not at hh
    exact hnew ⟨hc.1, fun K hK => hh K hK⟩
  obtain ⟨K, hK, hsum⟩ := hbad
  have hu : u ∈ K := by
    by_contra hu
    exact not_lt_of_ge (hc.2 K (old_clique_of_added_edge_endpoint_absent hK hu)) hsum
  have hv : v ∈ K := by
    by_contra hv
    have hK' : (G ⊔ SimpleGraph.edge v u).IsNClique r K := by
      rwa [SimpleGraph.edge_comm]
    exact not_lt_of_ge (hc.2 K (old_clique_of_added_edge_endpoint_absent hK' hv)) hsum
  have hvu : v ∈ K.erase u := Finset.mem_erase.mpr ⟨Ne.symm huv, hv⟩
  let Q := (K.erase u).erase v
  have hQ : G.IsNClique (r - 2) Q := by
    have h := (hK.erase_of_sup_edge_of_mem hu).erase_of_mem hvu
    have heq : r - 1 - 1 = r - 2 := by omega
    simpa only [heq] using h
  refine ⟨Q, hQ, ?_, ?_⟩
  · intro q hq
    have hqu : q ≠ u := (Finset.mem_erase.mp (Finset.mem_erase.mp hq).2).1
    have hqv : q ≠ v := (Finset.mem_erase.mp hq).1
    have hqK : q ∈ K := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hq)
    constructor
    · have h := hK.isClique hu hqK (Ne.symm hqu)
      rcases h with h | h
      · exact h
      · rcases (SimpleGraph.edge_adj ..).mp h with ⟨h | h, _⟩
        · exact False.elim (hqv h.2)
        · exact False.elim (huv h.1)
    · have h := hK.isClique hv hqK (Ne.symm hqv)
      rcases h with h | h
      · exact h
      · rcases (SimpleGraph.edge_adj ..).mp h with ⟨h | h, _⟩
        · exact False.elim (huv h.1.symm)
        · exact False.elim (hqu h.2)
  · have h1 := Finset.sum_erase_add K c hu
    have h2 := Finset.sum_erase_add (K.erase u) c hvu
    dsimp [Q]
    linarith

theorem globalWeightMaximum_edgeSaturatedCover
    {r : ℕ} (hr : 2 ≤ r) {x : ℝ} {G : SimpleGraph V} {p c : V → ℝ}
    (hp : IsProbabilityWeight p) (hpos : ∀ v, 0 < p v)
    (hc : IsCliqueCover r G c) (hcost : coverCost p c ≤ x)
    (hmax : IsGlobalWeightMaximum r x G p) :
    Weighted.Support.EdgeSaturatedCover r G c := by
  apply edgeSaturatedCover_of_not_cover_after_add_edge hr hc
  intro u v huv hn
  exact globalWeightMaximum_not_cover_after_add_edge hp hpos hcost hmax huv hn

end DensityHS
