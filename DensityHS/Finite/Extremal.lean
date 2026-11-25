module

public import DensityHS.Finite.AsymptoticUpper

/-!
# The extremal number for disjoint clique packings

Author and maintainer: Xizhi Liu.

The extremal number is the maximum edge count of an actual finite graph
having no more than the prescribed number of disjoint cliques. Attainment
is proved explicitly, so the supremum is not a relaxed optimization problem.
-/

@[expose] public section

namespace DensityHS

/-- The number of undirected edges, independent of a decidability instance. -/
noncomputable def graphEdgeCount {V : Type*} (G : SimpleGraph V) : ℕ :=
  Nat.card G.edgeSet

theorem graphEdgeCount_eq {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    graphEdgeCount G = G.edgeFinset.card := by
  simp only [graphEdgeCount, Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card]

/-- The finite edge counts achievable under the integral packing restriction. -/
noncomputable def packingEdgeCounts (r n k : ℕ) : Set ℕ := by
  classical
  exact {m | ∃ G : SimpleGraph (Fin n), HasPackingNumberAtMost r G k ∧ graphEdgeCount G = m}

/-- The usual extremal number `ex(n,(k+1)K_r)`. -/
noncomputable def packingExtremalNumber (r n k : ℕ) : ℕ := sSup (packingEdgeCounts r n k)

theorem packingNumber_bot {r : ℕ} (hr : 2 ≤ r) (n k : ℕ) :
    HasPackingNumberAtMost r (⊥ : SimpleGraph (Fin n)) k := by
  intro P hP
  have hEmpty : P = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro K hK
    have h := (SimpleGraph.isNClique_bot_iff.mp (hP.1 K hK)).1
    omega
  simp [hEmpty]

theorem packingEdgeCounts_nonempty {r : ℕ} (hr : 2 ≤ r) (n k : ℕ) :
    (packingEdgeCounts r n k).Nonempty := by
  classical
  exact ⟨0, ⊥, packingNumber_bot hr n k, by simp [graphEdgeCount_eq]⟩

theorem packingEdgeCounts_bddAbove (r n k : ℕ) : BddAbove (packingEdgeCounts r n k) := by
  classical
  refine ⟨n.choose 2, ?_⟩
  rintro m ⟨G, _, rfl⟩
  simpa only [graphEdgeCount_eq, Fintype.card_fin] using G.card_edgeFinset_le_card_choose_two

/-- There is a graph attaining the extremal number. -/
theorem exists_extremal_packing_graph {r : ℕ} (hr : 2 ≤ r) (n k : ℕ) :
    ∃ G : SimpleGraph (Fin n), HasPackingNumberAtMost r G k ∧
      graphEdgeCount G = packingExtremalNumber r n k := by
  classical
  have h := Nat.sSup_mem (packingEdgeCounts_nonempty hr n k)
    (packingEdgeCounts_bddAbove r n k)
  exact h

/-- Every admissible graph has at most the extremal number of edges. -/
theorem card_edges_le_packingExtremalNumber {r n k : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hG : HasPackingNumberAtMost r G k) :
    G.edgeFinset.card ≤ packingExtremalNumber r n k := by
  classical
  exact le_csSup (packingEdgeCounts_bddAbove r n k) ⟨G, hG, graphEdgeCount_eq G⟩

/-- Uniform asymptotic upper bound stated directly for the classical extremal
number. The quantifier over `k` is inside the uniform order threshold. -/
theorem packingExtremalNumber_upper {r : ℕ} (hr : 3 ≤ r) {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ k : ℕ, r * k ≤ n →
      (packingExtremalNumber r n k : ℝ) ≤
        (Phi r ((k : ℝ) / n) + ε) * (n : ℝ) ^ 2 := by
  classical
  obtain ⟨n₀, hbound⟩ := Regularity.finite_density_upper_bound_fin hr hε
  refine ⟨n₀, ?_⟩
  intro n hn k hk
  obtain ⟨G, hG, he⟩ := exists_extremal_packing_graph (by omega : 2 ≤ r) n k
  have h := hbound n hn G k hk hG
  rw [← graphEdgeCount_eq G, he] at h
  exact h

end DensityHS
