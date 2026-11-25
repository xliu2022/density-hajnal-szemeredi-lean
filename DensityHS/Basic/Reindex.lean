module

public import DensityHS.Basic.WeightedGraph

/-!
# Reindexing finite weighted graphs

Author and maintainer: Xizhi Liu.

Equivalences of vertex types preserve all data used by support minimization.
-/

@[expose] public section

namespace DensityHS

open Finset

attribute [local instance] Classical.propDecidable

variable {V W : Type*}

/-- A cover pulls back along an injective map of vertex labels. -/
theorem IsCliqueCover.pullback {r : ℕ} {G : SimpleGraph V} {c : V → ℝ}
    (hc : IsCliqueCover r G c) (e : W ↪ V) :
    IsCliqueCover r (G.comap e) (fun w => c (e w)) := by
  classical
  refine ⟨fun w => hc.1 (e w), ?_⟩
  intro K hK
  have hK' : G.IsNClique r (K.map e) :=
    SimpleGraph.IsNClique.mono (SimpleGraph.map_comap_le e G) hK.map
  simpa only [Finset.sum_map] using hc.2 (K.map e) hK'

/-- Relabeling vertices by an equivalence preserves covers. -/
theorem IsCliqueCover.reindex {r : ℕ} {G : SimpleGraph V} {c : V → ℝ}
    (hc : IsCliqueCover r G c) (e : W ≃ V) :
    IsCliqueCover r (G.comap e) (fun w => c (e w)) :=
  hc.pullback e.toEmbedding

variable [Fintype V] [Fintype W]

theorem IsProbabilityWeight.reindex {p : V → ℝ} (hp : IsProbabilityWeight p)
    (e : W ≃ V) : IsProbabilityWeight (fun w => p (e w)) := by
  refine ⟨fun w => hp.1 (e w), ?_⟩
  exact (e.sum_comp p).trans hp.2

/-- Cover cost is invariant under a bijective change of vertex labels. -/
theorem coverCost_reindex (e : W ≃ V) (p c : V → ℝ) :
    coverCost (fun w => p (e w)) (fun w => c (e w)) = coverCost p c :=
  e.sum_comp (fun v => p v * c v)

/-- Weighted edge mass is invariant under a bijective change of labels. -/
theorem edgeMass_reindex (e : W ≃ V) (G : SimpleGraph V) (p : V → ℝ) :
    edgeMass (G.comap e) (fun w => p (e w)) = edgeMass G p := by
  classical
  unfold edgeMass
  congr 1
  calc
    (∑ u : W, ∑ v : W, if (G.comap e).Adj u v then p (e u) * p (e v) else 0) =
        ∑ u : W, ∑ v : V, if G.Adj (e u) v then p (e u) * p v else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      exact e.sum_comp (fun v => if G.Adj (e u) v then p (e u) * p v else 0)
    _ = ∑ u : V, ∑ v : V, if G.Adj u v then p u * p v else 0 :=
      e.sum_comp (fun u => ∑ v : V, if G.Adj u v then p u * p v else 0)

/-- Relabeling preserves cover optimality, including zero vertex weights. -/
theorem IsOptimalCover.reindex {r : ℕ} {G : SimpleGraph V} {p c : V → ℝ}
    (hc : IsOptimalCover r G p c) (e : W ≃ V) :
    IsOptimalCover r (G.comap e) (fun w => p (e w)) (fun w => c (e w)) := by
  refine ⟨hc.1.reindex e, ?_⟩
  intro d hd
  have hd' : IsCliqueCover r G (fun v => d (e.symm v)) := by
    have hg : (G.comap e).comap e.symm = G := by ext u v; simp
    have hd' := hd.reindex e.symm
    rwa [hg] at hd'
  have h := hc.2 (fun v => d (e.symm v)) hd'
  rw [coverCost_reindex]
  have heq := coverCost_reindex e p (fun v => d (e.symm v))
  simpa only [Equiv.symm_apply_apply] using h.trans_eq heq.symm

end DensityHS
