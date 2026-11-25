module

public import DensityHS.Stability.GraphonCompactness
public import DensityHS.Constructions.FamilyPersistence

/-!
# Stability implications with concrete model persistence supplied

Author and maintainer: Xizhi Liu.

All construction-continuity hypotheses of the compactness implications
are discharged here. The sole remaining mathematical input is the full
equality classification, including transitions and endpoints.
-/

@[expose] public section

namespace DensityHS.Stability

open MeasureTheory Set Graphon Constructions

theorem active_model_local_approximation {r : ℕ} (hr : 3 ≤ r)
    (x : ℝ) (_hx : x ∈ Icc 0 (1/(r : ℝ)))
    (W : Vendor.GraphonSpace ℝ unitMeasure) (hW : W ∈ activeFamily r x)
    (ρ η : ℝ) (hρ : 0 < ρ) (hη : 0 < η) :
    ∃ a > 0, ∀ y ∈ Icc 0 (1/(r : ℝ)), |y-x| < a →
      ∃ U ∈ nearActiveFamily r y η, dist W U < ρ := by
  obtain ⟨a, ha, h⟩ := activeFamily_persists hr hW hρ hη
  refine ⟨a, ha, ?_⟩
  intro y hy hxy
  obtain ⟨U, hU, hd⟩ := h y hy hxy
  exact ⟨U, hU, by simpa only [dist_comm] using hd⟩

attribute [local instance] Classical.propDecidable

theorem finite_stability_from_equality {r : ℕ} (hr : 3 ≤ r)
    (hclassification : ∀ x ∈ Icc 0 (1/(r : ℝ)),
      ∀ W : Vendor.GraphonSpace ℝ unitMeasure,
      graphonSpaceTilingNumber unitMeasure r (by omega) W ≤ x →
      graphonSpaceDensity unitMeasure W = Phi r x → W ∈ activeFamily r x)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ > 0, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ k : ℕ, r*k ≤ n →
      ∀ G : SimpleGraph (Fin n), HasPackingNumberAtMost r G k →
      (Phi r ((k : ℝ)/n)-δ)*(n : ℝ)^2 ≤ (G.edgeFinset.card : ℝ) →
      ∃ H : SimpleGraph (Fin n), H ∈ nearActiveFiniteFamily r k η ∧
        (editDistance G H : ℝ) < ε*(n : ℝ)^2 :=
  finite_stability_of_classification hr hclassification
    (active_model_local_approximation hr) hε hη

theorem graphon_L1_stability_from_equality {r : ℕ} (hr : 3 ≤ r)
    (hclassification : ∀ x ∈ Icc 0 (1/(r : ℝ)),
      ∀ W : Vendor.GraphonSpace ℝ unitMeasure,
      graphonSpaceTilingNumber unitMeasure r (by omega) W ≤ x →
      graphonSpaceDensity unitMeasure W = Phi r x → W ∈ activeFamily r x)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ > 0, ∀ x ∈ Icc 0 (1/(r : ℝ)), ∀ W : Kernel ℝ,
      tilingNumber r W unitMeasure ≤ x → Phi r x-δ ≤ density unitMeasure W →
      ∃ t : ConstructionKind r, ∃ z : Fin (r-1) → ℝ,
        IsProbabilityWeight z ∧ constructionDomain r t x ∧
        Phi r x-η ≤ constructionDensity r t x ∧
        relabelL1Distance unitMeasure W (constructionKernel r t (x,z)) < ε :=
  graphon_L1_stability_of_classification hr hclassification
    (active_model_local_approximation hr) hε hη

end DensityHS.Stability
