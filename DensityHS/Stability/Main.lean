module

public import DensityHS.Graphon.Classification
public import DensityHS.Stability.ClassificationTransfer
public import DensityHS.Stability.Consequences

/-!
# The unconditional stability theorem and its corollaries

Author and maintainer: Xizhi Liu.

The concrete graphon equality classification supplies the final input to
the proved compactness and integer edit-rounding argument.  The resulting
finite theorem is uniform in the packing parameter.  The sequence and
unique-active-branch consequences retain the actual finite construction
families and their exact integer size conditions.
-/

@[expose] public section

namespace DensityHS.Stability

open MeasureTheory Filter Set Graphon Constructions
open scoped Topology

attribute [local instance] Classical.propDecidable

/-- The proved finite stability property, with the classification and
model-persistence inputs discharged by actual theorems. -/
theorem finite_stability_property {r : ℕ} (hr : 3 ≤ r) : FiniteStability r := by
  intro ε η hε hη
  exact finite_stability_from_equality hr
    (fun x hx W ht he => graphonSpace_equality_classification hr hx W ht he) hε hη

/-- Uniform finite stability for the density Hajnal--Szemerédi theorem.
The comparison graph belongs to an actual integer construction family
whose branch density is within `η` of the envelope at the same parameter. -/
theorem finite_stability {r : ℕ} (hr : 3 ≤ r)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ > 0, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ k : ℕ, r * k ≤ n →
      ∀ G : SimpleGraph (Fin n), HasPackingNumberAtMost r G k →
      (Phi r ((k : ℝ) / n) - δ) * (n : ℝ) ^ 2 ≤ (G.edgeFinset.card : ℝ) →
      ∃ H : SimpleGraph (Fin n), H ∈ nearActiveFiniteFamily r k η ∧
        (editDistance G H : ℝ) < ε * (n : ℝ) ^ 2 :=
  finite_stability_property hr ε η hε hη

/-- Uniform graphon stability in the actual relabeled `L¹` distance, with
a construction at the original tiling parameter. -/
theorem graphon_L1_stability {r : ℕ} (hr : 3 ≤ r)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ > 0, ∀ x ∈ Icc 0 (1 / (r : ℝ)), ∀ W : Kernel ℝ,
      tilingNumber r W unitMeasure ≤ x → Phi r x - δ ≤ density unitMeasure W →
      ∃ t : ConstructionKind r, ∃ z : Fin (r - 1) → ℝ,
        IsProbabilityWeight z ∧ constructionDomain r t x ∧
        Phi r x - η ≤ constructionDensity r t x ∧
        relabelL1Distance unitMeasure W (constructionKernel r t (x, z)) < ε :=
  graphon_L1_stability_from_equality hr
    (fun x hx W ht he => graphonSpace_equality_classification hr hx W ht he) hε hη

/-- Sequence form: every asymptotically extremal packing-bounded sequence
admits exact finite construction models whose normalized edit error plus
branch deficit tends to zero. -/
theorem finite_stability_sequence_unconditional {r : ℕ} (hr : 3 ≤ r)
    (n k : ℕ → ℕ) (G : ∀ j : ℕ, SimpleGraph (Fin (n j)))
    (hn : Tendsto n atTop atTop) (hk : ∀ j, r * k j ≤ n j)
    (hpack : ∀ j, HasPackingNumberAtMost r (G j) (k j))
    (hdeficit : Tendsto (fun j => Phi r ((k j : ℝ) / n j) -
      ((G j).edgeFinset.card : ℝ) / (n j : ℝ) ^ 2) atTop (𝓝 0)) :
    ∃ t : ℕ → ConstructionKind r, ∃ E : ∀ j : ℕ, SimpleGraph (Fin (n j)),
      (∀ j, constructionDomain r (t j) ((k j : ℝ) / n j) ∧
        E j ∈ finiteConstructionFamily r (k j) (t j)) ∧
      Tendsto (fun j => (editDistance (G j) (E j) : ℝ) / (n j : ℝ) ^ 2 +
        (Phi r ((k j : ℝ) / n j) - constructionDensity r (t j) ((k j : ℝ) / n j)))
        atTop (𝓝 0) :=
  finite_stability_sequence hr (finite_stability_property hr) n k G hn hk hpack hdeficit

/-- On any compact parameter set with a unique active branch, all
sufficiently large near-extremal graphs are uniformly close to that
specific actual finite construction family. -/
theorem finite_stability_unique_range_unconditional {r : ℕ} (hr : 3 ≤ r)
    (J : Set ℝ) (hJ : IsCompact J) (hJrange : J ⊆ Icc 0 (1 / (r : ℝ)))
    (t₀ : ConstructionKind r)
    (hunique : ∀ x ∈ J, ∀ t : ConstructionKind r, constructionDomain r t x →
      constructionDensity r t x = Phi r x → t = t₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ k : ℕ, r * k ≤ n →
      (k : ℝ) / n ∈ J → ∀ G : SimpleGraph (Fin n), HasPackingNumberAtMost r G k →
      (Phi r ((k : ℝ) / n) - δ) * (n : ℝ) ^ 2 ≤ (G.edgeFinset.card : ℝ) →
      ∃ H : SimpleGraph (Fin n), H ∈ finiteConstructionFamily r k t₀ ∧
        (editDistance G H : ℝ) < ε * (n : ℝ) ^ 2 :=
  finite_stability_unique_range hr (finite_stability_property hr) J hJ hJrange t₀ hunique hε

end DensityHS.Stability
