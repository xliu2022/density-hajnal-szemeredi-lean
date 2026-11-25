module

public import DensityHS.Graphon.Basic
public import Mathlib.Probability.Independence.Basic

/-!
# Sampling a kernel clique cover

Author and maintainer: Xizhi Liu.

An injective choice of coordinates of a finite independent sample has the
corresponding product distribution.  Applying this simultaneously to all
labelled clique embeddings proves that a kernel cover restricts to an actual
finite cover for almost every sample.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Selecting distinct coordinates from a finite independent sample preserves
the product probability distribution. -/
theorem measurePreserving_coordinates (μ : Measure Ω) [IsProbabilityMeasure μ]
    {I J : Type*} [Fintype I] [Fintype J] (e : I ↪ J) :
    MeasurePreserving (fun ω : J → Ω => ω ∘ e)
      (Measure.pi (fun _ : J => μ)) (Measure.pi (fun _ : I => μ)) := by
  have hind : iIndepFun (fun j (ω : J → Ω) => ω j) (Measure.pi (fun _ : J => μ)) :=
    iIndepFun_pi (X := fun _ : J => id) (fun _ => aemeasurable_id)
  have he : iIndepFun (fun i (ω : J → Ω) => ω (e i))
      (Measure.pi (fun _ : J => μ)) := hind.precomp e.injective
  refine ⟨Measurable.of_eval (fun i => measurable_pi_apply (e i)), ?_⟩
  change (Measure.pi (fun _ : J => μ)).map (fun ω i => ω (e i)) = _
  rw [he.map_fun_eq_pi_map (fun i => (measurable_pi_apply (e i)).aemeasurable)]
  congr 1
  funext i
  exact (measurePreserving_eval (fun _ : J => μ) (e i)).map_eq

/-- A single labelled clique embedding satisfies the sampled cover inequality
almost surely. -/
theorem IsKernelCover.ae_embedding {r n : ℕ} {W : Kernel Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {c : Ω → ℝ}
    (hc : IsKernelCover r W μ c) (e : Fin r ↪ Fin n) :
    ∀ᵐ ω : Fin n → Ω ∂Measure.pi (fun _ => μ),
      (∀ i j, i ≠ j → 0 < W (ω (e i)) (ω (e j))) →
        1 ≤ ∑ i, c (ω (e i)) :=
  (measurePreserving_coordinates μ e).quasiMeasurePreserving.ae hc.2.2

/-- For almost every sample, restricting a kernel clique cover gives a finite
fractional cover of every `r`-clique of the sampled support graph. -/
theorem IsKernelCover.ae_sampleCover {r : ℕ} {W : Kernel Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {c : Ω → ℝ}
    (hc : IsKernelCover r W μ c) (n : ℕ) :
    ∀ᵐ ω : Fin n → Ω ∂Measure.pi (fun _ => μ),
      DensityHS.IsCliqueCover r (sampleGraph W n ω) (sampleCover c ω) := by
  classical
  have hall : ∀ᵐ ω : Fin n → Ω ∂Measure.pi (fun _ => μ),
      ∀ e : Fin r ↪ Fin n,
        (∀ i j, i ≠ j → 0 < W (ω (e i)) (ω (e j))) →
          1 ≤ ∑ i, c (ω (e i)) :=
    ae_all_iff.mpr hc.ae_embedding
  filter_upwards [hall] with ω hω
  refine ⟨fun i => hc.nonneg (ω i), ?_⟩
  intro K hK
  let eK : Fin r ≃ K := (K.equivFinOfCardEq hK.card_eq).symm
  let e : Fin r ↪ Fin n :=
    ⟨fun i => (eK i).1, fun i j hij => eK.injective (Subtype.ext hij)⟩
  have hclique : ∀ i j, i ≠ j → 0 < W (ω (e i)) (ω (e j)) := by
    intro i j hij
    exact (hK.isClique (eK i).2 (eK j).2
      (fun h => hij (e.injective h))).2
  have hsum := hω e hclique
  have heq : (∑ i : Fin r, c (ω (e i))) = ∑ v ∈ K, c (ω v) := by
    calc
      (∑ i : Fin r, c (ω (e i))) = ∑ v : K, c (ω v) :=
        eK.sum_comp (fun v : K => c (ω v))
      _ = ∑ v ∈ K, c (ω v) := Finset.sum_coe_sort K (fun v => c (ω v))
  simpa only [heq, sampleCover_apply] using hsum

end DensityHS.Graphon
