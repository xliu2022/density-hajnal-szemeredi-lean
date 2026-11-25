module

public import DensityHS.Graphon.Duality
public import DensityHS.Graphon.SamplingMoments

/-!
# Almost-everywhere invariance of kernel parameters

Author and maintainer: Xizhi Liu.

Clique conditions are imposed only on distinct coordinates of an independent
tuple. Consequently changing a kernel on a product-null set preserves its
cover number and its independently defined tiling number.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

theorem ae_clique_entries_congr {W U : Kernel Ω}
    (h : Function.uncurry W =ᵐ[μ.prod μ] Function.uncurry U) (r : ℕ) :
    ∀ᵐ t : Fin r → Ω ∂Measure.pi (fun _ => μ),
      ∀ i j, i ≠ j → W (t i) (t j) = U (t i) (t j) := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  by_cases hij : i = j
  · exact Filter.Eventually.of_forall (fun _ hne => (hne hij).elim)
  · have hm : MeasurePreserving (fun t : Fin r → Ω => (t i,t j))
        (Measure.pi (fun _ => μ)) (μ.prod μ) :=
      ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j), sampleMeasure_map_pair hij⟩
    exact (hm.quasiMeasurePreserving.ae h).mono (fun _ ht _ => ht)

theorem isKernelCover_congr_ae {r : ℕ} {W U : Kernel Ω} {c : Ω → ℝ}
    (h : Function.uncurry W =ᵐ[μ.prod μ] Function.uncurry U) :
    IsKernelCover r W μ c ↔ IsKernelCover r U μ c := by
  have hall := ae_clique_entries_congr h r
  constructor
  · rintro ⟨hc,hb,ht⟩
    refine ⟨hc,hb,?_⟩
    filter_upwards [ht,hall] with t ht he
    intro hcl
    apply ht
    intro i j hij
    rw [he i j hij]
    exact hcl i j hij
  · rintro ⟨hc,hb,ht⟩
    refine ⟨hc,hb,?_⟩
    filter_upwards [ht,hall] with t ht he
    intro hcl
    apply ht
    intro i j hij
    rw [← he i j hij]
    exact hcl i j hij

theorem coverNumber_congr_ae (r : ℕ) {W U : Kernel Ω}
    (h : Function.uncurry W =ᵐ[μ.prod μ] Function.uncurry U) :
    coverNumber r W μ = coverNumber r U μ := by
  apply congrArg sInf
  ext x
  simp only [kernelCoverCosts, Set.mem_setOf_eq]
  exact exists_congr fun c => and_congr_left fun _ => isKernelCover_congr_ae h

theorem tilingNumber_congr_ae {r : ℕ} (hr : 0 < r) {W U : Kernel Ω}
    (h : Function.uncurry W =ᵐ[μ.prod μ] Function.uncurry U) :
    tilingNumber r W μ = tilingNumber r U μ := by
  rw [kernel_tiling_cover_duality r W μ hr, kernel_tiling_cover_duality r U μ hr]
  exact coverNumber_congr_ae r h

theorem density_congr_ae {W U : Kernel Ω}
    (h : Function.uncurry W =ᵐ[μ.prod μ] Function.uncurry U) :
    density μ W = density μ U := by
  rw [density_eq_prod_integral, density_eq_prod_integral]
  exact congrArg (fun x : ℝ => x/2) (integral_congr_ae h)

end DensityHS.Graphon
