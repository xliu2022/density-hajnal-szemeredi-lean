module

public import DensityHS.Graphon.BlockCovers

/-!
# Removing complete zero-cover coordinates

Author and maintainer: Xizhi Liu.

An actual almost-everywhere `K_r` cover restricts to a lower-order clique
cover whenever the missing coordinates can be sampled from complete
zero-cover blocks. The proof transports the original null sets through the
actual product measures; no pointwise representative assertion is assumed.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory ProbabilityTheory Set Filter

variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurePreserving_coordinates_family {I J : Type*} [Fintype I] [Fintype J]
    (ν : J → Measure Ω) [∀ j, IsProbabilityMeasure (ν j)] (e : I ↪ J) :
    MeasurePreserving (fun z : J → Ω => z ∘ e) (Measure.pi ν) (Measure.pi (fun i => ν (e i))) := by
  have hind : iIndepFun (fun j (z : J → Ω) => z j) (Measure.pi ν) :=
    iIndepFun_pi (X := fun _ : J => id) (fun _ => aemeasurable_id)
  have he : iIndepFun (fun i (z : J → Ω) => z (e i)) (Measure.pi ν) := hind.precomp e.injective
  refine ⟨Measurable.of_eval (fun i => measurable_pi_apply (e i)), ?_⟩
  change (Measure.pi ν).map (fun z i => z (e i)) = _
  rw [he.map_fun_eq_pi_map (fun i => (measurable_pi_apply (e i)).aemeasurable)]
  congr 1
  funext i
  exact (measurePreserving_eval ν (e i)).map_eq

/-- Deleting zero-cover coordinates which are complete to all other
coordinates yields the genuine lower-order kernel cover. -/
theorem IsKernelCover.remove_zero_coordinates {r t : ℕ} {W : Kernel Ω}
    {μ ν : Measure Ω} [IsFiniteMeasure μ] [IsProbabilityMeasure ν] {c : Ω → ℝ}
    (hc : IsKernelCover r W μ c) (e : Fin t ↪ Fin r)
    (η : Fin r → Measure Ω) [∀ j, IsProbabilityMeasure (η j)]
    (hη : ∀ j, η j ≪ μ) (hkeep : ∀ i, η (e i) = ν)
    (hzero : ∀ j, j ∉ Set.range e → ∀ᵐ x ∂η j, c x = 0)
    (hcross : ∀ i j, i ≠ j → (i ∉ Set.range e ∨ j ∉ Set.range e) →
      ∀ᵐ z : Ω × Ω ∂(η i).prod (η j), 0 < W z.1 z.2) :
    IsKernelCover t W ν c := by
  classical
  have hcover : ∀ᵐ z : Fin r → Ω ∂Measure.pi η,
      z ∈ cliqueTuples r W → 1 ≤ coordinateSum r c z :=
    hc.2.2.filter_mono (absolutelyContinuous_finPi_family μ r η hη).ae_le
  have hzeros : ∀ᵐ z : Fin r → Ω ∂Measure.pi η,
      ∀ j, j ∉ Set.range e → c (z j) = 0 := by
    apply ae_all_iff.mpr
    intro j
    by_cases hj : j ∈ Set.range e
    · exact Eventually.of_forall fun _ h => False.elim (h hj)
    exact ((measurePreserving_eval η j).quasiMeasurePreserving.ae (hzero j hj)).mono
      fun _ hz _ => hz
  have hcrosses : ∀ᵐ z : Fin r → Ω ∂Measure.pi η,
      ∀ i j, i ≠ j → (i ∉ Set.range e ∨ j ∉ Set.range e) → 0 < W (z i) (z j) := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ h => False.elim (h hij)
    by_cases hout : i ∉ Set.range e ∨ j ∉ Set.range e
    · exact ((measurePreserving_pair_coordinates η hij).quasiMeasurePreserving.ae
        (hcross i j hij hout)).mono fun _ hz _ _ => hz
    · exact Eventually.of_forall fun _ _ h => False.elim (hout h)
  have hsource : ∀ᵐ z : Fin r → Ω ∂Measure.pi η,
      (z ∘ e) ∈ cliqueTuples t W → 1 ≤ coordinateSum t c (z ∘ e) := by
    filter_upwards [hcover, hzeros, hcrosses] with z hzc hz0 hzx hsmall
    have hbig : z ∈ cliqueTuples r W := by
      intro i j hij
      by_cases hi : i ∈ Set.range e
      · by_cases hj : j ∈ Set.range e
        · obtain ⟨a, rfl⟩ := hi
          obtain ⟨b, rfl⟩ := hj
          exact hsmall a b (fun h => hij (congrArg e h))
        · exact hzx i j hij (Or.inr hj)
      · exact hzx i j hij (Or.inl hi)
    have hsum : coordinateSum r c z = coordinateSum t c (z ∘ e) := by
      calc
        (∑ j : Fin r, c (z j)) = ∑ j ∈ Finset.univ.map e, c (z j) := by
          symm
          apply Finset.sum_subset (Finset.subset_univ _)
          intro j _ hj
          apply hz0 j
          rintro ⟨i, rfl⟩
          exact hj (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩)
        _ = ∑ i : Fin t, c (z (e i)) := by simp
    exact hsum ▸ hzc hbig
  have hproj : MeasurePreserving (fun z : Fin r → Ω => z ∘ e)
      (Measure.pi η) (Measure.pi (fun _ : Fin t => ν)) := by
    convert measurePreserving_coordinates_family η e using 1
    congr 1
    funext i
    exact (hkeep i).symm
  have hmeas : MeasurableSet {z : Fin t → Ω |
      z ∈ cliqueTuples t W → 1 ≤ coordinateSum t c z} := by
    convert (measurableSet_cliqueTuples t W).compl.union
      (measurableSet_le measurable_const (measurable_coordinateSum t hc.measurable)) using 1
    ext z
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_setOf_eq]
    tauto
  refine ⟨hc.measurable, hc.2.1, ?_⟩
  rw [← hproj.map_eq]
  exact (ae_map_iff hproj.measurable.aemeasurable hmeas).mpr hsource

end DensityHS.Graphon
