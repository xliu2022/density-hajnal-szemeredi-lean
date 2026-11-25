module

public import DensityHS.Graphon.SamplingCover
public import DensityHS.Graphon.Tilings
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Typical clique tuples and independent coordinate replacements

Author and maintainer: Xizhi Liu.

An almost-everywhere tuple property remains valid for almost every
independent replacement of any one coordinate of almost every original
tuple. The proof uses actual measure-preserving finite-product maps.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Independent coordinate replacement preserves the product distribution. -/
theorem ae_coordinate_update {r : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (i : Fin r) {p : (Fin r → Ω) → Prop}
    (hp : ∀ᵐ z ∂Measure.pi (fun _ : Fin r => μ), p z) :
    ∀ᵐ z ∂Measure.pi (fun _ : Fin r => μ), ∀ᵐ w ∂μ, p (Function.update z i w) := by
  classical
  let e : Fin r ↪ Fin (r + 1) := {
    toFun := fun j => if j = i then 0 else j.succ
    inj' := by
      intro j k hjk
      by_cases hj : j = i <;> by_cases hk : k = i
      · exact hj.trans hk.symm
      · simp only [hj, if_pos rfl, if_neg hk] at hjk
        exact False.elim (Fin.succ_ne_zero k hjk.symm)
      · simp only [hk, if_pos rfl, if_neg hj] at hjk
        exact False.elim (Fin.succ_ne_zero j hjk)
      · simp only [if_neg hj, if_neg hk] at hjk
        exact Fin.succ_injective _ hjk }
  have hproj := measurePreserving_coordinates μ e
  have hins := (measurePreserving_piFinSuccAbove (fun _ : Fin (r + 1) => μ) 0).symm
  have hsource := (hproj.comp hins).quasiMeasurePreserving.ae hp
  have hpairs : ∀ᵐ z : Ω × (Fin r → Ω) ∂μ.prod (Measure.pi (fun _ : Fin r => μ)),
      p (Function.update z.2 i z.1) := by
    filter_upwards [hsource] with z hz
    have heq : ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => Ω) 0).symm z) ∘ e =
        Function.update z.2 i z.1 := by
      funext j
      simp only [Function.comp_apply, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv, Fin.insertNth_zero, Fin.zero_succAbove]
      by_cases hj : j = i
      · subst j
        change Fin.cons (α := fun _ : Fin (r + 1) => Ω) z.1 z.2 (if i = i then 0 else i.succ) = _
        simp
      · change Fin.cons (α := fun _ : Fin (r + 1) => Ω) z.1 z.2 (if j = i then 0 else j.succ) = _
        simp [hj]
    exact heq ▸ hz
  have hswap := (measurePreserving_swap (μ := Measure.pi (fun _ : Fin r => μ)) (ν := μ)).quasiMeasurePreserving.ae hpairs
  exact ae_ae_of_ae_prod hswap

/-- Every coordinate replacement of a typical tuple satisfies the actual
cover inequality whenever it is a clique. -/
theorem IsKernelCover.ae_typical_replacements {r : ℕ} {W : Kernel Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {c : Ω → ℝ}
    (hc : IsKernelCover r W μ c) :
    ∀ᵐ z ∂Measure.pi (fun _ : Fin r => μ), ∀ i : Fin r, ∀ᵐ w ∂μ,
      Function.update z i w ∈ cliqueTuples r W →
        1 ≤ coordinateSum r c (Function.update z i w) := by
  exact ae_all_iff.mpr fun i => ae_coordinate_update μ i hc.2.2

/-- A tuple with all unchanged pair edges and every new incident edge
positive remains a clique after replacing one coordinate. -/
theorem cliqueTuples_update {r : ℕ} {W : Kernel Ω} {z : Fin r → Ω}
    (hz : z ∈ cliqueTuples r W) (i : Fin r) (w : Ω)
    (hw : ∀ j, j ≠ i → 0 < W (z j) w) :
    Function.update z i w ∈ cliqueTuples r W := by
  classical
  intro j k hjk
  by_cases hj : j = i <;> by_cases hk : k = i
  · exact False.elim (hjk (hj.trans hk.symm))
  · subst j
    simpa only [Function.update_self, Function.update_of_ne hk, W.symmetric w (z k)] using hw k hk
  · subst k
    simpa only [Function.update_self, Function.update_of_ne hj] using hw j hj
  · simpa only [Function.update_of_ne hj, Function.update_of_ne hk] using hz j k hjk

theorem coordinateSum_update {r : ℕ} (c : Ω → ℝ) (z : Fin r → Ω) (i : Fin r) (w : Ω) :
    coordinateSum r c (Function.update z i w) = coordinateSum r c z - c (z i) + c w := by
  classical
  unfold coordinateSum
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
    ← Finset.sum_erase_add (Finset.univ : Finset (Fin r)) (fun j => c (z j)) (Finset.mem_univ i)]
  have hs : (∑ j ∈ (Finset.univ : Finset (Fin r)).erase i, c (Function.update z i w j)) =
      ∑ j ∈ (Finset.univ : Finset (Fin r)).erase i, c (z j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [hs, Function.update_self]
  ring

end DensityHS.Graphon
