module

public import DensityHS.Constructions.FiniteTemplate
public import DensityHS.Graphon.RelabelL1

/-!
# Exact alignment of finite measurable labels

Author and maintainer: Xizhi Liu.

The alignment is an actual measure-preserving measurable bijection.
Zero-measure cells are discarded only in the finite matching argument;
the resulting label identity holds almost everywhere on the whole space.
-/

@[expose] public section

namespace DensityHS.Constructions

open MeasureTheory Set Filter
open scoped ENNReal

variable {Ω I : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

/-- Almost every point belongs to a positive-measure cell of a finite label. -/
theorem ae_label_fiber_positive (μ : Measure Ω) (f : Ω → I) :
    ∀ᵐ x ∂μ, 0 < μ {y | f y = f x} := by
  classical
  have hi (i : I) : ∀ᵐ x ∂μ, f x = i → 0 < μ {y | f y = i} := by
    by_cases h : 0 < μ {y | f y = i}
    · exact Eventually.of_forall fun _ _ => h
    · have hz : μ {y | f y = i} = 0 := le_antisymm (le_of_not_gt h) bot_le
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with x hx hxi
      exact (hx hxi).elim
  filter_upwards [ae_all_iff.mpr hi] with x hx
  exact hx (f x) rfl

/-- Two finite measurable labels with equal cell masses are aligned by a
measure-preserving measurable bijection, even when some cells have mass zero. -/
theorem exists_label_alignment (μ : Measure Ω) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] (f g : Ω → I) (hf : Measurable f) (hg : Measurable g)
    (hmass : ∀ i, μ {x | f x = i} = μ {x | g x = i}) :
    ∃ e : Ω ≃ᵐ Ω, ∃ he : MeasurePreserving e μ μ,
      ∀ᵐ x ∂μ, g (e x) = f x := by
  classical
  let J := {i : I // 0 < μ {x | f x = i}}
  let q : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let S : Fin (Fintype.card J) → Set Ω := fun j => {x | f x = (q.symm j).val}
  let T : Fin (Fintype.card J) → Set Ω := fun j => {x | g x = (q.symm j).val}
  have hS (j : Fin (Fintype.card J)) : MeasurableSet (S j) :=
    hf (measurableSet_singleton _)
  have hT (j : Fin (Fintype.card J)) : MeasurableSet (T j) :=
    hg (measurableSet_singleton _)
  have hSd : Pairwise fun i j => Disjoint (S i) (S j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have he : (q.symm i).val = (q.symm j).val := hxi.symm.trans hxj
    exact hij (q.symm.injective (Subtype.ext he))
  have hTd : Pairwise fun i j => Disjoint (T i) (T j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have he : (q.symm i).val = (q.symm j).val := hxi.symm.trans hxj
    exact hij (q.symm.injective (Subtype.ext he))
  have hSmass (j : Fin (Fintype.card J)) : 0 < μ (S j) := (q.symm j).property
  have hmatch (j : Fin (Fintype.card J)) : μ (S j) = μ (T j) := hmass _
  have hSinj : Function.Injective S := by
    intro i j he
    obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero (hSmass i).ne'
    have hy : x ∈ S j := he ▸ hx
    exact q.symm.injective (Subtype.ext (hx.symm.trans hy))
  have hTinj : Function.Injective T := by
    intro i j he
    have hpos : 0 < μ (T i) := by rw [← hmatch]; exact hSmass i
    obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero hpos.ne'
    have hy : x ∈ T j := he ▸ hx
    exact q.symm.injective (Subtype.ext (hx.symm.trans hy))
  let P := Vendor.MeasurablePartition.ofCells (μ := μ) S hS hSd
  let Q := Vendor.MeasurablePartition.ofCells (μ := μ) T hT hTd
  obtain ⟨e, he, halign⟩ :=
    Vendor.Graphon.MeasurePreserving.exists_controlled_cell_alignment P Q S T
      (fun j => Vendor.MeasurablePartition.mem_ofCells_parts j)
      (fun j => Vendor.MeasurablePartition.mem_ofCells_parts j) hSinj hTinj hmatch
  refine ⟨e, he, ?_⟩
  filter_upwards [ae_all_iff.mpr halign, ae_label_fiber_positive μ f] with x hx hpos
  let j : J := ⟨f x, hpos⟩
  have hmem : x ∈ S (q j) := by simp [S, j]
  have h := hx (q j) hmem
  simpa only [T, q.symm_apply_apply, j, Set.mem_setOf_eq] using h

/-- Every finite measured partition on the real unit interval has the
canonical weighted interval partition as an exact relabelled representative. -/
theorem exists_intervalLabel_alignment [Nonempty I] (f : ℝ → I) (hf : Measurable f)
    {p : I → ℝ} (hp : IsProbabilityWeight p)
    (hmass : ∀ i, unitMeasure.real {x | f x = i} = p i) :
    ∃ e : ℝ ≃ᵐ ℝ, ∃ he : MeasurePreserving e unitMeasure unitMeasure,
      ∀ᵐ x ∂unitMeasure, intervalLabel p (e x) = f x := by
  apply exists_label_alignment unitMeasure f (intervalLabel p) hf (measurable_intervalLabel p)
  intro i
  apply (measureReal_eq_measureReal_iff (μ := unitMeasure) (ν := unitMeasure)).mp
  rw [hmass i, intervalLabel_mass hp i]

/-- Almost-equal concrete kernels give equal vendor graphons. -/
theorem toVendorGraphon_eq_of_ae (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W U : Graphon.Kernel Ω)
    (h : Function.uncurry W =ᵐ[μ.prod μ] Function.uncurry U) :
    W.toVendorGraphon μ = U.toVendorGraphon μ := by
  apply Vendor.Graphon.ext
  apply Vendor.SymmKernel.ext
  apply AEEqFun.ext
  exact (W.toVendorGraphon_ae μ).trans (h.trans (U.toVendorGraphon_ae μ).symm)

/-- An actual measure-preserving relabelling yields equality in the compact
cut-distance quotient. -/
theorem graphonSpace_eq_of_relabel (μ : Measure Ω) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] (W U : Graphon.Kernel Ω) (e : Ω ≃ᵐ Ω)
    (he : MeasurePreserving e μ μ)
    (h : Function.uncurry W =ᵐ[μ.prod μ]
      Function.uncurry (U.comap e he.measurable)) :
    Vendor.GraphonSpace.mk (W.toVendorGraphon μ) =
      Vendor.GraphonSpace.mk (U.toVendorGraphon μ) := by
  rw [toVendorGraphon_eq_of_ae μ W _ h, Graphon.toVendorGraphon_comap U he,
    Vendor.GraphonSpace.mk_eq_mk_iff]
  change Vendor.Graphon.cutDistance
    (Vendor.Graphon.pullback (U.toVendorGraphon μ) e he) (U.toVendorGraphon μ) = 0
  rw [Vendor.Graphon.cutDistance_symm]
  exact Vendor.Graphon.cutDistance_pullback_eq_zero _ e he

/-- A finite step kernel with prescribed cell masses is exactly represented
by the weighted interval template in the compact graphon quotient. -/
theorem FiniteTemplate.graphon_eq_of_label [Nonempty I] (A : FiniteTemplate I)
    (W : Graphon.Kernel ℝ) (f : ℝ → I) (hf : Measurable f)
    {p : I → ℝ} (hp : IsProbabilityWeight p)
    (hmass : ∀ i, unitMeasure.real {x | f x = i} = p i)
    (hW : ∀ᵐ z : ℝ × ℝ ∂unitMeasure.prod unitMeasure,
      W z.1 z.2 = A.entry (f z.1) (f z.2)) :
    Vendor.GraphonSpace.mk (W.toVendorGraphon unitMeasure) = A.graphon p := by
  obtain ⟨e, he, halign⟩ := exists_intervalLabel_alignment f hf hp hmass
  apply graphonSpace_eq_of_relabel unitMeasure W (A.kernel p) e he
  have hfst := (Measure.quasiMeasurePreserving_fst (μ := unitMeasure) (ν := unitMeasure)).ae halign
  have hsnd := (Measure.quasiMeasurePreserving_snd (μ := unitMeasure) (ν := unitMeasure)).ae halign
  filter_upwards [hW, hfst, hsnd] with z hz hx hy
  change W z.1 z.2 = A.entry (intervalLabel p (e z.1)) (intervalLabel p (e z.2))
  rw [hx, hy]
  exact hz

end DensityHS.Constructions

