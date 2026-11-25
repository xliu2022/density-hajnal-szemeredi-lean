module

public import DensityHS.Graphon.RSupport
public import DensityHS.Graphon.PeelingCover

/-!
# Extending marked tuples by complete measurable blocks

Author and maintainer: Xizhi Liu.

Every exclusion is transported through the actual finite product measures.
In particular no complete rectangle is extracted from an arbitrary positive
measure set of edges.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory ProbabilityTheory Set Filter

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A marked clique exclusion remains valid for any finite indexing set and
any absolutely continuous probability distribution at each coordinate. -/
theorem NoCliqueMeets.ae_family {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Z : Set Ω} (hfree : NoCliqueMeets r W μ Z)
    {I : Type*} [Fintype I] (hcard : Fintype.card I = r)
    (η : I → Measure Ω) [∀ i, IsProbabilityMeasure (η i)] (hη : ∀ i, η i ≪ μ) :
    ∀ᵐ z : I → Ω ∂Measure.pi η,
      (∀ i j, i ≠ j → 0 < W (z i) (z j)) → ∀ i, z i ∉ Z := by
  classical
  let e : Fin r ≃ I := (Fintype.equivFinOfCardEq hcard).symm
  have hn : ∀ᵐ z : Fin r → Ω ∂Measure.pi (fun i => η (e i)),
      z ∈ cliqueTuples r W → ∀ i, z i ∉ Z :=
    hfree.filter_mono (absolutelyContinuous_finPi_family μ r (fun i => η (e i))
      (fun i => hη (e i))).ae_le
  have hp := (measurePreserving_coordinates_family η e.toEmbedding).quasiMeasurePreserving.ae hn
  filter_upwards [hp] with z hz hcl i
  have hsmall : (z ∘ e) ∈ cliqueTuples r W := fun a b hab =>
    hcl (e a) (e b) (fun he => hab (e.injective he))
  simpa only [Function.comp_apply, Equiv.coe_toEmbedding, Equiv.apply_symm_apply] using hz hsmall (e.symm i)

/-- A marked `k`-tuple cannot be completed to a forbidden `r`-clique by
independently sampling one point in each of a finite family of positive
complete blocks. The neighbor conditions are imposed on the original
free coordinates and may depend on the block. -/
theorem NoCliqueMeets.forbid_extension {r k : ℕ} (hk : 0 < k)
    {W : Kernel Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z : Set Ω} (hZ : MeasurableSet Z) (hfree : NoCliqueMeets r W μ Z)
    {J : Type*} [Fintype J] (hcard : k + Fintype.card J = r)
    (C S : J → Set Ω) (hC : ∀ j, MeasurableSet (C j))
    (hC0 : ∀ j, μ (C j) ≠ 0) (hS : ∀ j, MeasurableSet (S j))
    (hCC : ∀ i j, i ≠ j → ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      z.1 ∈ C i → z.2 ∈ C j → 0 < W z.1 z.2)
    (hSC : ∀ j, ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      z.1 ∈ S j → z.2 ∈ C j → 0 < W z.1 z.2) :
    ∀ᵐ z : Fin k → Ω ∂Measure.pi (fun _ => μ),
      ¬ ((∀ a, z a ∈ Z) ∧ z ∈ cliqueTuples k W ∧ ∀ a j, z a ∈ S j) := by
  classical
  let η : Fin k ⊕ J → Measure Ω := Sum.elim (fun _ => μ) (fun j => cond μ (C j))
  letI : ∀ i, IsProbabilityMeasure (η i) := by
    intro i
    cases i with
    | inl a => exact inferInstanceAs (IsProbabilityMeasure μ)
    | inr j => exact cond_isProbabilityMeasure (hC0 j)
  have hη : ∀ i, η i ≪ μ := by
    intro i
    cases i with
    | inl a => exact Measure.AbsolutelyContinuous.rfl
    | inr j => exact cond_absolutelyContinuous
  have hbig := hfree.ae_family (I := Fin k ⊕ J)
    (by simpa only [Fintype.card_sum, Fintype.card_fin] using hcard) η hη
  have hfixed : ∀ᵐ z : Fin k ⊕ J → Ω ∂Measure.pi η,
      ∀ i j : J, i ≠ j → 0 < W (z (.inr i)) (z (.inr j)) := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ h => False.elim (h hij)
    have he := cross_positive_cond W μ (hC i) (hC j) (hCC i j hij)
    exact ((measurePreserving_pair_coordinates η
      (show (Sum.inr i : Fin k ⊕ J) ≠ .inr j from fun h => hij (Sum.inr.inj h))).quasiMeasurePreserving.ae he).mono
        fun _ hz _ => hz
  have hfreefixed : ∀ᵐ z : Fin k ⊕ J → Ω ∂Measure.pi η,
      ∀ a : Fin k, ∀ j : J, z (.inl a) ∈ S j → 0 < W (z (.inl a)) (z (.inr j)) := by
    apply ae_all_iff.mpr
    intro a
    apply ae_all_iff.mpr
    intro j
    have he : ∀ᵐ z : Ω × Ω ∂μ.prod (cond μ (C j)), z.1 ∈ S j → 0 < W z.1 z.2 := by
      have hac := (Measure.AbsolutelyContinuous.rfl (μ := μ)).prod
        (cond_absolutelyContinuous (μ := μ) (s := C j))
      filter_upwards [(hSC j).filter_mono hac.ae_le,
        Measure.quasiMeasurePreserving_snd.ae (ae_cond_mem (hC j))] with z hz hy hx
      exact hz hx hy
    exact (measurePreserving_pair_coordinates η
      (show (Sum.inl a : Fin k ⊕ J) ≠ .inr j from Sum.inl_ne_inr)).quasiMeasurePreserving.ae he
  let e : Fin k ↪ Fin k ⊕ J := ⟨Sum.inl, Sum.inl_injective⟩
  let P : (Fin k → Ω) → Prop := fun z =>
    (∀ a, z a ∈ Z) ∧ z ∈ cliqueTuples k W ∧ ∀ a j, z a ∈ S j
  have hsource : ∀ᵐ z : Fin k ⊕ J → Ω ∂Measure.pi η, ¬ P (z ∘ e) := by
    filter_upwards [hbig, hfixed, hfreefixed] with z hz hx hy hp
    have hc : ∀ i j : Fin k ⊕ J, i ≠ j → 0 < W (z i) (z j) := by
      intro i j hij
      cases i with
      | inl a =>
        cases j with
        | inl b => exact hp.2.1 a b (fun h => hij (congrArg Sum.inl h))
        | inr j => exact hy a j (hp.2.2 a j)
      | inr i =>
        cases j with
        | inl a => simpa only [W.symmetric] using hy a i (hp.2.2 a i)
        | inr j => exact hx i j (fun h => hij (congrArg Sum.inr h))
    exact hz hc (.inl ⟨0, hk⟩) (hp.1 ⟨0, hk⟩)
  have hmeas : MeasurableSet {z : Fin k → Ω | ¬ P z} := by
    apply MeasurableSet.compl
    have heq : {z : Fin k → Ω | P z} =
        (⋂ a, (fun z : Fin k → Ω => z a) ⁻¹' Z) ∩
          (cliqueTuples k W ∩ ⋂ a, ⋂ j, (fun z : Fin k → Ω => z a) ⁻¹' S j) := by
      ext z
      simp only [P, mem_setOf_eq, mem_inter_iff, mem_iInter, mem_preimage]
    change MeasurableSet {z : Fin k → Ω | P z}
    rw [heq]
    exact (MeasurableSet.iInter fun a => hZ.preimage (measurable_pi_apply a)).inter
      ((measurableSet_cliqueTuples k W).inter
        (MeasurableSet.iInter fun a => MeasurableSet.iInter fun j =>
          (hS j).preimage (measurable_pi_apply a)))
  have hproj : MeasurePreserving (fun z : Fin k ⊕ J → Ω => z ∘ e)
      (Measure.pi η) (Measure.pi (fun _ : Fin k => μ)) :=
    measurePreserving_coordinates_family η e
  change ∀ᵐ z : Fin k → Ω ∂Measure.pi (fun _ => μ), ¬ P z
  rw [← hproj.map_eq]
  exact (ae_map_iff hproj.measurable.aemeasurable hmeas).mpr hsource

/-- Positive complete blocks of total size `r` cannot include a marked
block. This also permits a repeated block when it is internally complete. -/
theorem NoCliqueMeets.not_complete_blocks {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Z : Set Ω} (hfree : NoCliqueMeets r W μ Z)
    {I : Type*} [Fintype I] (hcard : Fintype.card I = r)
    (C : I → Set Ω) (hC : ∀ i, MeasurableSet (C i)) (hC0 : ∀ i, μ (C i) ≠ 0)
    (hcross : ∀ i j, i ≠ j → ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      z.1 ∈ C i → z.2 ∈ C j → 0 < W z.1 z.2)
    (i : I) (hi : C i ⊆ Z) : False := by
  let η : I → Measure Ω := fun j => cond μ (C j)
  letI : ∀ j, IsProbabilityMeasure (η j) := fun j => cond_isProbabilityMeasure (hC0 j)
  have hf := hfree.ae_family hcard η (fun _ => cond_absolutelyContinuous)
  have hclique : ∀ᵐ z : I → Ω ∂Measure.pi η,
      ∀ a b, a ≠ b → 0 < W (z a) (z b) := by
    apply ae_all_iff.mpr
    intro a
    apply ae_all_iff.mpr
    intro b
    by_cases hab : a = b
    · exact Eventually.of_forall fun _ h => False.elim (h hab)
    · exact ((measurePreserving_pair_coordinates η hab).quasiMeasurePreserving.ae
        (cross_positive_cond W μ (hC a) (hC b) (hcross a b hab))).mono fun _ hz _ => hz
  have hmem : ∀ᵐ z : I → Ω ∂Measure.pi η, z i ∈ C i :=
    (measurePreserving_eval η i).quasiMeasurePreserving.ae (ae_cond_mem (hC i))
  obtain ⟨z, hz, hc, hm⟩ := (hf.and (hclique.and hmem)).exists
  exact hz hc i (hi hm)

end DensityHS.Graphon
