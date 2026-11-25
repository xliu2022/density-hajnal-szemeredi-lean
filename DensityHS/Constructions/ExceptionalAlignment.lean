module

public import DensityHS.Constructions.ExceptionalKernel
public import DensityHS.Constructions.PartitionLabels
public import DensityHS.Graphon.ExceptionalPartition

/-!
# Canonical interval representative of the exceptional equality model

Author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS.Constructions

open MeasureTheory Set Filter

variable {Ω : Type*} [MeasurableSpace Ω] {t : ℕ}

noncomputable def exceptionalLabel (C : Set Ω) (B : Fin t → Set Ω) (x : Ω) :
    Option (Option (Fin t)) := by
  classical
  exact if x ∈ C then none else some (finiteBlockLabel B x)

theorem exceptionalLabel_none_iff (C : Set Ω) (B : Fin t → Set Ω) (x : Ω) :
    exceptionalLabel C B x = none ↔ x ∈ C := by
  classical
  by_cases hx : x ∈ C <;> simp [exceptionalLabel, hx]

theorem exceptionalLabel_zero_iff (C : Set Ω) (B : Fin t → Set Ω) (x : Ω) :
    exceptionalLabel C B x = some none ↔ x ∉ C ∧ ∀ i, x ∉ B i := by
  classical
  by_cases hx : x ∈ C <;>
    simp [exceptionalLabel, hx, finiteBlockLabel_none_iff]

theorem exceptionalLabel_block_iff (C : Set Ω) (B : Fin t → Set Ω)
    (hd : Pairwise fun i j => Disjoint (B i) (B j))
    (hCB : ∀ i, Disjoint C (B i)) (i : Fin t) (x : Ω) :
    exceptionalLabel C B x = some (some i) ↔ x ∈ B i := by
  classical
  by_cases hx : x ∈ C
  · have hn : x ∉ B i := fun hxi => Set.disjoint_left.mp (hCB i) hx hxi
    simp [exceptionalLabel, hx, hn]
  · simp [exceptionalLabel, hx, finiteBlockLabel_some_iff B hd]

theorem measurable_exceptionalLabel
    [MeasurableSpace (Option (Option (Fin t)))]
    [MeasurableSingletonClass (Option (Option (Fin t)))] (C : Set Ω) (B : Fin t → Set Ω)
    (hC : MeasurableSet C) (hB : ∀ i, MeasurableSet (B i))
    (hd : Pairwise fun i j => Disjoint (B i) (B j)) :
    Measurable (exceptionalLabel C B) := by
  classical
  letI : MeasurableSpace (Option (Fin t)) := ⊤
  exact Measurable.ite hC measurable_const
    ((measurable_of_finite (some : Option (Fin t) → Option (Option (Fin t)))).comp
      (measurable_finiteBlockLabel B hB hd))

theorem exceptionalTemplate_row_block (i : Fin t) (v : Option (Option (Fin t)))
    (hv : v ≠ some (some i)) :
    (exceptionalTemplate t).entry (some (some i)) v = 1 := by
  classical
  cases v with
  | none => norm_num [exceptionalTemplate, exceptionalDefect]
  | some v => cases v with
    | none => norm_num [exceptionalTemplate, exceptionalDefect]
    | some j =>
      have hij : i ≠ j := by intro h; subst j; exact hv rfl
      simp [exceptionalTemplate, exceptionalDefect, hij]

theorem exceptional_step_identity (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Graphon.Kernel Ω) (C : Set Ω) (B : Fin t → Set Ω)
    (hd : Pairwise fun i j => Disjoint (B i) (B j)) (hCB : ∀ i, Disjoint C (B i))
    (hind : ∀ i, ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      z.1 ∈ B i → z.2 ∈ B i → W z.1 z.2 = 0)
    (hcross : ∀ i, ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      z.1 ∈ B i → z.2 ∉ B i → W z.1 z.2 = 1)
    (hrem : ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      (∀ i, z.1 ∉ B i) → (∀ i, z.2 ∉ B i) →
        W z.1 z.2 = (C ×ˢ C).indicator (fun _ => (1 : ℝ)) z) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ, W z.1 z.2 =
      (exceptionalTemplate t).entry (exceptionalLabel C B z.1) (exceptionalLabel C B z.2) := by
  classical
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    (ae_all_iff.mpr hcross)
  filter_upwards [ae_all_iff.mpr hind, ae_all_iff.mpr hcross, hswap, hrem]
    with z hi hc hs hr
  by_cases hleft : ∃ i, z.1 ∈ B i
  · obtain ⟨i, hxi⟩ := hleft
    have hlabel := (exceptionalLabel_block_iff C B hd hCB i z.1).mpr hxi
    rw [hlabel]
    by_cases hyi : z.2 ∈ B i
    · rw [hi i hxi hyi, (exceptionalLabel_block_iff C B hd hCB i z.2).mpr hyi]
      simp [exceptionalTemplate, exceptionalDefect]
    · rw [hc i hxi hyi]
      exact (exceptionalTemplate_row_block i _ (by
        intro h; exact hyi ((exceptionalLabel_block_iff C B hd hCB i z.2).mp h))).symm
  · have hleft' : ∀ i, z.1 ∉ B i := by simpa only [not_exists] using hleft
    by_cases hright : ∃ i, z.2 ∈ B i
    · obtain ⟨i, hyi⟩ := hright
      have hlabel := (exceptionalLabel_block_iff C B hd hCB i z.2).mpr hyi
      have hW : W z.1 z.2 = 1 := by
        rw [W.symmetric]
        exact hs i hyi (hleft' i)
      rw [hW, hlabel, (exceptionalTemplate t).symmetric]
      exact (exceptionalTemplate_row_block i _ (by
        intro h; exact hleft' i ((exceptionalLabel_block_iff C B hd hCB i z.1).mp h))).symm
    · have hright' : ∀ i, z.2 ∉ B i := by simpa only [not_exists] using hright
      have hblx := (finiteBlockLabel_none_iff B z.1).mpr hleft'
      have hbly := (finiteBlockLabel_none_iff B z.2).mpr hright'
      rw [hr hleft' hright']
      by_cases hxC : z.1 ∈ C <;> by_cases hyC : z.2 ∈ C <;>
        simp [exceptionalLabel, hxC, hyC, hblx, hbly, exceptionalTemplate,
          exceptionalDefect, Set.indicator]

end DensityHS.Constructions

namespace DensityHS.Graphon.ExceptionalPartition

open MeasureTheory Set Filter DensityHS.Constructions

theorem graphon_eq {r : ℕ} (hr : 2 ≤ r) {x : ℝ} (hx : ADomain r x) {W : Kernel ℝ}
    (P : ExceptionalPartition r x W unitMeasure) :
    Vendor.GraphonSpace.mk (W.toVendorGraphon unitMeasure) = exceptionalGraphon r x := by
  classical
  letI := P.fintype
  letI : MeasurableSpace (Option (Option (Fin (r - 2)))) := ⊤
  let e : P.Index ≃ Fin (r - 2) := Fintype.equivOfCardEq (by
    simpa only [Fintype.card_fin] using P.cardinality)
  let B : Fin (r - 2) → Set ℝ := fun j => P.block (e.symm j)
  have hB (j : Fin (r - 2)) : MeasurableSet (B j) := P.measurable _
  have hd : Pairwise fun j k => Disjoint (B j) (B k) := by
    intro j k hjk
    exact P.disjoint (e.symm.injective.ne hjk)
  have hCB (j : Fin (r - 2)) : Disjoint P.clique (B j) := P.clique_disjoint _
  have hm (j : Fin (r - 2)) : unitMeasure.real (B j) = 1 / ((r : ℝ) - 1) := P.mass _
  have hrr : ((r - 2 : ℕ) : ℝ) + 1 = (r : ℝ) - 1 := by
    rw [Nat.cast_sub hr]
    norm_num
    ring
  have hrp : (0 : ℝ) < (r : ℝ) - 1 := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  apply (exceptionalTemplate (r - 2)).graphon_eq_of_label W (exceptionalLabel P.clique B)
    (measurable_exceptionalLabel P.clique B P.clique_measurable hB hd)
    (exceptionalWeight_admissible hr hx)
  · intro i
    cases i with
    | none =>
      have he : {x | exceptionalLabel P.clique B x = none} = P.clique := by
        ext x
        exact exceptionalLabel_none_iff _ _ _
      rw [he]
      exact P.clique_mass
    | some i => cases i with
      | some j =>
        have he : {x | exceptionalLabel P.clique B x = some (some j)} = B j := by
          ext x
          exact exceptionalLabel_block_iff _ _ hd hCB _ _
        rw [he, hm j]
        simp only [exceptionalWeight, hrr]
      | none =>
        have he : {x | exceptionalLabel P.clique B x = some none} =
            (P.clique ∪ ⋃ j, B j)ᶜ := by
          ext x
          simp only [Set.mem_setOf_eq, exceptionalLabel_zero_iff, Set.mem_compl_iff,
            Set.mem_union, Set.mem_iUnion, not_or, not_exists]
        have hdu : Disjoint P.clique (⋃ j, B j) := by
          apply Set.disjoint_left.mpr
          intro x hx hxB
          obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxB
          exact Set.disjoint_left.mp (hCB j) hx hj
        rw [he, measureReal_compl (P.clique_measurable.union (MeasurableSet.iUnion hB)),
          probReal_univ, measureReal_union hdu (MeasurableSet.iUnion hB),
          P.clique_mass, measureReal_iUnion_fintype hd hB]
        simp only [hm, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, exceptionalWeight]
        rw [hrr, Nat.cast_sub hr, Nat.cast_ofNat]
        field_simp [ne_of_gt hrp]
        ring
  · apply exceptional_step_identity unitMeasure W P.clique B hd hCB
      (fun j => P.independent (e.symm j)) (fun j => P.complete_cross (e.symm j))
    filter_upwards [P.remainder] with z hz hxz hyz
    apply hz
    · intro j
      simpa only [B, e.symm_apply_apply] using hxz (e j)
    · intro j
      simpa only [B, e.symm_apply_apply] using hyz (e j)

end DensityHS.Graphon.ExceptionalPartition

