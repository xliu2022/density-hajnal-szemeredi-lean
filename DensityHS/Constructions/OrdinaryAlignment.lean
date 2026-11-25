module

public import DensityHS.Constructions.OrdinaryKernel
public import DensityHS.Constructions.PartitionLabels
public import DensityHS.Graphon.OrdinaryClassification

/-!
# Canonical interval representative of the ordinary equality model

Author and maintainer: Xizhi Liu.

The measurable independent classes supplied by the equality classification
are aligned with the balanced interval cells by an actual measure-preserving
bijection. Their quotient graphon is therefore the concrete B construction.
-/

@[expose] public section

namespace DensityHS.Constructions

open MeasureTheory Set Filter

theorem ordinaryTemplate_entry_zero_iff {s : ℕ} (u v : Option (Fin s)) :
    (ordinaryTemplate s).entry u v = 0 ↔ ∃ i, u = some i ∧ v = some i := by
  classical
  cases u <;> cases v <;> simp [ordinaryTemplate]
  split_ifs <;> simp_all [eq_comm]

theorem ordinaryTemplate_entry_one_of_not_same {s : ℕ} (u v : Option (Fin s))
    (h : ¬∃ i, u = some i ∧ v = some i) : (ordinaryTemplate s).entry u v = 1 := by
  classical
  cases u <;> cases v <;> simp_all [ordinaryTemplate, eq_comm]

/-- An ordinary measurable partition gives its prescribed finite-template
label identity almost everywhere. -/
theorem ordinary_step_identity {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {s : ℕ} (W : Graphon.Kernel Ω) (C : Fin s → Set Ω)
    (hd : Pairwise fun i j => Disjoint (C i) (C j))
    (hind : ∀ i, ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      z.1 ∈ C i → z.2 ∈ C i → W z.1 z.2 = 0)
    (hcomplete : ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      (¬∃ i, z.1 ∈ C i ∧ z.2 ∈ C i) → W z.1 z.2 = 1) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ, W z.1 z.2 =
      (ordinaryTemplate s).entry (finiteBlockLabel C z.1) (finiteBlockLabel C z.2) := by
  classical
  filter_upwards [ae_all_iff.mpr hind, hcomplete] with z hi hc
  by_cases hsame : ∃ i, z.1 ∈ C i ∧ z.2 ∈ C i
  · obtain ⟨i, hxi, hyi⟩ := hsame
    rw [hi i hxi hyi]
    apply Eq.symm
    apply (ordinaryTemplate_entry_zero_iff _ _).mpr
    exact ⟨i, (finiteBlockLabel_some_iff C hd i _).mpr hxi,
      (finiteBlockLabel_some_iff C hd i _).mpr hyi⟩
  · rw [hc hsame, ordinaryTemplate_entry_one_of_not_same]
    rintro ⟨i, hxi, hyi⟩
    exact hsame ⟨i, (finiteBlockLabel_some_iff C hd i _).mp hxi,
      (finiteBlockLabel_some_iff C hd i _).mp hyi⟩

end DensityHS.Constructions

namespace DensityHS.Graphon.OrdinaryPartition

open MeasureTheory Set Filter DensityHS.Constructions

/-- The actual ordinary equality model has the canonical interval graphon
as its class in the compact cut-distance quotient. -/
theorem graphon_eq {r i : ℕ} (hir : i < r) {x : ℝ}
    (hx : x ∈ Icc 0 (1 / (r : ℝ))) {W : Kernel ℝ}
    (P : OrdinaryPartition r i x W unitMeasure) :
    Vendor.GraphonSpace.mk (W.toVendorGraphon unitMeasure) = ordinaryGraphon r i x := by
  classical
  letI := P.fintype
  letI : MeasurableSpace (Option (Fin (r - i))) := ⊤
  let e : P.Index ≃ Fin (r - i) := Fintype.equivOfCardEq (by
    simpa only [Fintype.card_fin] using P.cardinality)
  let C : Fin (r - i) → Set ℝ := fun j => P.block (e.symm j)
  have hC (j : Fin (r - i)) : MeasurableSet (C j) := P.measurable _
  have hd : Pairwise fun j k => Disjoint (C j) (C k) := by
    intro j k hjk
    exact P.disjoint (e.symm.injective.ne hjk)
  have hm (j : Fin (r - i)) :
      unitMeasure.real (C j) = (1 - (i : ℝ) * x) / ((r - i : ℕ) : ℝ) := P.mass _
  have hs : (0 : ℝ) < (r - i : ℕ) := by exact_mod_cast (by omega : 0 < r - i)
  apply (ordinaryTemplate (r - i)).graphon_eq_of_label W (finiteBlockLabel C)
    (measurable_finiteBlockLabel C hC hd) (ordinaryWeight_admissible hir hx)
  · intro j
    cases j with
    | none =>
      rw [finiteBlockLabel_mass_none unitMeasure C hC hd]
      simp only [hm, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ordinaryWeight]
      field_simp
      ring
    | some j =>
      rw [finiteBlockLabel_fiber_some C hd j]
      exact hm j
  · apply ordinary_step_identity unitMeasure W C hd (fun j => P.independent (e.symm j))
    filter_upwards [P.complete_outside] with z hz hnone
    apply hz
    rintro ⟨j, hxj, hyj⟩
    apply hnone
    refine ⟨e j, ?_, ?_⟩
    · simpa only [C, e.symm_apply_apply] using hxj
    · simpa only [C, e.symm_apply_apply] using hyj

end DensityHS.Graphon.OrdinaryPartition

