module

public import DensityHS.Graphon.FlatMeasure
public import DensityHS.Graphon.ZeroTwinData

/-!
# Finite termination of measure uncrossing

Author and maintainer: Xizhi Liu.

All original class indices and all original defect sets are retained.
Absolute continuity cannot create a positive class or a positive Boolean
atom.  Killing a positive class, or a positive difference of two defects,
strictly lowers their combined finite count.  Strong induction therefore
terminates the sequence of actual absolutely continuous measure changes.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory MeasureTheory.Measure Filter Set Finset

variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]

attribute [local instance] Classical.propDecidable

/-- A Boolean atom of the full original defect family, restricted to `P`. -/
def defectAtom (P : Set Ω) (D : I → Set Ω) (a : Finset I) : Set Ω :=
  P ∩ ⋂ i : I, if i ∈ a then D i else (D i)ᶜ

theorem mem_defectAtom {P : Set Ω} {D : I → Set Ω} {a : Finset I} {x : Ω} :
    x ∈ defectAtom P D a ↔ x ∈ P ∧ ∀ i, x ∈ D i ↔ i ∈ a := by
  simp only [defectAtom, Set.mem_inter_iff, Set.mem_iInter]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro i
  by_cases hi : i ∈ a <;> simp [hi]

theorem measurableSet_defectAtom {P : Set Ω} {D : I → Set Ω}
    (hP : MeasurableSet P) (hD : ∀ i, MeasurableSet (D i)) (a : Finset I) :
    MeasurableSet (defectAtom P D a) := by
  apply hP.inter
  apply MeasurableSet.iInter
  intro i
  by_cases hi : i ∈ a
  · simpa only [if_pos hi] using hD i
  · simpa only [if_neg hi] using (hD i).compl

theorem exists_mem_defectAtom {P : Set Ω} (D : I → Set Ω) {x : Ω}
    (hx : x ∈ P) : ∃ a : Finset I, x ∈ defectAtom P D a := by
  refine ⟨univ.filter (fun i => x ∈ D i), mem_defectAtom.mpr ⟨hx, ?_⟩⟩
  intro i
  simp

/-- A positive difference contains a positive atom of the original family. -/
theorem exists_positive_defectAtom_in_sdiff {μ : Measure Ω} {P : Set Ω}
    {D : I → Set Ω} {i j : I} (hDi : D i ⊆ P) (hμ : μ (D i \ D j) ≠ 0) :
    ∃ a : Finset I, μ (defectAtom P D a) ≠ 0 ∧ defectAtom P D a ⊆ D i \ D j := by
  have hcover : D i \ D j = ⋃ a : Finset I, (D i \ D j) ∩ defectAtom P D a := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, ha⟩ := exists_mem_defectAtom D (hDi hx.1)
      exact Set.mem_iUnion.mpr ⟨a, hx, ha⟩
    · intro hx
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
      exact ha.1
  have hsome : ∃ a : Finset I, μ ((D i \ D j) ∩ defectAtom P D a) ≠ 0 := by
    by_contra hnone
    push_neg at hnone
    apply hμ
    rw [hcover]
    exact measure_iUnion_null hnone
  obtain ⟨a, ha⟩ := hsome
  obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero ha
  have hpat := (mem_defectAtom.mp hx.2).2
  have hi : i ∈ a := (hpat i).mp hx.1.1
  have hj : j ∉ a := fun hj => hx.1.2 ((hpat j).mpr hj)
  refine ⟨a, fun hzero => ha (measure_mono_null Set.inter_subset_right hzero), ?_⟩
  intro y hy
  have hyp := (mem_defectAtom.mp hy).2
  exact ⟨(hyp i).mpr hi, fun hyj => hj ((hyp j).mp hyj)⟩

noncomputable def activeClasses (μ : Measure Ω) (C : I → Set Ω) : Finset I :=
  univ.filter fun i => μ (C i) ≠ 0

noncomputable def positiveDefectAtoms (μ : Measure Ω) (P : Set Ω) (D : I → Set Ω) :
    Finset (Finset I) := univ.filter fun a => μ (defectAtom P D a) ≠ 0

noncomputable def uncrossingComplexity (μ : Measure Ω) (C : I → Set Ω)
    (P : Set Ω) (D : I → Set Ω) : ℕ :=
  (activeClasses μ C).card + (positiveDefectAtoms μ P D).card

theorem activeClasses_mono {μ ν : Measure Ω} (hν : ν ≪ μ) (C : I → Set Ω) :
    activeClasses ν C ⊆ activeClasses μ C := by
  intro i hi
  simp only [activeClasses, mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact fun hzero => hi (hν hzero)

theorem positiveDefectAtoms_mono {μ ν : Measure Ω} (hν : ν ≪ μ)
    (P : Set Ω) (D : I → Set Ω) : positiveDefectAtoms ν P D ⊆ positiveDefectAtoms μ P D := by
  intro a ha
  simp only [positiveDefectAtoms, mem_filter, Finset.mem_univ, true_and] at ha ⊢
  exact fun hzero => ha (hν hzero)

theorem uncrossingComplexity_mono {μ ν : Measure Ω} (hν : ν ≪ μ)
    (C : I → Set Ω) (P : Set Ω) (D : I → Set Ω) :
    uncrossingComplexity ν C P D ≤ uncrossingComplexity μ C P D :=
  Nat.add_le_add (card_le_card (activeClasses_mono hν C))
    (card_le_card (positiveDefectAtoms_mono hν P D))

theorem activeClasses_card_lt_of_kill {μ ν : Measure Ω} (hν : ν ≪ μ)
    {C : I → Set Ω} {i : I} (hi : μ (C i) ≠ 0) (hkill : ν (C i) = 0) :
    (activeClasses ν C).card < (activeClasses μ C).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨activeClasses_mono hν C, ?_⟩
  intro heq
  have hmem : i ∈ activeClasses μ C := by simp [activeClasses, hi]
  rw [← heq] at hmem
  simpa [activeClasses, hkill] using hmem

theorem positiveDefectAtoms_card_lt_of_kill_sdiff {μ ν : Measure Ω} (hν : ν ≪ μ)
    {P : Set Ω} {D : I → Set Ω} {i j : I}
    (hDi : D i ⊆ P) (hpos : μ (D i \ D j) ≠ 0) (hkill : ν (D i \ D j) = 0) :
    (positiveDefectAtoms ν P D).card < (positiveDefectAtoms μ P D).card := by
  obtain ⟨a, ha, hasub⟩ := exists_positive_defectAtom_in_sdiff hDi hpos
  have hnew : ν (defectAtom P D a) = 0 := measure_mono_null hasub hkill
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨positiveDefectAtoms_mono hν P D, ?_⟩
  intro heq
  have hmem : a ∈ positiveDefectAtoms μ P D := by simp [positiveDefectAtoms, ha]
  rw [← heq] at hmem
  simpa [positiveDefectAtoms, hnew] using hmem

/-- Either possible positive endpoint outcome gives a strict descent. -/
theorem uncrossingComplexity_lt_of_endpoint {μ ν : Measure Ω} (hν : ν ≪ μ)
    {C D : I → Set Ω} {P : Set Ω} (hD : ∀ i, D i ⊆ P) {i j : I}
    (hi : μ (C i) ≠ 0) (hcross : μ (D j \ D i) ≠ 0)
    (hkill : ν (C i) = 0 ∨ ν (D j \ D i) = 0) :
    uncrossingComplexity ν C P D < uncrossingComplexity μ C P D := by
  rcases hkill with h | h
  · exact Nat.add_lt_add_of_lt_of_le (activeClasses_card_lt_of_kill hν hi h)
      (card_le_card (positiveDefectAtoms_mono hν P D))
  · exact Nat.add_lt_add_of_le_of_lt (card_le_card (activeClasses_mono hν C))
      (positiveDefectAtoms_card_lt_of_kill_sdiff hν (hD j) hcross h)

/-- Comparability is required only for classes that still have positive
measure; the original finite family itself is never deleted or changed. -/
def ActiveDefectsComparable (μ : Measure Ω) (C D : I → Set Ω) : Prop :=
  ∀ i j, μ (C i) ≠ 0 → μ (C j) ≠ 0 → μ (D i \ D j) = 0 ∨ μ (D j \ D i) = 0

theorem ActiveDefectsComparable.ae_le {μ : Measure Ω} {C D : I → Set Ω}
    (h : ActiveDefectsComparable μ C D) {i j : I} (hi : μ (C i) ≠ 0) (hj : μ (C j) ≠ 0) :
    D i ≤ᵐ[μ] D j ∨ D j ≤ᵐ[μ] D i := (h i j hi hj).imp ae_le_set.mpr ae_le_set.mpr

theorem ActiveDefectsComparable.ae_le_of_measure_le {μ : Measure Ω} [IsFiniteMeasure μ]
    {C D : I → Set Ω} (h : ActiveDefectsComparable μ C D)
    (hD : ∀ i, MeasurableSet (D i)) {i j : I}
    (hi : μ (C i) ≠ 0) (hj : μ (C j) ≠ 0) (hm : μ (D i) ≤ μ (D j)) :
    D i ≤ᵐ[μ] D j := by
  rcases h.ae_le hi hj with h | h
  · exact h
  · exact (ae_eq_of_ae_subset_of_measure_ge h hm
      (hD j).nullMeasurableSet (measure_ne_top μ (D i))).symm.le

/-- The active family has an actual minimum defect modulo null sets. -/
theorem ActiveDefectsComparable.exists_minimal {μ : Measure Ω} [IsFiniteMeasure μ]
    {C D : I → Set Ω} (h : ActiveDefectsComparable μ C D)
    (hD : ∀ i, MeasurableSet (D i)) (hne : (activeClasses μ C).Nonempty) :
    ∃ i : I, μ (C i) ≠ 0 ∧ ∀ j : I, μ (C j) ≠ 0 → D i ≤ᵐ[μ] D j := by
  obtain ⟨i, hi, hmin⟩ := (activeClasses μ C).exists_min_image (fun i => μ (D i)) hne
  have hi' : μ (C i) ≠ 0 := (Finset.mem_filter.mp hi).2
  refine ⟨i, hi', ?_⟩
  intro j hj
  apply h.ae_le_of_measure_le hD hi' hj
  exact hmin j (by simp [activeClasses, hj])

/-- Finite termination from a local, invariant-preserving endpoint move.
The measure changes supplied by the local step are actual measures, and
their absolute continuity is composed throughout the induction. -/
theorem exists_uncrossed_measure {μ : Measure Ω} (C D : I → Set Ω) (P : Set Ω)
    (hD : ∀ i, D i ⊆ P) (Good : Measure Ω → Prop) (hgood : Good μ)
    (hstep : ∀ ν : Measure Ω, ν ≪ μ → Good ν → ∀ i j,
      ν (C i) ≠ 0 → ν (C j) ≠ 0 → ν (D i \ D j) ≠ 0 → ν (D j \ D i) ≠ 0 →
      ∃ ν' : Measure Ω, ν' ≪ ν ∧ Good ν' ∧ (ν' (C i) = 0 ∨ ν' (D j \ D i) = 0)) :
    ∃ ν : Measure Ω, ν ≪ μ ∧ Good ν ∧ ActiveDefectsComparable ν C D := by
  have haux : ∀ n : ℕ, ∀ ν : Measure Ω, uncrossingComplexity ν C P D = n →
      ν ≪ μ → Good ν →
      ∃ ν' : Measure Ω, ν' ≪ μ ∧ Good ν' ∧ ActiveDefectsComparable ν' C D := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro ν hn hν hG
      by_cases hcomp : ActiveDefectsComparable ν C D
      · exact ⟨ν, hν, hG, hcomp⟩
      simp only [ActiveDefectsComparable, not_forall, not_imp, not_or] at hcomp
      obtain ⟨i, j, hi, hj, hij, hji⟩ := hcomp
      obtain ⟨ν', hν', hG', hkill⟩ := hstep ν hν hG i j hi hj hij hji
      have hlt := uncrossingComplexity_lt_of_endpoint hν' hD hi hji hkill
      rw [hn] at hlt
      exact ih _ hlt ν' rfl (hν'.trans hν) hG'
  exact haux _ μ rfl AbsolutelyContinuous.rfl hgood

namespace ZeroTwinData

variable {W : Kernel Ω} {μ : Measure Ω} {c : Ω → ℝ}

/-- The fixed defect family of zero-cover twins lies in the positive-cover
set, exactly as required by the Boolean-atom descent. -/
theorem defect_subset_positive (P : ZeroTwinData W μ c I) (i : I) :
    P.defect i ⊆ {x | 0 < c x} := fun x hx => P.defect_pos i x hx

theorem exists_uncrossed_measure (P : ZeroTwinData W μ c I)
    (Good : Measure Ω → Prop) (hgood : Good μ)
    (hstep : ∀ ν : Measure Ω, ν ≪ μ → Good ν → ∀ i j,
      ν (P.block i) ≠ 0 → ν (P.block j) ≠ 0 →
      ν (P.defect i \ P.defect j) ≠ 0 → ν (P.defect j \ P.defect i) ≠ 0 →
      ∃ ν' : Measure Ω, ν' ≪ ν ∧ Good ν' ∧
        (ν' (P.block i) = 0 ∨ ν' (P.defect j \ P.defect i) = 0)) :
    ∃ ν : Measure Ω, ν ≪ μ ∧ Good ν ∧ ActiveDefectsComparable ν P.block P.defect :=
  Graphon.exists_uncrossed_measure P.block P.defect {x | 0 < c x}
    P.defect_subset_positive Good hgood hstep

end ZeroTwinData

end DensityHS.Graphon
