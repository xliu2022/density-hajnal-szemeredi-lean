module

public import DensityHS.Constructions.Alignment

/-!
# Labels from disjoint measurable blocks

Author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS.Constructions

open MeasureTheory Set Filter

variable {Ω I : Type*} [MeasurableSpace Ω]

/-- Independent blocks receive a some label, and their complement receives
the none label. -/
noncomputable def finiteBlockLabel (C : I → Set Ω) (x : Ω) : Option I := by
  classical
  exact if h : ∃ i, x ∈ C i then some (Classical.choose h) else none

theorem finiteBlockLabel_some_iff (C : I → Set Ω)
    (hd : Pairwise fun i j => Disjoint (C i) (C j)) (i : I) (x : Ω) :
    finiteBlockLabel C x = some i ↔ x ∈ C i := by
  classical
  by_cases h : ∃ j, x ∈ C j
  · have hx : x ∈ C (Classical.choose h) := Classical.choose_spec h
    rw [finiteBlockLabel, dif_pos h, Option.some.injEq]
    constructor
    · rintro rfl
      exact hx
    · intro hxi
      by_contra hne
      exact Set.disjoint_left.mp (hd hne) hx hxi
  · have hn : x ∉ C i := fun hx => h ⟨i, hx⟩
    simp [finiteBlockLabel, h, hn]

theorem finiteBlockLabel_none_iff (C : I → Set Ω) (x : Ω) :
    finiteBlockLabel C x = none ↔ ∀ i, x ∉ C i := by
  classical
  by_cases h : ∃ i, x ∈ C i
  · have hn : ¬∀ i, x ∉ C i := by
      intro hh
      obtain ⟨i, hi⟩ := h
      exact hh i hi
    simp [finiteBlockLabel, h, hn]
  · have hn : ∀ i, x ∉ C i := not_exists.mp h
    simp [finiteBlockLabel, h, hn]

theorem finiteBlockLabel_fiber_some (C : I → Set Ω)
    (hd : Pairwise fun i j => Disjoint (C i) (C j)) (i : I) :
    {x | finiteBlockLabel C x = some i} = C i := by
  ext x
  exact finiteBlockLabel_some_iff C hd i x

theorem finiteBlockLabel_fiber_none (C : I → Set Ω) :
    {x | finiteBlockLabel C x = none} = (⋃ i, C i)ᶜ := by
  ext x
  simp only [Set.mem_setOf_eq, finiteBlockLabel_none_iff, Set.mem_compl_iff,
    Set.mem_iUnion, not_exists]

theorem measurable_finiteBlockLabel [Fintype I] [MeasurableSpace (Option I)]
    [MeasurableSingletonClass (Option I)] (C : I → Set Ω)
    (hC : ∀ i, MeasurableSet (C i))
    (hd : Pairwise fun i j => Disjoint (C i) (C j)) :
    Measurable (finiteBlockLabel C) := by
  apply measurable_to_countable'
  intro i
  change MeasurableSet {x | finiteBlockLabel C x = i}
  cases i with
  | none =>
    rw [finiteBlockLabel_fiber_none]
    exact (MeasurableSet.iUnion hC).compl
  | some i =>
    rw [finiteBlockLabel_fiber_some C hd i]
    exact hC i

theorem finiteBlockLabel_mass_none [Fintype I] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (C : I → Set Ω) (hC : ∀ i, MeasurableSet (C i))
    (hd : Pairwise fun i j => Disjoint (C i) (C j)) :
    μ.real {x | finiteBlockLabel C x = none} = 1 - ∑ i, μ.real (C i) := by
  rw [finiteBlockLabel_fiber_none, measureReal_compl (MeasurableSet.iUnion hC),
    probReal_univ, measureReal_iUnion_fintype hd hC]

end DensityHS.Constructions

