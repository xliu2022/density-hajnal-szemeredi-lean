module

public import DensityHS.Constructions.CompactFamilies

/-!
# Closed limits and uniform approximation of near-active families

Author and maintainer: Xizhi Liu.

The density defect is included as an additional coordinate of a compact
parameter image. A compact minimum argument then proves that near-active
models approach the joint graph of active models uniformly, allowing the
density parameter to vary through crossings and domain endpoints.
-/

@[expose] public section

namespace DensityHS.Constructions

open MeasureTheory Set

theorem exists_active_kind {r : ℕ} (hr : 3 ≤ r) (x : ℝ) :
    ∃ t : ConstructionKind r, constructionDomain r t x ∧
      Phi r x = constructionDensity r t x := by
  rcases Phi_mem_branchValues hr x with ⟨i, hi, hir, he⟩ | ⟨hd, he⟩ | ⟨hd, he⟩
  · let j : Fin (r - 1) := ⟨i - 1, by omega⟩
    refine ⟨.ordinary j, trivial, ?_⟩
    change Phi r x = B r (i - 1 + 1) x
    simpa only [Nat.sub_add_cancel hi] using he
  · exact ⟨.exceptional, hd, he⟩
  · exact ⟨.final, hd, he⟩

theorem activeFamily_nonempty {r : ℕ} (hr : 3 ≤ r) {x : ℝ}
    (hx : x ∈ Icc 0 (1 / (r : ℝ))) : (activeFamily r x).Nonempty := by
  obtain ⟨t, hd, he⟩ := exists_active_kind hr x
  let z : Fin (r - 1) → ℝ := fun _ => 1 / ((r - 1 : ℕ) : ℝ)
  have hs : (r - 1 : ℕ) ≠ 0 := by omega
  have hz : IsProbabilityWeight z := by
    refine ⟨fun _ => by dsimp [z]; positivity, ?_⟩
    simp [z, hs]
  refine ⟨constructionGraphon r t (x, z), (mem_activeFamily_iff hr).mpr ?_⟩
  exact ⟨t, z, hx, hz, hd, he, rfl⟩

theorem nearActiveGraph_mono (r : ℕ) {η θ : ℝ} (h : η ≤ θ) :
    nearActiveGraph r η ⊆ nearActiveGraph r θ := by
  rintro u hu
  obtain ⟨t, p, hp, rfl⟩ := Set.mem_iUnion.mp hu
  apply Set.mem_iUnion.mpr
  refine ⟨t, p, ⟨hp.1, hp.2.1, hp.2.2.1, ?_⟩, rfl⟩
  linarith [hp.2.2.2]

theorem activeFamily_subset_nearActive (r : ℕ) (x : ℝ) {η : ℝ} (hη : 0 ≤ η) :
    activeFamily r x ⊆ nearActiveFamily r x η :=
  fun _ h => nearActiveGraph_mono r hη h

def admissibleParameters (r : ℕ) (t : ConstructionKind r) :
    Set (ℝ × (Fin (r - 1) → ℝ)) :=
  {p | p.1 ∈ Icc 0 (1 / (r : ℝ)) ∧ IsProbabilityWeight p.2 ∧
    constructionDomain r t p.1}

theorem isCompact_admissibleParameters (r : ℕ) (t : ConstructionKind r) :
    IsCompact (admissibleParameters r t) := by
  have he : admissibleParameters r t =
      ((Icc (0 : ℝ) (1 / (r : ℝ))) ×ˢ {z | IsProbabilityWeight z}) ∩
        {p | constructionDomain r t p.1} := by
    ext p
    simp only [admissibleParameters, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_prod]
    tauto
  rw [he]
  exact (isCompact_Icc.prod (isCompact_probabilityWeights _)).inter_right
    ((isClosed_constructionDomain r t).preimage continuous_fst)

/-- The compact joint image with the actual branch defect as an extra coordinate. -/
def gappedConstructionGraph (r : ℕ) :
    Set (ℝ × (ℝ × Vendor.GraphonSpace ℝ unitMeasure)) :=
  ⋃ t : ConstructionKind r,
    (fun p => (continuousEnvelope r p.1 - constructionDensity r t p.1,
      (p.1, constructionGraphon r t p))) '' admissibleParameters r t

theorem isCompact_gappedConstructionGraph (r : ℕ) : IsCompact (gappedConstructionGraph r) := by
  apply isCompact_iUnion
  intro t
  apply (isCompact_admissibleParameters r t).image
  exact (((continuous_continuousEnvelope r).comp continuous_fst).sub
      ((continuous_constructionDensity r t).comp continuous_fst)).prodMk
    (continuous_fst.prodMk (continuous_constructionGraphon r t))

theorem gappedConstructionGraph_nonneg {r : ℕ} (hr : 3 ≤ r)
    {a : ℝ × (ℝ × Vendor.GraphonSpace ℝ unitMeasure)}
    (ha : a ∈ gappedConstructionGraph r) : 0 ≤ a.1 := by
  obtain ⟨t, p, hp, rfl⟩ := Set.mem_iUnion.mp ha
  change 0 ≤ continuousEnvelope r p.1 - constructionDensity r t p.1
  rw [← Phi_eq_continuousEnvelope hr hp.1]
  exact sub_nonneg.mpr (constructionDensity_le_Phi hr t hp.2.2)

theorem gappedConstructionGraph_nearActive {r : ℕ}
    {a : ℝ × (ℝ × Vendor.GraphonSpace ℝ unitMeasure)}
    (ha : a ∈ gappedConstructionGraph r) {η : ℝ} (hη : a.1 ≤ η) :
    a.2 ∈ nearActiveGraph r η := by
  obtain ⟨t, p, hp, rfl⟩ := Set.mem_iUnion.mp ha
  apply Set.mem_iUnion.mpr
  refine ⟨t, p, ⟨hp.1, hp.2.1, hp.2.2, ?_⟩, rfl⟩
  linarith

theorem exists_gapped_of_nearActive {r : ℕ} {η : ℝ}
    {u : ℝ × Vendor.GraphonSpace ℝ unitMeasure} (hu : u ∈ nearActiveGraph r η) :
    ∃ g : ℝ, (g, u) ∈ gappedConstructionGraph r ∧ g ≤ η := by
  obtain ⟨t, p, hp, rfl⟩ := Set.mem_iUnion.mp hu
  refine ⟨continuousEnvelope r p.1 - constructionDensity r t p.1, ?_, ?_⟩
  · exact Set.mem_iUnion.mpr ⟨t, p, ⟨hp.1, hp.2.1, hp.2.2.1⟩, rfl⟩
  · linarith [hp.2.2.2]

/-- Compact nonnegative defects approach their zero locus uniformly. -/
theorem compact_gap_approach_zero_set {Y : Type*} [MetricSpace Y]
    (S : Set (ℝ × Y)) (hS : IsCompact S) (hgap : ∀ a ∈ S, 0 ≤ a.1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ a ∈ S, a.1 ≤ η →
      ∃ b ∈ S, b.1 = 0 ∧ dist a.2 b.2 < ε := by
  classical
  let O : Set (ℝ × Y) := ⋃ b ∈ {b ∈ S | b.1 = 0}, {a | dist a.2 b.2 < ε}
  have hO : IsOpen O := by
    apply isOpen_iUnion
    intro b
    apply isOpen_iUnion
    intro _
    exact isOpen_lt (continuous_snd.dist continuous_const) continuous_const
  have hmemO (a : ℝ × Y) :
      a ∈ O ↔ ∃ b ∈ S, b.1 = 0 ∧ dist a.2 b.2 < ε := by
    simp only [O, Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨b, ⟨hb, hb0⟩, hd⟩
      exact ⟨b, hb, hb0, hd⟩
    · rintro ⟨b, hb, hb0, hd⟩
      exact ⟨b, ⟨hb, hb0⟩, hd⟩
  have hbad : IsCompact (S ∩ Oᶜ) := hS.inter_right hO.isClosed_compl
  by_cases hn : (S ∩ Oᶜ).Nonempty
  · obtain ⟨b, hb, hmin⟩ := hbad.exists_isMinOn hn continuous_fst.continuousOn
    have hbpos : 0 < b.1 := by
      have hbn := hgap b hb.1
      by_contra h
      have hb0 : b.1 = 0 := le_antisymm (le_of_not_gt h) hbn
      exact hb.2 ((hmemO b).mpr ⟨b, hb.1, hb0, by simpa using hε⟩)
    refine ⟨b.1 / 2, by positivity, ?_⟩
    intro a ha hsmall
    apply (hmemO a).mp
    by_contra hnot
    have hle := hmin ⟨ha, hnot⟩
    change b.1 ≤ a.1 at hle
    linarith
  · refine ⟨1, by norm_num, ?_⟩
    intro a ha _
    apply (hmemO a).mp
    by_contra hnot
    exact hn ⟨a, ha, hnot⟩

/-- Uniform approximation to the joint active-family graph. The parameter
may vary, which is necessary at crossings and domain endpoints. -/
theorem nearActiveGraph_approaches_active {r : ℕ} (hr : 3 ≤ r)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ u ∈ nearActiveGraph r η,
      ∃ v ∈ nearActiveGraph r 0, dist u v < ε := by
  obtain ⟨η, hη, h⟩ := compact_gap_approach_zero_set (gappedConstructionGraph r)
    (isCompact_gappedConstructionGraph r) (fun _ ha => gappedConstructionGraph_nonneg hr ha) hε
  refine ⟨η, hη, ?_⟩
  intro u hu
  obtain ⟨g, hg, hsmall⟩ := exists_gapped_of_nearActive hu
  obtain ⟨b, hb, hb0, hd⟩ := h (g, u) hg hsmall
  exact ⟨b.2, gappedConstructionGraph_nearActive hb hb0.le, hd⟩

end DensityHS.Constructions

