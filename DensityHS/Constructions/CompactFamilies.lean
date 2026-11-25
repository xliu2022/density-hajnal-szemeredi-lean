module

public import DensityHS.Constructions.OrdinaryKernel
public import DensityHS.Constructions.ExceptionalKernel
public import DensityHS.Constructions.FinalKernel

/-!
# Compact active and near-active graphon families

Author and maintainer: Xizhi Liu.

All three construction families are represented by actual interval graphons.
The ordinary and exceptional maps ignore the simplex coordinate; the final
family uses every simplex vector, including its boundary. The joint graph
of admissible near-active constructions is compact in parameter and cut
distance, so it retains all limiting degenerations and branch ties.
-/

@[expose] public section

namespace DensityHS.Constructions

open MeasureTheory Set

inductive ConstructionKind (r : ℕ)
  | ordinary (i : Fin (r - 1))
  | exceptional
  | final
  deriving DecidableEq, Fintype

noncomputable def constructionDensity (r : ℕ) : ConstructionKind r → ℝ → ℝ
  | .ordinary i => B r (i.val + 1)
  | .exceptional => A r
  | .final => R r

def constructionDomain (r : ℕ) : ConstructionKind r → ℝ → Prop
  | .ordinary _ => fun _ => True
  | .exceptional => ADomain r
  | .final => RDomain r

noncomputable def constructionKernel (r : ℕ) (t : ConstructionKind r)
    (p : ℝ × (Fin (r - 1) → ℝ)) : Graphon.Kernel ℝ :=
  match t with
  | .ordinary i => ordinaryKernel r (i.val + 1) p.1
  | .exceptional => exceptionalKernel r p.1
  | .final => finalKernel r p.1 p.2

noncomputable def constructionGraphon (r : ℕ) (t : ConstructionKind r)
    (p : ℝ × (Fin (r - 1) → ℝ)) : Vendor.GraphonSpace ℝ unitMeasure :=
  match t with
  | .ordinary i => ordinaryGraphon r (i.val + 1) p.1
  | .exceptional => exceptionalGraphon r p.1
  | .final => finalGraphon r p.1 p.2

theorem continuous_constructionDensity (r : ℕ) (t : ConstructionKind r) :
    Continuous (constructionDensity r t) := by
  cases t with
  | ordinary i => exact continuous_B _ _
  | exceptional => exact continuous_A _
  | final => exact continuous_R _

theorem isClosed_constructionDomain (r : ℕ) (t : ConstructionKind r) :
    IsClosed {x | constructionDomain r t x} := by
  cases t with
  | ordinary i => exact isClosed_univ
  | exceptional => exact isClosed_Icc
  | final => exact isClosed_Icc

theorem continuous_constructionGraphon (r : ℕ) (t : ConstructionKind r) :
    Continuous (constructionGraphon r t) := by
  cases t with
  | ordinary i => exact (continuous_ordinaryGraphon _ _).comp continuous_fst
  | exceptional => exact (continuous_exceptionalGraphon _).comp continuous_fst
  | final => exact continuous_finalGraphon _

theorem density_constructionKernel {r : ℕ} (hr : 3 ≤ r) (t : ConstructionKind r)
    {p : ℝ × (Fin (r - 1) → ℝ)} (hx : p.1 ∈ Icc 0 (1 / (r : ℝ)))
    (hz : IsProbabilityWeight p.2) (hd : constructionDomain r t p.1) :
    Graphon.density unitMeasure (constructionKernel r t p) = constructionDensity r t p.1 := by
  cases t with
  | ordinary i =>
    exact density_ordinaryKernel (by have := i.isLt; omega) hx
  | exceptional => exact density_exceptionalKernel (by omega) hd
  | final => exact density_finalKernel (by omega) hd hz

theorem constructionDensity_le_Phi {r : ℕ} (hr : 3 ≤ r) (t : ConstructionKind r)
    {x : ℝ} (hd : constructionDomain r t x) : constructionDensity r t x ≤ Phi r x := by
  cases t with
  | ordinary i => exact B_le_Phi hr (by omega) (by have := i.isLt; omega) x
  | exceptional => exact A_le_Phi hr hd
  | final => exact R_le_Phi hr hd

theorem isClosed_probabilityWeights (I : Type*) [Fintype I] :
    IsClosed {z : I → ℝ | IsProbabilityWeight z} := by
  have hnonneg : IsClosed {z : I → ℝ | ∀ i, 0 ≤ z i} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  have hsum : Continuous (fun z : I → ℝ => ∑ i, z i) := by fun_prop
  exact hnonneg.inter (isClosed_eq hsum continuous_const)

theorem isCompact_probabilityWeights (I : Type*) [Fintype I] :
    IsCompact {z : I → ℝ | IsProbabilityWeight z} := by
  apply (isCompact_Icc : IsCompact (Icc (fun _ : I => (0 : ℝ)) (fun _ => 1))).of_isClosed_subset
    (isClosed_probabilityWeights I)
  intro z hz
  exact ⟨hz.1, probabilityWeight_le_one hz⟩

/-- Compact parameters for all branches at a fixed density tolerance.
The continuous envelope agrees exactly with Phi on the included interval. -/
def nearActiveParameters (r : ℕ) (t : ConstructionKind r) (η : ℝ) :
    Set (ℝ × (Fin (r - 1) → ℝ)) :=
  {p | p.1 ∈ Icc 0 (1 / (r : ℝ)) ∧ IsProbabilityWeight p.2 ∧
    constructionDomain r t p.1 ∧
    continuousEnvelope r p.1 - η ≤ constructionDensity r t p.1}

theorem isCompact_nearActiveParameters (r : ℕ) (t : ConstructionKind r) (η : ℝ) :
    IsCompact (nearActiveParameters r t η) := by
  have hcompact : IsCompact ((Icc (0 : ℝ) (1 / (r : ℝ))) ×ˢ
      {z : Fin (r - 1) → ℝ | IsProbabilityWeight z}) :=
    isCompact_Icc.prod (isCompact_probabilityWeights _)
  have hclosed : IsClosed {p : ℝ × (Fin (r - 1) → ℝ) |
      constructionDomain r t p.1 ∧
        continuousEnvelope r p.1 - η ≤ constructionDensity r t p.1} :=
    ((isClosed_constructionDomain r t).preimage continuous_fst).inter
      (isClosed_le (((continuous_continuousEnvelope r).comp continuous_fst).sub continuous_const)
        ((continuous_constructionDensity r t).comp continuous_fst))
  have he : nearActiveParameters r t η =
      ((Icc (0 : ℝ) (1 / (r : ℝ))) ×ˢ {z | IsProbabilityWeight z}) ∩
        {p | constructionDomain r t p.1 ∧
          continuousEnvelope r p.1 - η ≤ constructionDensity r t p.1} := by
    ext p
    simp only [nearActiveParameters, Set.mem_setOf_eq, Set.mem_inter_iff,
      Set.mem_prod]
    tauto
  rw [he]
  exact hcompact.inter_right hclosed

/-- The joint graph of all near-active interval constructions. -/
def nearActiveGraph (r : ℕ) (η : ℝ) : Set (ℝ × Vendor.GraphonSpace ℝ unitMeasure) :=
  ⋃ t : ConstructionKind r,
    (fun p => (p.1, constructionGraphon r t p)) '' nearActiveParameters r t η

theorem isCompact_nearActiveGraph (r : ℕ) (η : ℝ) : IsCompact (nearActiveGraph r η) := by
  apply isCompact_iUnion
  intro t
  exact (isCompact_nearActiveParameters r t η).image
    (continuous_fst.prodMk (continuous_constructionGraphon r t))

theorem mem_nearActiveGraph_iff {r : ℕ} (hr : 3 ≤ r) {η x : ℝ}
    {U : Vendor.GraphonSpace ℝ unitMeasure} :
    (x, U) ∈ nearActiveGraph r η ↔
      ∃ t : ConstructionKind r, ∃ z : Fin (r - 1) → ℝ,
        x ∈ Icc 0 (1 / (r : ℝ)) ∧ IsProbabilityWeight z ∧
        constructionDomain r t x ∧ Phi r x - η ≤ constructionDensity r t x ∧
        U = constructionGraphon r t (x, z) := by
  constructor
  · intro h
    obtain ⟨t, p, hp, he⟩ := Set.mem_iUnion.mp h
    have hpx : p.1 = x := congrArg Prod.fst he
    have hpu : constructionGraphon r t p = U := congrArg Prod.snd he
    refine ⟨t, p.2, ?_, hp.2.1, ?_, ?_, ?_⟩
    · simpa only [hpx] using hp.1
    · simpa only [hpx] using hp.2.2.1
    · rw [Phi_eq_continuousEnvelope hr (by simpa only [hpx] using hp.1)]
      simpa only [hpx] using hp.2.2.2
    · simpa only [← hpx, Prod.mk.eta] using hpu.symm
  · rintro ⟨t, z, hx, hz, hd, hnear, rfl⟩
    apply Set.mem_iUnion.mpr
    refine ⟨t, (x, z), ⟨hx, hz, hd, ?_⟩, rfl⟩
    simpa only [← Phi_eq_continuousEnvelope hr hx] using hnear

def nearActiveFamily (r : ℕ) (x η : ℝ) : Set (Vendor.GraphonSpace ℝ unitMeasure) :=
  {U | (x, U) ∈ nearActiveGraph r η}

def activeFamily (r : ℕ) (x : ℝ) : Set (Vendor.GraphonSpace ℝ unitMeasure) :=
  nearActiveFamily r x 0

theorem isCompact_nearActiveFamily (r : ℕ) (x η : ℝ) :
    IsCompact (nearActiveFamily r x η) := by
  have hcompact := (isCompact_nearActiveGraph r η).inter_right
    (isClosed_eq continuous_fst (continuous_const : Continuous (fun _ :
      ℝ × Vendor.GraphonSpace ℝ unitMeasure => x)))
  have he : nearActiveFamily r x η =
      Prod.snd '' (nearActiveGraph r η ∩ {p | p.1 = x}) := by
    ext U
    constructor
    · intro h
      exact ⟨(x, U), ⟨h, rfl⟩, rfl⟩
    · rintro ⟨⟨y, V⟩, ⟨hp, hpx⟩, rfl⟩
      change y = x at hpx
      change (x, V) ∈ nearActiveGraph r η
      simpa only [hpx] using hp
  rw [he]
  exact hcompact.image continuous_snd

theorem isCompact_activeFamily (r : ℕ) (x : ℝ) : IsCompact (activeFamily r x) :=
  isCompact_nearActiveFamily r x 0

theorem mem_activeFamily_iff {r : ℕ} (hr : 3 ≤ r) {x : ℝ}
    {U : Vendor.GraphonSpace ℝ unitMeasure} :
    U ∈ activeFamily r x ↔
      ∃ t : ConstructionKind r, ∃ z : Fin (r - 1) → ℝ,
        x ∈ Icc 0 (1 / (r : ℝ)) ∧ IsProbabilityWeight z ∧
        constructionDomain r t x ∧ Phi r x = constructionDensity r t x ∧
        U = constructionGraphon r t (x, z) := by
  rw [activeFamily, nearActiveFamily, Set.mem_setOf_eq, mem_nearActiveGraph_iff hr]
  constructor
  · rintro ⟨t, z, hx, hz, hd, hnear, hU⟩
    exact ⟨t, z, hx, hz, hd,
      le_antisymm (by simpa using hnear) (constructionDensity_le_Phi hr t hd), hU⟩
  · rintro ⟨t, z, hx, hz, hd, he, hU⟩
    exact ⟨t, z, hx, hz, hd, by simp [he], hU⟩

end DensityHS.Constructions

