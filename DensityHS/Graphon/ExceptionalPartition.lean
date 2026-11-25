module

public import DensityHS.Graphon.ZeroRegions
public import DensityHS.Graphon.RankTwo

/-!
# Measurable exceptional constructions and their recursive assembly

Author and maintainer: Xizhi Liu.

An exceptional construction consists of `r-2` universal independent classes
of mass `1/(r-1)`. The remaining region is a clique of mass `2x` together with
isolated vertices. These are actual measurable partitions and almost-
everywhere kernel identities.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped ENNReal

universe u

structure ExceptionalPartition {Ω : Type u} [MeasurableSpace Ω]
    (r : ℕ) (x : ℝ) (W : Kernel Ω) (μ : Measure Ω) where
  Index : Type u
  fintype : Fintype Index
  cardinality : @Fintype.card Index fintype = r - 2
  block : Index → Set Ω
  measurable : ∀ i, MeasurableSet (block i)
  disjoint : Pairwise fun i j => Disjoint (block i) (block j)
  mass : ∀ i, μ.real (block i) = 1 / ((r : ℝ) - 1)
  independent : ∀ i, ∀ᵐ z : Ω × Ω ∂μ.prod μ,
    z.1 ∈ block i → z.2 ∈ block i → W z.1 z.2 = 0
  complete_cross : ∀ i, ∀ᵐ z : Ω × Ω ∂μ.prod μ,
    z.1 ∈ block i → z.2 ∉ block i → W z.1 z.2 = 1
  clique : Set Ω
  clique_measurable : MeasurableSet clique
  clique_disjoint : ∀ i, Disjoint clique (block i)
  clique_mass : μ.real clique = 2 * x
  remainder : ∀ᵐ z : Ω × Ω ∂μ.prod μ,
    (∀ i, z.1 ∉ block i) → (∀ i, z.2 ∉ block i) →
      W z.1 z.2 = (clique ×ˢ clique).indicator (fun _ => (1 : ℝ)) z

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Conditional masses rescale to the intersection with the conditioning
region. This is used to assemble actual disjoint sets in the original space. -/
theorem measureReal_cond_mul (μ : Measure Ω) [IsFiniteMeasure μ]
    {S T : Set Ω} (hT : MeasurableSet T) (hS0 : μ S ≠ 0) :
    μ.real S * (cond μ S).real T = μ.real (S ∩ T) := by
  have hR0 : μ.real S ≠ 0 := (ENNReal.toReal_pos hS0 (measure_ne_top μ S)).ne'
  unfold Measure.real
  rw [ProbabilityTheory.cond, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply hT, ENNReal.toReal_mul, ENNReal.toReal_inv,
    inter_comm T S]
  change μ.real S * ((μ.real S)⁻¹ * μ.real (S ∩ T)) = _
  rw [← mul_assoc, mul_inv_cancel₀ hR0, one_mul]
  rfl

/-- The matching equality is the base exceptional partition with no peeled
independent classes. -/
theorem exceptionalPartition_two (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {x : ℝ} (hx : 2 / 5 < x) (hx1 : x ≤ 1 / 2)
    (hcover : coverNumber 2 W μ ≤ x) (he : density μ W = 2 * x ^ 2) :
    Nonempty (ExceptionalPartition 2 x W μ) := by
  classical
  obtain ⟨C, hC, hmass, hkernel⟩ := rank_two_equality_coverNumber W μ hx hx1 hcover he
  refine ⟨{
    Index := ULift.{u} (Fin 0)
    fintype := inferInstance
    cardinality := by simp
    block := fun _ => ∅
    measurable := fun _ => MeasurableSet.empty
    disjoint := by intro i; exact Fin.elim0 i.down
    mass := by intro i; exact Fin.elim0 i.down
    independent := by intro i; exact Fin.elim0 i.down
    complete_cross := by intro i; exact Fin.elim0 i.down
    clique := C
    clique_measurable := hC
    clique_disjoint := by intro i; exact Fin.elim0 i.down
    clique_mass := hmass
    remainder := ?_ }⟩
  filter_upwards [hkernel] with z hz _ _
  exact hz

/-- Adding one universal independent class to a normalized exceptional
construction gives the exceptional construction of the next clique order. -/
theorem ExceptionalPartition.add_class {t : ℕ} (ht : 2 ≤ t)
    {W : Kernel Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {x : ℝ}
    {S : Set Ω} (hS : MeasurableSet S) (hSmass : μ.real S = 1 / (t : ℝ))
    (hind : ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ S → z.2 ∈ S → W z.1 z.2 = 0)
    (hcross : ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ S → z.2 ∉ S → W z.1 z.2 = 1)
    (P : ExceptionalPartition t (x / (((t : ℝ) - 1) / t)) W (cond μ Sᶜ)) :
    Nonempty (ExceptionalPartition (t + 1) x W μ) := by
  classical
  letI := P.fintype
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0 : ℝ) < t := by linarith
  have ht1 : 0 < (t : ℝ) - 1 := by linarith
  let q := ((t : ℝ) - 1) / t
  have hq : 0 < q := div_pos ht1 ht0
  have hScmass : μ.real Sᶜ = q := by
    rw [measureReal_compl hS, probReal_univ, hSmass]
    dsimp [q]
    field_simp
    <;> ring
  have hSc0 : μ Sᶜ ≠ 0 := by
    intro hz
    have : μ.real Sᶜ = 0 := by simp [measureReal_def, hz]
    linarith
  letI : IsProbabilityMeasure (cond μ Sᶜ) := cond_isProbabilityMeasure hSc0
  let b : Option P.Index → Set Ω := fun i => match i with
    | none => S
    | some j => Sᶜ ∩ P.block j
  have hbm : ∀ i, MeasurableSet (b i) := by
    rintro (_ | i)
    · exact hS
    · exact hS.compl.inter (P.measurable i)
  have hbd : Pairwise fun i j => Disjoint (b i) (b j) := by
    rintro (_ | i) (_ | j) hij
    · exact False.elim (hij rfl)
    · exact disjoint_compl_right.mono_right inter_subset_left
    · exact disjoint_compl_left.mono_left inter_subset_left
    · exact (P.disjoint (fun h => hij (congrArg some h))).mono inter_subset_right inter_subset_right
  have hbmasses : ∀ i, μ.real (b i) = 1 / ((t + 1 : ℕ) - 1 : ℝ) := by
    rintro (_ | i)
    · simpa using hSmass
    · have he := measureReal_cond_mul μ (P.measurable i) hSc0
      rw [hScmass, P.mass] at he
      change μ.real (Sᶜ ∩ P.block i) = _
      rw [← he]
      dsimp [q]
      push_cast
      simp only [add_sub_cancel_right]
      field_simp [ht0.ne', ht1.ne']
  have hbi : ∀ i, ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      z.1 ∈ b i → z.2 ∈ b i → W z.1 z.2 = 0 := by
    rintro (_ | i)
    · exact hind
    · filter_upwards [ae_of_ae_cond_prod μ hS.compl hSc0 (P.independent i)] with z hz hx hy
      exact hz hx.1 hy.1 hx.2 hy.2
  have hbc : ∀ i, ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      z.1 ∈ b i → z.2 ∉ b i → W z.1 z.2 = 1 := by
    rintro (_ | i)
    · exact hcross
    · have hswap := (measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hcross
      filter_upwards [ae_of_ae_cond_prod μ hS.compl hSc0 (P.complete_cross i), hswap]
        with z hz hzswap hx hy
      by_cases hys : z.2 ∈ S
      · exact (W.symmetric z.1 z.2).trans (hzswap hys hx.1)
      · exact hz hx.1 hys hx.2 (fun hyP => hy ⟨hys, hyP⟩)
  let C := Sᶜ ∩ P.clique
  have hC : MeasurableSet C := hS.compl.inter P.clique_measurable
  have hCd : ∀ i, Disjoint C (b i) := by
    rintro (_ | i)
    · exact disjoint_compl_left.mono_left inter_subset_left
    · exact (P.clique_disjoint i).mono inter_subset_right inter_subset_right
  have hCmass : μ.real C = 2 * x := by
    have he := measureReal_cond_mul μ P.clique_measurable hSc0
    rw [hScmass, P.clique_mass] at he
    change μ.real (Sᶜ ∩ P.clique) = _
    rw [← he]
    change q * (2 * (x / q)) = _
    field_simp
  refine ⟨{
    Index := Option P.Index
    fintype := inferInstance
    cardinality := by simp only [Fintype.card_option, P.cardinality]; omega
    block := b
    measurable := hbm
    disjoint := hbd
    mass := by simpa using hbmasses
    independent := hbi
    complete_cross := hbc
    clique := C
    clique_measurable := hC
    clique_disjoint := hCd
    clique_mass := hCmass
    remainder := ?_ }⟩
  filter_upwards [ae_of_ae_cond_prod μ hS.compl hSc0 P.remainder] with z hz hx hy
  have hxSc : z.1 ∈ Sᶜ := hx none
  have hySc : z.2 ∈ Sᶜ := hy none
  have hxP : ∀ i, z.1 ∉ P.block i := fun i hi => hx (some i) ⟨hxSc, hi⟩
  have hyP : ∀ i, z.2 ∉ P.block i := fun i hi => hy (some i) ⟨hySc, hi⟩
  rw [hz hxSc hySc hxP hyP]
  by_cases hxC : z.1 ∈ P.clique <;> by_cases hyC : z.2 ∈ P.clique <;>
    simp [C, hxSc, hySc, hxC, hyC]

end DensityHS.Graphon
