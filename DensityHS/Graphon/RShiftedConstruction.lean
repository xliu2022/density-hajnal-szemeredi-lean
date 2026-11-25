module

public import DensityHS.Graphon.RShiftRows
public import DensityHS.Graphon.RShiftedData
public import DensityHS.Graphon.ZeroTwinRows
public import DensityHS.Graphon.ConditionalClusters

/-!
# Constructing the shifted system from actual tangent variation

Author and maintainer: Xizhi Liu.

The strict degree deficit eliminates the unmarked clique remainder. The
null tangent operator makes every remaining independent block a global
twin class; their shifted neighbor masses force a finite index set.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter TopologicalSpace
open scoped ENNReal InnerProductSpace Classical

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

/-- Actual constant-cover tangent geometry with a positive degree deficit
produces a finite shifted block system. -/
theorem exists_shiftedBlockSystem (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] [SeparableSpace (Lp ℝ 2 μ)]
    {r : ℕ} {Z : Set Ω} (hZ : MeasurableSet Z) (hP0 : μ Zᶜ ≠ 0)
    (hc : IsKernelCover r W μ (markedCover r Z))
    {x L θ t : ℝ} (hxa : x ≠ 1 / (r : ℝ)) (ht : 0 < t)
    (hcx : (∫ z, markedCover r Z z ∂μ) = x)
    (hd : ∀ᵐ z ∂μ, kernelDegree W μ z = 1 - L + θ * markedCover r Z z)
    (hdP : ∀ᵐ z ∂μ, z ∉ Z → kernelDegree W.complement μ z = μ.real Z + t)
    (hq : ∀ h : Lp ℝ 2 μ, h ∈ DensityHS.Analysis.boundedL2 μ →
      (∫ z, h z ∂μ) = 0 → (∫ z, markedCover r Z z * h z ∂μ) = 0 →
        ⟪h, kernelOperator W μ h⟫_ℝ ≤ 0)
    (hbin : ∀ᵐ z : Ω × Ω ∂μ.prod μ, W z.1 z.2 = 0 ∨ W z.1 z.2 = 1)
    (P : ClusterPartition W.complement (cond μ Zᶜ)) :
    Nonempty (ShiftedBlockSystem W μ Z t) := by
  let Q := P.onOriginalMeasure hZ.compl hP0
  have hlocal (i : Q.Index) : ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      z.1 ∈ Q.block i → z.2 ∉ Z →
        W.complement z.1 z.2 = (Q.block i).indicator (fun _ => (1 : ℝ)) z.2 := by
    filter_upwards [Q.row_on_block i] with z hz hx hy
    have h := hz hx
    rw [Kernel.mask_apply _ hZ.compl hx.1 hy] at h
    exact h
  have hdeg (i : Q.Index) : ∀ᵐ z ∂μ, z ∈ Q.block i →
      kernelDegree W.complement μ z = μ.real Z + t := by
    filter_upwards [hdP] with z hz hx
    exact hz hx.1
  have hC0 (i : Q.Index) : μ (Q.block i) ≠ 0 := (Q.positive i).ne'
  have hind (i : Q.Index) : ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      z.1 ∈ Q.block i → z.2 ∈ Q.block i → W z.1 z.2 = 0 := by
    filter_upwards [hlocal i] with z hz hx hy
    have he := hz hx hy.1
    rw [Set.indicator_of_mem hy] at he
    change 1 - W z.1 z.2 = 1 at he
    linarith
  have hconstant (i : Q.Index) : ∀ᵐ z ∂μ, z ∈ Q.block i → markedCover r Z z = 1 / (r : ℝ) :=
    Eventually.of_forall fun z hz => Set.indicator_of_mem hz.1 _
  have htwins (i : Q.Index) : ∃ T : Set Ω, MeasurableSet T ∧
      ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ Q.block i →
        W.complement z.1 z.2 = T.indicator (fun _ => (1 : ℝ)) z.2 := by
    apply exists_binary_common_row W.complement μ (Q.block i) (Q.measurable i) (Q.mass_pos i)
      (complement_binary W μ hbin)
    intro f _ hfs hm
    rw [kernelOperator_complement, hm,
      tangent_constant_block_annihilation W μ hc hxa hcx hd hq (hC0 i) (hconstant i) (hind i) f hfs hm]
    simp [constantL2]
  have hsets (i : Q.Index) : ∃ S : Set Ω, MeasurableSet S ∧ S ⊆ Z ∧
      μ.real S = μ.real (Q.block i) - t ∧
      ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ Q.block i → z.2 ∈ Z →
        W z.1 z.2 = S.indicator (fun _ => (1 : ℝ)) z.2 := by
    obtain ⟨T, hT, hrow⟩ := htwins i
    exact shifted_neighbor_set_of_common_row W μ hZ (Q.measurable i) hT (hC0 i)
      (P.onOriginalMeasure_block_subset hZ.compl hP0 i) rfl (hdeg i) hrow (hlocal i)
  choose S hS hSZ hSm hSr using hsets
  have hlower : ∀ i : Q.Index, t ≤ Q.mass i := by
    intro i
    have hn := measureReal_nonneg (μ := μ) (s := S i)
    rw [hSm i] at hn
    change t ≤ μ.real (Q.block i)
    linarith
  have hlarge := Q.finite_large_mass (show 0 < t / 2 by positivity)
  have huniv : (Set.univ : Set Q.Index).Finite := hlarge.subset (by
    intro i _
    exact (show t / 2 < t by linarith).trans_le (hlower i))
  letI : Finite Q.Index := Set.finite_univ_iff.mp huniv
  letI : Fintype Q.Index := Fintype.ofFinite Q.Index
  have hcovers : ∀ᵐ z ∂μ, z ∉ Z → ∃ i, z ∈ Q.block i := by
    filter_upwards [ae_ae_of_ae_prod Q.zero_rows, hdP] with z hz hdz hzP
    by_contra hn
    have hnone : z ∉ ⋃ i, Q.block i := by simpa only [mem_iUnion] using hn
    have hrow : ∀ᵐ y ∂μ, y ∉ Z → W z y = 1 := by
      filter_upwards [hz] with y hy hyP
      have he := hy hnone
      rw [Kernel.mask_apply _ hZ.compl hzP hyP] at he
      change 1 - W z y = 0 at he
      linarith
    have hi : (∫ y in Zᶜ, W z y ∂μ) = μ.real Zᶜ := by
      calc
        _ = ∫ _ : Ω in Zᶜ, (1 : ℝ) ∂μ := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem hZ.compl, ae_restrict_of_ae hrow] with y hy hyr
          exact hyr hy
        _ = _ := by simp
    have hle := setIntegral_le_integral (s := Zᶜ) (W.integrable_left μ z)
      (Eventually.of_forall fun y => W.nonneg z y)
    rw [hi] at hle
    change μ.real Zᶜ ≤ kernelDegree W μ z at hle
    have hdval := hdz hzP
    rw [kernelDegree_complement] at hdval
    rw [measureReal_compl hZ, probReal_univ] at hle
    linarith
  have hcross (i j : Q.Index) (hij : i ≠ j) : ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      z.1 ∈ Q.block i → z.2 ∈ Q.block j → 0 < W z.1 z.2 := by
    filter_upwards [hlocal i] with z hz hx hy
    have he := hz hx hy.1
    rw [Set.indicator_of_notMem (fun h => Set.disjoint_left.mp (Q.disjoint hij) h hy)] at he
    change 1 - W z.1 z.2 = 0 at he
    linarith
  exact ⟨{
    Index := Q.Index
    fintype := inferInstance
    block := Q.block
    measurable := Q.measurable
    positive := Q.mass_pos
    disjoint := Q.disjoint
    unmarked := fun _ => inter_subset_left
    covers := hcovers
    neighbor := S
    neighbor_measurable := hS
    neighbor_subset := hSZ
    neighbor_mass := hSm
    cross := hcross
    marked_row := hSr }⟩

end DensityHS.Graphon
