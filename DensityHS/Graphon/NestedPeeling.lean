module

public import DensityHS.Graphon.BlockOperator
public import DensityHS.Graphon.Uncrossing

/-!
# Peeling the smallest defect

Author and maintainer: Xizhi Liu.

All masses, defects and lower-order covers are actual measurable objects.
The nonpositive cross-defect term may be discarded in the recursion; the
stronger missing-degree bound is retained for the transition estimates.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped ENNReal InnerProductSpace

variable {Ω I : Type*} [MeasurableSpace Ω]

theorem IsKernelCover.peel_into {t : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {c : Ω → ℝ} (hc : IsKernelCover (t + 1) W μ c)
    {C R : Set Ω} (hC : MeasurableSet C) (hR : MeasurableSet R)
    (hC0 : μ C ≠ 0) (hR0 : μ R ≠ 0)
    (hcC : ∀ᵐ z ∂μ, z ∈ C → c z = 0)
    (hcross : ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ C → z.2 ∈ R → W z.1 z.2 = 1) :
    IsKernelCover t W (cond μ R) c := by
  classical
  letI : IsProbabilityMeasure (cond μ C) := cond_isProbabilityMeasure hC0
  letI : IsProbabilityMeasure (cond μ R) := cond_isProbabilityMeasure hR0
  let η : Fin (t + 1) → Measure Ω := fun i => if i = 0 then cond μ C else cond μ R
  letI (i : Fin (t + 1)) : IsProbabilityMeasure (η i) := by
    dsimp [η]
    split <;> infer_instance
  have he : ∀ j : Fin (t + 1), j ∉ range (Fin.succEmb t) ↔ j = 0 := by
    intro j
    simp only [Fin.coe_succEmb, Fin.range_succ, mem_compl_iff, mem_singleton_iff, not_not]
  apply hc.remove_zero_coordinates (Fin.succEmb t) η
  · intro i
    dsimp [η]
    split <;> exact cond_absolutelyContinuous
  · intro i
    simp [η, Fin.succ_ne_zero]
  · intro j hj
    have hj0 := (he j).mp hj
    subst j
    simp only [η, if_pos rfl]
    filter_upwards [hcC.filter_mono cond_absolutelyContinuous.ae_le, ae_cond_mem hC] with z hz hzC
    exact hz hzC
  · intro i j hij hout
    have hi0j0 : i = 0 ∨ j = 0 := hout.imp ((he i).mp) ((he j).mp)
    have hforward : ∀ᵐ z : Ω × Ω ∂(cond μ C).prod (cond μ R), 0 < W z.1 z.2 := by
      apply cross_positive_cond W μ hC hR
      filter_upwards [hcross] with z hz hx hy
      rw [hz hx hy]
      norm_num
    rcases hi0j0 with hi0 | hj0
    · have hj0 : j ≠ 0 := fun hj => hij (hi0.trans hj.symm)
      simpa only [η, hi0, if_pos rfl, if_neg hj0] using hforward
    · have hi0 : i ≠ 0 := fun hi => hij (hi.trans hj0.symm)
      have hs := (measurePreserving_swap (μ := cond μ R) (ν := cond μ C)).quasiMeasurePreserving.ae hforward
      filter_upwards [show ∀ᵐ z : Ω × Ω ∂(η i).prod (η j), 0 < W z.2 z.1 by
        simpa only [η, hj0, if_pos rfl, if_neg hi0, Prod.fst_swap, Prod.snd_swap] using hs]
        with z hz
      simpa only [W.symmetric z.1 z.2] using hz

namespace ZeroTwinData

variable {W : Kernel Ω} {μ : Measure Ω} {c : Ω → ℝ}

theorem ae_zero_mem_active [Fintype I] (P : ZeroTwinData W μ c I) :
    ∀ᵐ z ∂μ, c z = 0 → ∃ i, μ (P.block i) ≠ 0 ∧ z ∈ P.block i := by
  have hall : ∀ᵐ z ∂μ, ∀ i, z ∈ P.block i → μ (P.block i) ≠ 0 := by
    apply ae_all_iff.mpr
    intro i
    by_cases hi : μ (P.block i) = 0
    · have hn : ∀ᵐ z ∂μ, z ∉ P.block i := by
        simpa only [ae_iff, not_not, Set.setOf_mem_eq] using hi
      exact hn.mono fun _ hz hzC => False.elim (hz hzC)
    · exact Eventually.of_forall fun _ _ => hi
  filter_upwards [P.zero_covered, hall] with z hz hza hz0
  obtain ⟨i, hi⟩ := hz hz0
  exact ⟨i, hza i hi, hi⟩

theorem activeClasses_nonempty [Fintype I] [DecidableEq I] (P : ZeroTwinData W μ c I)
    (hZ0 : μ {z | c z = 0} ≠ 0) : (activeClasses μ P.block).Nonempty := by
  obtain ⟨z, hz, hza⟩ := exists_mem_of_measure_ne_zero_of_ae hZ0
    (ae_restrict_of_ae P.ae_zero_mem_active)
  obtain ⟨i, hi, _⟩ := hza hz
  exact ⟨i, by simp [activeClasses, hi]⟩

/-- A minimum active defect misses every zero-cover class, with all
exceptional sets assembled in the actual product measure. -/
theorem minimal_defect_anticomplete_zero [Fintype I] [SFinite μ]
    (P : ZeroTwinData W μ c I) (i : I)
    (hmin : ∀ j, μ (P.block j) ≠ 0 → P.defect i ≤ᵐ[μ] P.defect j) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ P.defect i → c z.2 = 0 → W z.1 z.2 = 0 := by
  have hmins : ∀ᵐ z ∂μ, ∀ j, μ (P.block j) ≠ 0 → z ∈ P.defect i → z ∈ P.defect j := by
    apply ae_all_iff.mpr
    intro j
    by_cases hj : μ (P.block j) = 0
    · exact Eventually.of_forall fun _ h => False.elim (h hj)
    · exact (hmin j hj).mono fun _ hz _ => hz
  have hrows : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ∀ j,
      z.2 ∈ P.block j → z.1 ∈ P.defect j → W z.2 z.1 = 0 := by
    apply ae_all_iff.mpr
    intro j
    exact (measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
      (P.defect_anticomplete j)
  filter_upwards [hrows, quasiMeasurePreserving_fst.ae hmins,
    quasiMeasurePreserving_snd.ae P.ae_zero_mem_active] with z hz hm hzero hzD hz0
  obtain ⟨j, hj, hzj⟩ := hzero hz0
  exact (W.symmetric z.1 z.2).trans (hz j hzj (hm j hj hzD))

/-- Integrating the missing degree over the minimum defect gives the exact
bound used in all of the transition estimates. -/
theorem minimal_defect_cost_bound [Fintype I] [IsProbabilityMeasure μ]
    (P : ZeroTwinData W μ c I) {r : ℕ} (hc : IsKernelCover r W μ c)
    {L θ : ℝ} (hd : ∀ᵐ z ∂μ, kernelDegree W μ z = 1 - L + θ * c z)
    (i : I) (hmin : ∀ j, μ (P.block j) ≠ 0 → P.defect i ≤ᵐ[μ] P.defect j) :
    θ * (∫ z in P.defect i, c z ∂μ) ≤
      μ.real (P.defect i) * (L - μ.real {z | c z = 0}) := by
  let Z := {z | c z = 0}
  have hZ : MeasurableSet Z := measurableSet_eq_fun hc.measurable measurable_const
  have hind := P.minimal_defect_anticomplete_zero i hmin
  have hcross : ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      z.1 ∈ P.defect i → z.2 ∈ Z → W.complement z.1 z.2 = 1 := by
    filter_upwards [hind] with z hz hx hy
    rw [Kernel.complement_apply, hz hx hy]
    norm_num
  have hDZ := kernel_inner_block_constant W.complement μ (P.measurable_defect i) hZ hcross
  have hnon := kernel_inner_nonneg_of_nonneg W.complement μ
    (blockIndicatorL2_nonneg μ (P.defect i) (P.measurable_defect i))
    (blockIndicatorL2_nonneg μ Zᶜ hZ.compl)
  have hdc : ∀ᵐ z ∂μ, kernelDegree W.complement μ z = 1 - (1 - L) + (-θ) * c z := by
    filter_upwards [hd] with z hz
    rw [kernelDegree_complement, hz]
    ring
  have hD := kernel_inner_block_one_affine W.complement μ hc.integrable hdc (P.measurable_defect i)
  have hadd := blockIndicatorL2_add_compl μ Z hZ
  rw [← hadd, map_add, inner_add_right] at hD
  rw [hDZ] at hD
  change θ * (∫ z in P.defect i, c z ∂μ) ≤ μ.real (P.defect i) * (L - μ.real Z)
  nlinarith

theorem integral_block_cover [IsFiniteMeasure μ] (P : ZeroTwinData W μ c I) (i : I) :
    (∫ z in P.block i, c z ∂μ) = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem (P.measurable_block i)] with z hz
  exact P.block_zero i z hz

theorem integral_block_union_defect_cover [IsFiniteMeasure μ] (P : ZeroTwinData W μ c I)
    (hc : Integrable c μ) (i : I) :
    (∫ z in P.block i ∪ P.defect i, c z ∂μ) = ∫ z in P.defect i, c z ∂μ := by
  rw [setIntegral_union (P.block_defect_disjoint i i) (P.measurable_defect i)
    hc.integrableOn hc.integrableOn, P.integral_block_cover i, zero_add]

theorem remainder_cost [IsProbabilityMeasure μ] (P : ZeroTwinData W μ c I)
    (hc : Integrable c μ) {x : ℝ} (hcx : (∫ z, c z ∂μ) = x) (i : I) :
    (∫ z in (P.block i ∪ P.defect i)ᶜ, c z ∂μ) = x - ∫ z in P.defect i, c z ∂μ := by
  have h := integral_add_compl ((P.measurable_block i).union (P.measurable_defect i)) hc
  rw [P.integral_block_union_defect_cover hc i, hcx] at h
  linarith

theorem defect_cost_range [IsProbabilityMeasure μ] (P : ZeroTwinData W μ c I)
    {r : ℕ} (hc : IsKernelCover r W μ c) {x : ℝ} (hcx : (∫ z, c z ∂μ) = x) (i : I) :
    (∫ z in P.defect i, c z ∂μ) ∈ Icc 0 x := by
  refine ⟨integral_nonneg hc.nonneg, ?_⟩
  have hnon : 0 ≤ ∫ z in (P.block i ∪ P.defect i)ᶜ, c z ∂μ := integral_nonneg hc.nonneg
  rw [P.remainder_cost hc.integrable hcx i] at hnon
  linarith

theorem union_mass [IsProbabilityMeasure μ] (P : ZeroTwinData W μ c I)
    {L θ : ℝ} (hd : ∀ᵐ z ∂μ, kernelDegree W μ z = 1 - L + θ * c z)
    (i : I) (hi : μ (P.block i) ≠ 0) : μ.real (P.block i ∪ P.defect i) = L := by
  rw [measureReal_union (P.block_defect_disjoint i i) (P.measurable_defect i)]
  exact P.mass_eq hd i hi

theorem remainder_mass [IsProbabilityMeasure μ] (P : ZeroTwinData W μ c I)
    {L θ : ℝ} (hd : ∀ᵐ z ∂μ, kernelDegree W μ z = 1 - L + θ * c z)
    (i : I) (hi : μ (P.block i) ≠ 0) : μ.real (P.block i ∪ P.defect i)ᶜ = 1 - L := by
  rw [measureReal_compl ((P.measurable_block i).union (P.measurable_defect i)),
    probReal_univ, P.union_mass hd i hi]

/-- The density decomposition with its nonpositive cross-defect term
discarded. It follows from exact indicator pairings and `0 ≤ W ≤ 1`. -/
theorem defect_density_bound [IsProbabilityMeasure μ] (P : ZeroTwinData W μ c I)
    {r : ℕ} (hc : IsKernelCover r W μ c) {L θ : ℝ}
    (hd : ∀ᵐ z ∂μ, kernelDegree W μ z = 1 - L + θ * c z)
    (hL1 : L < 1) (i : I) (hi : μ (P.block i) ≠ 0) :
    density μ W ≤ L * (1 - L) + (1 - L)^2 *
      density (cond μ (P.block i ∪ P.defect i)ᶜ) W +
      θ * (∫ z in P.defect i, c z ∂μ) / 2 := by
  let C := P.block i
  let D := P.defect i
  let S := C ∪ D
  have hC : MeasurableSet C := P.measurable_block i
  have hD : MeasurableSet D := P.measurable_defect i
  have hS : MeasurableSet S := hC.union hD
  have hSm : μ.real S = L := P.union_mass hd i hi
  have hRm : μ.real Sᶜ = 1 - L := P.remainder_mass hd i hi
  have hR0 : μ Sᶜ ≠ 0 := by
    intro hz
    have he : μ.real Sᶜ = 0 := by simp [measureReal_def, hz]
    linarith
  let f := blockIndicatorL2 μ C hC
  let g := blockIndicatorL2 μ D hD
  let v := blockIndicatorL2 μ S hS
  let w := blockIndicatorL2 μ Sᶜ hS.compl
  have hv : v = f + g := blockIndicatorL2_union μ hC hD (P.block_defect_disjoint i i)
  have hall : f + g + w = constantL2 μ 1 := by
    rw [← hv]
    exact blockIndicatorL2_add_compl μ S hS
  have hfg : ⟪f, kernelOperator W μ g⟫_ℝ = 0 := by
    have h := kernel_inner_block_constant W μ hC hD (P.defect_anticomplete i)
    simpa only [zero_mul] using h
  have hgf : ⟪g, kernelOperator W μ f⟫_ℝ = 0 := by
    rw [kernel_inner_comm W μ g f]
    exact hfg
  have hff : ⟪f, kernelOperator W μ f⟫_ℝ = 0 := by
    have h := kernel_inner_block_constant W μ hC hC (P.independent i)
    simpa only [zero_mul] using h
  have hvv : ⟪v, kernelOperator W μ v⟫_ℝ = ⟪g, kernelOperator W μ g⟫_ℝ := by
    rw [hv, map_add, inner_add_left, inner_add_right, inner_add_right, hff, hfg, hgf]
    ring
  have hcostS : (∫ z in S, c z ∂μ) = ∫ z in D, c z ∂μ :=
    P.integral_block_union_defect_cover hc.integrable i
  have hdegS : ⟪v, kernelOperator W μ (constantL2 μ 1)⟫_ℝ =
      L * (1 - L) + θ * ∫ z in D, c z ∂μ := by
    rw [kernel_inner_block_one_affine W μ hc.integrable hd hS, hSm, hcostS]
    ring
  have hdegD := kernel_inner_block_one_affine W μ hc.integrable hd hD
  have hcrossle := kernel_inner_blocks_le W μ hD hS.compl
  rw [hRm] at hcrossle
  have hquad : θ * (∫ z in D, c z ∂μ) ≤ ⟪g, kernelOperator W μ g⟫_ℝ := by
    rw [← hall, map_add, map_add, inner_add_right, inner_add_right] at hdegD
    change ⟪g, kernelOperator W μ f⟫_ℝ + ⟪g, kernelOperator W μ g⟫_ℝ +
      ⟪g, kernelOperator W μ w⟫_ℝ = _ at hdegD
    rw [hgf] at hdegD
    change ⟪g, kernelOperator W μ w⟫_ℝ ≤ _ at hcrossle
    nlinarith
  have he := density_remove_region W μ hS hR0
  change density μ W = ⟪v, kernelOperator W μ (constantL2 μ 1)⟫_ℝ -
    ⟪v, kernelOperator W μ v⟫_ℝ / 2 + _ at he
  rw [hdegS, hvv, hRm] at he
  change density μ W ≤ L * (1 - L) + (1 - L)^2 * density (cond μ Sᶜ) W +
    θ * (∫ z in D, c z ∂μ) / 2
  linarith

/-- The genuine lower-order density recursion, obtained from a real
fractional `K_(r-1)` cover on the normalized remainder. -/
theorem peeling_recursion [IsProbabilityMeasure μ] (P : ZeroTwinData W μ c I)
    {r : ℕ} (hr : 3 ≤ r) (hc : IsKernelCover r W μ c)
    {x L θ : ℝ} (hcx : (∫ z, c z ∂μ) = x)
    (hd : ∀ᵐ z ∂μ, kernelDegree W μ z = 1 - L + θ * c z)
    (hL1 : L < 1) (hLx : L ≤ 1 - ((r - 1 : ℕ) : ℝ) * x)
    (i : I) (hi : μ (P.block i) ≠ 0) :
    density μ W ≤ L * (1 - L) + (1 - L)^2 *
      Phi (r - 1) ((x - ∫ z in P.defect i, c z ∂μ) / (1 - L)) +
      θ * (∫ z in P.defect i, c z ∂μ) / 2 := by
  let S := P.block i ∪ P.defect i
  have hS : MeasurableSet S := (P.measurable_block i).union (P.measurable_defect i)
  have hRm : μ.real Sᶜ = 1 - L := P.remainder_mass hd i hi
  have hR0 : μ Sᶜ ≠ 0 := by
    intro hz
    have he : μ.real Sᶜ = 0 := by simp [measureReal_def, hz]
    linarith
  letI : IsProbabilityMeasure (cond μ Sᶜ) := cond_isProbabilityMeasure hR0
  have hcr : IsKernelCover (r - 1) W (cond μ Sᶜ) c := by
    have hc' : IsKernelCover ((r - 1) + 1) W μ c := by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ r)] using hc
    exact hc'.peel_into (P.measurable_block i) hS.compl hi hR0
      (Eventually.of_forall (P.block_zero i)) (P.outside_complete i)
  have hcost : (∫ z, c z ∂cond μ Sᶜ) =
      (x - ∫ z in P.defect i, c z ∂μ) / (1 - L) := by
    rw [integral_cond_eq_normalized, P.remainder_cost hc.integrable hcx i, hRm]
    ring
  have ha := P.defect_cost_range hc hcx i
  have hrp : (0 : ℝ) < (r - 1 : ℕ) := by exact_mod_cast (by omega : 0 < r - 1)
  have hy : (x - ∫ z in P.defect i, c z ∂μ) / (1 - L) ≤ 1 / ((r - 1 : ℕ) : ℝ) := by
    apply (div_le_div_iff₀ (by linarith : 0 < 1 - L) hrp).mpr
    nlinarith [mul_nonneg hrp.le ha.1]
  have hsmall := kernel_clique_cover_density_bound (by omega : 2 ≤ r - 1) hcr
    (by rw [hcost]; exact hy)
  rw [hcost] at hsmall
  have hrec := P.defect_density_bound hc hd hL1 i hi
  exact hrec.trans (by
    have hmul := mul_le_mul_of_nonneg_left hsmall (sq_nonneg (1 - L))
    linarith)

end ZeroTwinData

end DensityHS.Graphon
