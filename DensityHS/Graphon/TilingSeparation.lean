module

public import DensityHS.Graphon.TilingL2
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# Separation for approximate kernel tilings

Author and maintainer: Xizhi Liu.

The closed convex hull of fixed-mass clique loads and nonnegative slack
contains the unit capacity whenever every cover costs at least that mass.
Separation would otherwise produce a cheaper bounded measurable cover.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set
open scoped ENNReal InnerProductSpace Pointwise

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Integration as a continuous linear functional on a probability `L²` space. -/
noncomputable def integralL2 (μ : Measure Ω) [IsProbabilityMeasure μ] : Lp ℝ 2 μ →L[ℝ] ℝ :=
  innerSL ℝ (constantL2 μ 1)

theorem integralL2_apply (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Lp ℝ 2 μ) :
    integralL2 μ f = ∫ x, f x ∂μ := inner_constantL2_one μ f

theorem constantL2_one_nonneg (μ : Measure Ω) [IsProbabilityMeasure μ] :
    0 ≤ constantL2 μ 1 := by
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [constantL2_coe μ 1] with x hx
  simp [hx]

theorem cliqueIndicatorL2_nonneg (r : ℕ) (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] : 0 ≤ cliqueIndicatorL2 r W μ := by
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [cliqueIndicatorL2_coe r W μ] with z hz
  rw [hz]
  exact Set.indicator_nonneg (fun _ _ => by norm_num) z

theorem cliqueIndicatorL2_supported (r : ℕ) (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] : IsCliqueSupportedL2 r W μ (cliqueIndicatorL2 r W μ) := by
  filter_upwards [cliqueIndicatorL2_coe r W μ] with z hz hzs
  exact hz.trans (Set.indicator_of_notMem hzs _)

theorem l2_eq_zero_of_nonneg_integral_zero {μ : Measure Ω} [IsProbabilityMeasure μ]
    (f : Lp ℝ 2 μ) (hf : 0 ≤ f) (hi : integralL2 μ f = 0) : f = 0 := by
  rw [integralL2_apply] at hi
  have hz := (integral_eq_zero_iff_of_nonneg_ae
    ((Lp.coeFn_nonneg f).mpr hf) (l2_integrable μ f)).mp hi
  apply Lp.ext
  exact hz.trans (Lp.coeFn_zero ℝ 2 μ).symm

theorem cliqueIndicator_integral_pos_of_coverNumber_pos {r : ℕ} {W : Kernel Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (hpos : 0 < coverNumber r W μ) :
    0 < integralL2 (Measure.pi (fun _ : Fin r => μ)) (cliqueIndicatorL2 r W μ) := by
  let χ := cliqueIndicatorL2 r W μ
  have hi0 : 0 ≤ integralL2 (Measure.pi (fun _ : Fin r => μ)) χ :=
    l2_inner_nonneg (constantL2_one_nonneg _) (cliqueIndicatorL2_nonneg r W μ)
  by_contra! hi
  have hχ0 : χ = 0 := l2_eq_zero_of_nonneg_integral_zero χ
    (cliqueIndicatorL2_nonneg r W μ) (le_antisymm hi hi0)
  have hc : IsKernelCover r W μ 0 := by
    refine ⟨measurable_const, fun _ => by norm_num, ?_⟩
    have hχeq := cliqueIndicatorL2_coe r W μ
    change ⇑χ =ᵐ[Measure.pi (fun _ : Fin r => μ)] _ at hχeq
    rw [hχ0] at hχeq
    filter_upwards [hχeq, Lp.coeFn_zero ℝ 2 (Measure.pi (fun _ : Fin r => μ))]
      with z hz hz0 hcl
    have hmem : z ∈ cliqueTuples r W := hcl
    rw [hz0, Set.indicator_of_mem hmem] at hz
    norm_num at hz
  have := coverNumber_le_cost hc
  simp only [Pi.zero_apply, integral_zero] at this
  linarith

/-- Positive clique densities with prescribed integral. -/
def cliqueMassSimplexL2 (r : ℕ) (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x : ℝ) : Set (Lp ℝ 2 (Measure.pi (fun _ : Fin r => μ))) :=
  {t | 0 ≤ t ∧ IsCliqueSupportedL2 r W μ t ∧
    integralL2 (Measure.pi (fun _ : Fin r => μ)) t = x}

theorem convex_cliqueMassSimplexL2 (r : ℕ) (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (x : ℝ) : Convex ℝ (cliqueMassSimplexL2 r W μ x) := by
  intro t ht q hq a b ha hb hab
  refine ⟨add_nonneg (smul_nonneg ha ht.1) (smul_nonneg hb hq.1), ?_, ?_⟩
  · filter_upwards [ht.2.1, hq.2.1, Lp.coeFn_add (a • t) (b • q),
      Lp.coeFn_smul a t, Lp.coeFn_smul b q] with z htz hqz hadd hat hbq hz
    simp only [hadd, hat, hbq, Pi.add_apply, Pi.smul_apply, smul_eq_mul, htz hz, hqz hz,
      mul_zero, add_zero]
  · simp only [map_add, map_smul, smul_eq_mul, ht.2.2, hq.2.2]
    rw [← add_mul, hab, one_mul]

theorem smul_mem_cliqueMassSimplexL2 {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {t : Lp ℝ 2 (Measure.pi (fun _ : Fin r => μ))}
    (ht : 0 ≤ t) (hs : IsCliqueSupportedL2 r W μ t)
    {x : ℝ} (hx : 0 ≤ x)
    (hi : 0 < integralL2 (Measure.pi (fun _ : Fin r => μ)) t) :
    (x / integralL2 (Measure.pi (fun _ : Fin r => μ)) t) • t ∈
      cliqueMassSimplexL2 r W μ x := by
  refine ⟨smul_nonneg (div_nonneg hx hi.le) ht, ?_, ?_⟩
  · filter_upwards [hs, Lp.coeFn_smul (x / integralL2 (Measure.pi (fun _ : Fin r => μ)) t) t]
      with z hz hsm hzs
    simp only [hsm, Pi.smul_apply, smul_eq_mul, hz hzs, mul_zero]
  · simp only [map_smul, smul_eq_mul, div_mul_cancel₀ _ hi.ne']

theorem cliqueMassSimplexL2_nonempty {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {x : ℝ} (hx : 0 < x) (hmin : x ≤ coverNumber r W μ) :
    (cliqueMassSimplexL2 r W μ x).Nonempty := by
  have hpos := cliqueIndicator_integral_pos_of_coverNumber_pos (hx.trans_le hmin)
  exact ⟨_, smul_mem_cliqueMassSimplexL2 (cliqueIndicatorL2_nonneg r W μ)
    (cliqueIndicatorL2_supported r W μ) hx.le hpos⟩

/-- A linear functional bounded below on a translate of the positive cone
is nonnegative on that cone. -/
theorem l2_functional_nonneg_of_lowerBound {μ : Measure Ω}
    (f : Lp ℝ 2 μ →L[ℝ] ℝ) (b : Lp ℝ 2 μ) (u : ℝ)
    (h : ∀ q : Lp ℝ 2 μ, 0 ≤ q → u < f (b + q)) :
    ∀ q : Lp ℝ 2 μ, 0 ≤ q → 0 ≤ f q := by
  intro q hq
  by_contra! hneg
  have hb : u < f b := by simpa using h 0 le_rfl
  let a := (f b - u + 1) / (-f q)
  have ha : 0 ≤ a := le_of_lt (div_pos (by linarith) (neg_pos.mpr hneg))
  have hmul : a * (-f q) = f b - u + 1 := div_mul_cancel₀ _ (neg_pos.mpr hneg).ne'
  have hbad := h (a • q) (smul_nonneg ha hq)
  rw [map_add, map_smul, smul_eq_mul] at hbad
  nlinarith

/-- Separation places the unit capacity in the norm closure of fixed-mass
clique loads plus nonnegative slack. -/
theorem unit_mem_closure_clique_loads {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {x : ℝ} (hx : 0 < x) (hmin : x ≤ coverNumber r W μ) :
    constantL2 μ 1 ∈ closure
      ((marginalLoadL2 r μ) '' cliqueMassSimplexL2 r W μ x + Set.Ici 0) := by
  classical
  let C := (marginalLoadL2 r μ) '' cliqueMassSimplexL2 r W μ x + Set.Ici 0
  have hconv : Convex ℝ C :=
    ((convex_cliqueMassSimplexL2 r W μ x).linear_image
      (marginalLoadL2 r μ).toLinearMap).add (convex_Ici 0)
  obtain ⟨t0, ht0⟩ := cliqueMassSimplexL2_nonempty hx hmin
  have hgen : ∀ t ∈ cliqueMassSimplexL2 r W μ x, ∀ q : Lp ℝ 2 μ, 0 ≤ q →
      marginalLoadL2 r μ t + q ∈ closure C := by
    intro t ht q hq
    exact subset_closure ⟨_, ⟨t, ht, rfl⟩, q, hq, rfl⟩
  by_contra hnot
  obtain ⟨φ, u, hφ1, hsep⟩ := geometric_hahn_banach_point_closed
    hconv.closure isClosed_closure hnot
  let f := (InnerProductSpace.toDual ℝ (Lp ℝ 2 μ)).symm φ
  have hrepr : ∀ q, φ q = ⟪f, q⟫_ℝ := fun q => InnerProductSpace.toDual_symm_apply.symm
  have hφpos := l2_functional_nonneg_of_lowerBound φ (marginalLoadL2 r μ t0) u
    (fun q hq => hsep _ (hgen t0 ht0 q hq))
  have hf : 0 ≤ f := l2_nonneg_of_inner_nonneg f (fun q hq => by
    rw [← hrepr]
    exact hφpos q hq)
  have hu : 0 < u := lt_of_le_of_lt (hφpos _ (constantL2_one_nonneg μ)) hφ1
  let ν := Measure.pi (fun _ : Fin r => μ)
  let F := x • coordinateSumL2 r μ f - u • constantL2 ν 1
  have hF : ∀ᵐ z ∂ν, z ∈ cliqueTuples r W → 0 ≤ F z := by
    apply l2_nonneg_on_set_of_inner_nonneg F (measurableSet_cliqueTuples r W)
    intro t ht hs
    let I := integralL2 ν t
    have hI0 : 0 ≤ I := l2_inner_nonneg (constantL2_one_nonneg ν) ht
    by_cases hI : I = 0
    · have htz : t = 0 := l2_eq_zero_of_nonneg_integral_zero t ht hI
      simp [htz]
    · have hIp : 0 < I := lt_of_le_of_ne hI0 (Ne.symm hI)
      have htm := smul_mem_cliqueMassSimplexL2 ht hs hx.le hIp
      have hsep' := hsep _ (hgen _ htm 0 le_rfl)
      simp only [add_zero, map_smul, smul_eq_mul, hrepr] at hsep'
      rw [real_inner_smul_right, real_inner_comm (marginalLoadL2 r μ t) f,
        marginalLoadL2_inner, real_inner_comm (coordinateSumL2 r μ f) t] at hsep'
      have hmul : (x / I) * ⟪coordinateSumL2 r μ f, t⟫_ℝ * I =
          x * ⟪coordinateSumL2 r μ f, t⟫_ℝ := by
        field_simp
      have hsepI := mul_lt_mul_of_pos_right hsep' hIp
      change 0 ≤ ⟪x • coordinateSumL2 r μ f - u • constantL2 ν 1, t⟫_ℝ
      rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left]
      change 0 ≤ x * ⟪coordinateSumL2 r μ f, t⟫_ℝ - u * I
      change u * I < (x / I) * ⟪coordinateSumL2 r μ f, t⟫_ℝ * I at hsepI
      rw [hmul] at hsepI
      linarith
  let d := (x / u) • f
  have hd : 0 ≤ d := smul_nonneg (div_nonneg hx.le hu.le) hf
  have hdcover : ∀ᵐ z ∂ν, z ∈ cliqueTuples r W → 1 ≤ ∑ i, d (z i) := by
    have hdc : ∀ᵐ z ∂ν, ∀ i, d (z i) = (x / u) * f (z i) :=
      ae_all_iff.mpr fun i =>
        (measurePreserving_eval (fun _ : Fin r => μ) i).quasiMeasurePreserving.ae
          (Lp.coeFn_smul (x / u) f)
    filter_upwards [hF, Lp.coeFn_sub (x • coordinateSumL2 r μ f) (u • constantL2 ν 1),
      Lp.coeFn_smul x (coordinateSumL2 r μ f), Lp.coeFn_smul u (constantL2 ν 1),
      coordinateSumL2_coe r μ f, constantL2_coe ν 1, hdc] with z hz hsub hsm hsu hsum h1 hdz
    intro hcl
    have hz' := hz hcl
    change 0 ≤ (x • coordinateSumL2 r μ f - u • constantL2 ν 1) z at hz'
    simp only [hsub, hsm, hsu, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hsum, h1,
      mul_one] at hz'
    simp only [hdz, ← Finset.mul_sum]
    have heq : (x / u) * (∑ i, f (z i)) = (x * ∑ i, f (z i)) / u := by ring
    rw [heq]
    exact (le_div_iff₀ hu).mpr (by linarith)
  obtain ⟨c, hc, hcost⟩ := exists_kernelCover_of_nonnegative_L2 d hd hdcover
  have hdint : (∫ z, d z ∂μ) = (x / u) * φ (constantL2 μ 1) := by
    rw [← integralL2_apply]
    change integralL2 μ ((x / u) • f) = _
    rw [map_smul, smul_eq_mul, hrepr, real_inner_comm (constantL2 μ 1) f]
    rfl
  have hlt : (x / u) * φ (constantL2 μ 1) < x := by
    have hscale : 0 < x / u := div_pos hx hu
    have h := mul_lt_mul_of_pos_left hφ1 hscale
    rwa [div_mul_cancel₀ _ hu.ne'] at h
  have hbound := hmin.trans (coverNumber_le_cost hc)
  rw [hdint] at hcost
  linarith

/-- Every lower bound on cover cost admits fixed-mass clique densities whose
marginal loads differ from an admissible capacity by arbitrarily little in `L²`. -/
theorem exists_clique_density_approximate_load {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {x ε : ℝ} (hx : 0 < x) (hmin : x ≤ coverNumber r W μ)
    (hε : 0 < ε) :
    ∃ t : Lp ℝ 2 (Measure.pi (fun _ : Fin r => μ)),
      t ∈ cliqueMassSimplexL2 r W μ x ∧ ∃ q : Lp ℝ 2 μ,
        0 ≤ q ∧ ‖marginalLoadL2 r μ t + q - constantL2 μ 1‖ < ε := by
  obtain ⟨y, ⟨_, ⟨t, ht, rfl⟩, q, hq, rfl⟩, hy⟩ :=
    Metric.mem_closure_iff.mp (unit_mem_closure_clique_loads hx hmin) ε hε
  refine ⟨t, ht, q, hq, ?_⟩
  simpa only [dist_eq_norm, norm_sub_rev] using hy

end DensityHS.Graphon
