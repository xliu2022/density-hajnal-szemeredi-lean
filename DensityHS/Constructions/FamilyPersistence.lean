module

public import DensityHS.Constructions.EndpointIdentity
public import DensityHS.Constructions.FamilyLimits

/-!
# Persistence of active models at nearby original parameters

Author and maintainer: Xizhi Liu.

An active model at x0 is approximated, at every sufficiently close original
parameter x, by an admissible near-active model at x. The only branch that
can lose admissibility is A at its right endpoint, where the actual model
equals B2 and continues through that ordinary branch.
-/

@[expose] public section

namespace DensityHS.Constructions

open MeasureTheory Set Filter
open scoped Topology

theorem eventually_candidate_close_and_near {r : ℕ} (hr : 3 ≤ r)
    (t : ConstructionKind r) (z : Fin (r - 1) → ℝ) {x₀ : ℝ}
    (hx₀ : x₀ ∈ Icc 0 (1 / (r : ℝ)))
    (hactive : constructionDensity r t x₀ = Phi r x₀) {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) :
    ∀ᶠ x in 𝓝 x₀,
      dist (constructionGraphon r t (x, z)) (constructionGraphon r t (x₀, z)) < ε ∧
        (x ∈ Icc 0 (1 / (r : ℝ)) → Phi r x - η ≤ constructionDensity r t x) := by
  have hG : Continuous (fun x => constructionGraphon r t (x, z)) :=
    (continuous_constructionGraphon r t).comp (continuous_id.prodMk continuous_const)
  have hg : Continuous (fun x => continuousEnvelope r x - constructionDensity r t x) :=
    (continuous_continuousEnvelope r).sub (continuous_constructionDensity r t)
  have hg₀ : continuousEnvelope r x₀ - constructionDensity r t x₀ = 0 := by
    rw [hactive, Phi_eq_continuousEnvelope hr hx₀, sub_self]
  have hball : ∀ᶠ x in 𝓝 x₀,
      dist (constructionGraphon r t (x, z)) (constructionGraphon r t (x₀, z)) < ε :=
    (isOpen_lt (hG.dist continuous_const) continuous_const).mem_nhds (by simpa using hε)
  have hgap : ∀ᶠ x in 𝓝 x₀, continuousEnvelope r x - constructionDensity r t x < η :=
    (isOpen_lt hg continuous_const).mem_nhds (by
      change continuousEnvelope r x₀ - constructionDensity r t x₀ < η
      rw [hg₀]
      exact hη)
  filter_upwards [hball, hgap] with x hball hgap
  refine ⟨hball, ?_⟩
  intro hx
  rw [Phi_eq_continuousEnvelope hr hx]
  linarith

theorem eventually_branch_persists {r : ℕ} (hr : 3 ≤ r)
    (t : ConstructionKind r) (z : Fin (r - 1) → ℝ) (hz : IsProbabilityWeight z)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Icc 0 (1 / (r : ℝ)))
    (hactive : constructionDensity r t x₀ = Phi r x₀)
    (hdom : ∀ᶠ x in 𝓝 x₀, x ∈ Icc 0 (1 / (r : ℝ)) → constructionDomain r t x)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∀ᶠ x in 𝓝 x₀, x ∈ Icc 0 (1 / (r : ℝ)) →
      ∃ U ∈ nearActiveFamily r x η,
        dist U (constructionGraphon r t (x₀, z)) < ε := by
  filter_upwards [eventually_candidate_close_and_near hr t z hx₀ hactive hε hη, hdom]
    with x hx hd hxi
  refine ⟨constructionGraphon r t (x, z), ?_, hx.1⟩
  apply (mem_nearActiveGraph_iff hr).mpr
  exact ⟨t, z, hxi, hz, hd hxi, hx.2 hxi, rfl⟩

/-- The active-family graph is lower continuous into every positive
near-active tolerance, with models always at the original nearby parameter. -/
theorem eventually_activeFamily_persists {r : ℕ} (hr : 3 ≤ r)
    {x₀ : ℝ} {U₀ : Vendor.GraphonSpace ℝ unitMeasure}
    (hU₀ : U₀ ∈ activeFamily r x₀) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∀ᶠ x in 𝓝 x₀, x ∈ Icc 0 (1 / (r : ℝ)) →
      ∃ U ∈ nearActiveFamily r x η, dist U U₀ < ε := by
  obtain ⟨t, z, hx₀, hz, hd, he, rfl⟩ := (mem_activeFamily_iff hr).mp hU₀
  cases t with
  | ordinary i =>
    apply eventually_branch_persists hr (.ordinary i) z hz hx₀ he.symm _ hε hη
    exact Eventually.of_forall fun _ _ => trivial
  | exceptional =>
    by_cases hxend : x₀ = AEnd r
    · subst x₀
      let b : ConstructionKind r := .ordinary ⟨1, by omega⟩
      have hbactive : constructionDensity r b (AEnd r) = Phi r (AEnd r) := by
        change B r 2 (AEnd r) = Phi r (AEnd r)
        exact (A_tangent_eq_B_two hr).symm.trans he.symm
      have hmodel : constructionGraphon r .exceptional (AEnd r, z) =
          constructionGraphon r b (AEnd r, z) := exceptionalGraphon_at_end hr
      have hA := eventually_candidate_close_and_near hr .exceptional z hx₀ he.symm hε hη
      have hB := eventually_candidate_close_and_near hr b z hx₀ hbactive hε hη
      filter_upwards [hA, hB] with x hA hB hxi
      by_cases hxe : x ≤ AEnd r
      · refine ⟨constructionGraphon r .exceptional (x, z), ?_, hA.1⟩
        apply (mem_nearActiveGraph_iff hr).mpr
        exact ⟨.exceptional, z, hxi, hz, ⟨hxi.1, hxe⟩, hA.2 hxi, rfl⟩
      · refine ⟨constructionGraphon r b (x, z), ?_, ?_⟩
        · apply (mem_nearActiveGraph_iff hr).mpr
          exact ⟨b, z, hxi, hz, trivial, hB.2 hxi, rfl⟩
        · simpa only [hmodel] using hB.1
    · have hxe : x₀ < AEnd r := lt_of_le_of_ne hd.2 hxend
      apply eventually_branch_persists hr .exceptional z hz hx₀ he.symm _ hε hη
      filter_upwards [Iio_mem_nhds hxe] with x hx hxi
      exact ⟨hxi.1, le_of_lt hx⟩
  | final =>
    have hstart : RCrossing r ≤ x₀ := (R_active_iff hr hx₀).mp ⟨hd, he.symm⟩
    have hleft : ((r : ℝ) - 2) / ((r : ℝ) * ((r : ℝ) - 1)) < x₀ :=
      (RCrossing_gt_left_endpoint hr).trans_le hstart
    apply eventually_branch_persists hr .final z hz hx₀ he.symm _ hε hη
    filter_upwards [Ioi_mem_nhds hleft] with x hx hxi
    exact ⟨le_of_lt hx, hxi.2⟩

/-- Quantitative neighbourhood form used in finite stability arguments. -/
theorem activeFamily_persists {r : ℕ} (hr : 3 ≤ r)
    {x₀ : ℝ} {U₀ : Vendor.GraphonSpace ℝ unitMeasure}
    (hU₀ : U₀ ∈ activeFamily r x₀) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Icc 0 (1 / (r : ℝ)), |x - x₀| < δ →
      ∃ U ∈ nearActiveFamily r x η, dist U U₀ < ε := by
  obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff.mp
    (eventually_activeFamily_persists hr hU₀ hε hη)
  refine ⟨δ, hδ, ?_⟩
  intro x hx hdist
  exact h (by simpa only [Real.dist_eq] using hdist) hx

end DensityHS.Constructions

