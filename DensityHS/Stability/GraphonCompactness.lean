module

public import DensityHS.Stability.FiniteCompactness
public import DensityHS.Stability.Compactness

/-!
# Uniform graphon stability from equality classification

Author and maintainer: Xizhi Liu.

The parameter is included in the actual compact feasible space. This
intermediate theorem requires the equality classification and the local
same-parameter approximation; compactness and all metric estimates are
fully instantiated here.
-/

@[expose] public section

namespace DensityHS.Stability

open MeasureTheory Filter Set Graphon Constructions
open scoped Topology

theorem graphon_cut_stability_of_classification {r : ℕ} (hr : 3 ≤ r)
    (hclassification : ∀ x ∈ Icc 0 (1/(r : ℝ)),
      ∀ W : Vendor.GraphonSpace ℝ unitMeasure,
      graphonSpaceTilingNumber unitMeasure r (by omega) W ≤ x →
      graphonSpaceDensity unitMeasure W = Phi r x → W ∈ activeFamily r x)
    (happrox : ∀ x ∈ Icc 0 (1/(r : ℝ)),
      ∀ W : Vendor.GraphonSpace ℝ unitMeasure, W ∈ activeFamily r x →
      ∀ ρ η : ℝ, 0 < ρ → 0 < η → ∃ a > 0,
        ∀ y ∈ Icc 0 (1/(r : ℝ)), |y-x| < a →
          ∃ U ∈ nearActiveFamily r y η, dist W U < ρ)
    {ρ η : ℝ} (hρ : 0 < ρ) (hη : 0 < η) :
    ∃ δ > 0, ∀ x ∈ Icc 0 (1/(r : ℝ)),
      ∀ W : Vendor.GraphonSpace ℝ unitMeasure,
      graphonSpaceTilingNumber unitMeasure r (by omega) W ≤ x →
      Phi r x-δ ≤ graphonSpaceDensity unitMeasure W →
      ∃ U ∈ nearActiveFamily r x η, dist W U < ρ := by
  let P := Icc (0 : ℝ) (1/(r : ℝ))
  let X := Vendor.GraphonSpace ℝ unitMeasure
  let accepted : P → X → Prop := fun x W => ∃ U ∈ nearActiveFamily r x.val η, dist W U < ρ
  have htarget : Continuous (fun p : P => Phi r p.val) := by
    have he : (fun p : P => Phi r p.val) = fun p : P => continuousEnvelope r p.val :=
      funext (fun p => Phi_eq_continuousEnvelope hr p.property)
    rw [he]
    exact (continuous_continuousEnvelope r).comp continuous_subtype_val
  have hlocal : ∀ (p : P) (W : X),
      graphonSpaceTilingNumber unitMeasure r (by omega) W ≤ p.val →
      graphonSpaceDensity unitMeasure W=Phi r p.val →
      (p,W) ∈ interior {z : P × X | accepted z.1 z.2} := by
    intro p W ht he
    have hactive := hclassification p.val p.property W ht he
    obtain ⟨a, ha, hnear⟩ := happrox p.val p.property W hactive (ρ/2) η (half_pos hρ) hη
    rw [mem_interior_iff_mem_nhds]
    apply Metric.mem_nhds_iff.mpr
    refine ⟨min a (ρ/2), lt_min ha (half_pos hρ), ?_⟩
    intro z hz
    have hdist : dist z.1 p < min a (ρ/2) ∧ dist z.2 W < min a (ρ/2) := by
      simpa only [Metric.mem_ball, Prod.dist_eq, max_lt_iff] using hz
    have hx : |z.1.val-p.val| < a := by
      have hh := hdist.1.trans_le (min_le_left _ _)
      simpa only [Subtype.dist_eq, Real.dist_eq] using hh
    obtain ⟨U, hU, hdU⟩ := hnear z.1.val z.1.property hx
    refine ⟨U, hU, (dist_triangle z.2 W U).trans_lt ?_⟩
    have hzW := hdist.2.trans_le (min_le_right _ _)
    linarith
  obtain ⟨δ, hδ, hgap⟩ := uniform_stability_of_lowerSemicontinuous_constraint
    (graphonSpaceTilingNumber unitMeasure r (by omega))
    (lowerSemicontinuous_graphonSpaceTilingNumber unitMeasure (by omega))
    (fun p : P => p.val) (fun p : P => Phi r p.val) (graphonSpaceDensity unitMeasure)
    continuous_subtype_val htarget (continuous_graphonSpaceDensity unitMeasure) accepted
    (fun p W ht => graphon_density_le_Phi_of_tiling_le hr p.property W ht) hlocal
  refine ⟨δ, hδ, ?_⟩
  intro x hx W ht he
  exact hgap ⟨x,hx⟩ W ht he

theorem graphon_L1_stability_of_classification {r : ℕ} (hr : 3 ≤ r)
    (hclassification : ∀ x ∈ Icc 0 (1/(r : ℝ)),
      ∀ W : Vendor.GraphonSpace ℝ unitMeasure,
      graphonSpaceTilingNumber unitMeasure r (by omega) W ≤ x →
      graphonSpaceDensity unitMeasure W = Phi r x → W ∈ activeFamily r x)
    (happrox : ∀ x ∈ Icc 0 (1/(r : ℝ)),
      ∀ W : Vendor.GraphonSpace ℝ unitMeasure, W ∈ activeFamily r x →
      ∀ ρ η : ℝ, 0 < ρ → 0 < η → ∃ a > 0,
        ∀ y ∈ Icc 0 (1/(r : ℝ)), |y-x| < a →
          ∃ U ∈ nearActiveFamily r y η, dist W U < ρ)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ > 0, ∀ x ∈ Icc 0 (1/(r : ℝ)), ∀ W : Kernel ℝ,
      tilingNumber r W unitMeasure ≤ x → Phi r x-δ ≤ density unitMeasure W →
      ∃ t : ConstructionKind r, ∃ z : Fin (r-1) → ℝ,
        IsProbabilityWeight z ∧ constructionDomain r t x ∧
        Phi r x-η ≤ constructionDensity r t x ∧
        relabelL1Distance unitMeasure W (constructionKernel r t (x,z)) < ε := by
  let M := 2*r-1
  have hM : (0 : ℝ) < M := by dsimp [M]; exact_mod_cast (by omega : 0 < 2*r-1)
  obtain ⟨δ, hδ, hstab⟩ := graphon_cut_stability_of_classification hr hclassification happrox
    (div_pos hε (sq_pos_of_pos hM)) hη
  refine ⟨δ, hδ, ?_⟩
  intro x hx W ht he
  let Wq := Vendor.GraphonSpace.mk (W.toVendorGraphon unitMeasure)
  obtain ⟨U, hU, hdist⟩ := hstab x hx Wq
    (by simpa only [Wq, graphonSpaceTilingNumber_kernel] using ht)
    (by simpa only [Wq, graphonSpaceDensity_kernel] using he)
  obtain ⟨t, z, _, hz, hd, hnear, hmodel⟩ := (mem_nearActiveGraph_iff hr).mp hU
  refine ⟨t, z, hz, hd, hnear, ?_⟩
  apply (construction_relabelL1_bound (by omega : 2 ≤ r) t (x,z) W).trans_lt
  have hcut : Vendor.Graphon.cutDistance (W.toVendorGraphon unitMeasure)
      ((constructionKernel r t (x,z)).toVendorGraphon unitMeasure) < ε/(M : ℝ)^2 := by
    rw [hmodel] at hdist
    cases t <;> exact hdist
  change (M : ℝ)^2 * _ < ε
  simpa only [mul_comm] using (lt_div_iff₀ (sq_pos_of_pos hM)).mp hcut

end DensityHS.Stability
