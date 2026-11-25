module

public import DensityHS.Graphon.RegularModels
public import DensityHS.Graphon.MetricTilings
public import DensityHS.Constructions.FiniteTemplate

/-!
# Integral finite clique packings pass to graphon limits

Author and maintainer: Xizhi Liu.

Finite graphs are represented on actual equal interval cells. Regularity
and integer rounding produce nearby kernels with the correct tiling bound;
the proved cut-metric lower semicontinuity then gives the limit inequality.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Filter Regularity Constructions
open scoped Topology

universe u

variable {V : Type u} [Fintype V] [Nonempty V]

noncomputable def finiteGraphKernel (G : SimpleGraph V) : Kernel ℝ :=
  (FiniteTemplate.ofSimpleGraph G).kernel (uniformWeight V)

noncomputable def finiteGraphon (G : SimpleGraph V) : Vendor.GraphonSpace ℝ unitMeasure :=
  Vendor.GraphonSpace.mk ((finiteGraphKernel G).toVendorGraphon unitMeasure)

theorem finiteGraphKernel_apply (G : SimpleGraph V) [DecidableRel G.Adj] (x y : ℝ) :
    finiteGraphKernel G x y = indicatorMatrix G
      (intervalLabel (uniformWeight V) x) (intervalLabel (uniformWeight V) y) := by
  classical
  by_cases h : G.Adj (intervalLabel (uniformWeight V) x) (intervalLabel (uniformWeight V) y)
  · simp [finiteGraphKernel,FiniteTemplate.kernel_apply,FiniteTemplate.ofSimpleGraph,
      indicatorMatrix,h]
  · simp [finiteGraphKernel,FiniteTemplate.kernel_apply,FiniteTemplate.ofSimpleGraph,
      indicatorMatrix,h]

theorem density_finiteGraphKernel [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    density unitMeasure (finiteGraphKernel G) =
      (G.edgeFinset.card : ℝ)/(Fintype.card V : ℝ)^2 := by
  rw [finiteGraphKernel,FiniteTemplate.density_ofSimpleGraph G uniformWeight_probability,
    edgeMass_uniform]

theorem density_finiteGraphon [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    graphonSpaceDensity unitMeasure (finiteGraphon G) =
      (G.edgeFinset.card : ℝ)/(Fintype.card V : ℝ)^2 := by
  rw [finiteGraphon,graphonSpaceDensity_kernel,density_finiteGraphKernel]

theorem exists_finiteGraphon_model {r : ℕ} (hr : 3 ≤ r)
    {ρ τ : ℝ} (hρ : 0 < ρ) (hτ : 0 < τ) :
    ∃ n₀ : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
      (G : SimpleGraph V) [DecidableRel G.Adj], n₀ ≤ Fintype.card V →
      ∀ k : ℕ, HasPackingNumberAtMost r G k →
      ∃ U : Kernel ℝ,
        dist (finiteGraphon G) (Vendor.GraphonSpace.mk (U.toVendorGraphon unitMeasure)) < ρ ∧
        tilingNumber r U unitMeasure ≤ (k : ℝ)/Fintype.card V+τ := by
  obtain ⟨n₀,hmodel⟩ := exists_regular_kernel_model.{0,u} (Ω := ℝ) hr hρ hτ
  refine ⟨n₀,?_⟩
  intro V instV instDecV instNonempty G instAdj hn k hpack
  letI : MeasurableSpace V := ⊤
  haveI : MeasurableSingletonClass V := ⟨fun _ => trivial⟩
  obtain ⟨U,hcut,htil⟩ := hmodel G hn unitMeasure (intervalLabel (uniformWeight V))
    (measurable_intervalLabel _) (intervalLabel_mass uniformWeight_probability)
    (finiteGraphKernel G) (finiteGraphKernel_apply G) k hpack
  refine ⟨U,?_,htil⟩
  change Vendor.Graphon.cutDistance ((finiteGraphKernel G).toVendorGraphon unitMeasure)
    (U.toVendorGraphon unitMeasure) < ρ
  apply (Vendor.Graphon.cutDistance_le_cutNormDiff _ _).trans_lt
  rwa [cutNormDiff_toVendorGraphon]

/-- The actual finite-to-graphon transference inequality for convergent
normalized integral packing bounds. No fractional packing bound is assumed
for the finite graphs themselves. -/
theorem finite_graphon_tiling_transference {r : ℕ} (hr : 3 ≤ r)
    {V : ℕ → Type u} [∀ j, Fintype (V j)] [∀ j, DecidableEq (V j)]
    [∀ j, Nonempty (V j)] (G : ∀ j, SimpleGraph (V j))
    [∀ j, DecidableRel (G j).Adj] (k : ℕ → ℕ)
    (hpack : ∀ j, HasPackingNumberAtMost r (G j) (k j))
    (horder : Tendsto (fun j => Fintype.card (V j)) atTop atTop)
    {W : Vendor.GraphonSpace ℝ unitMeasure} {x : ℝ}
    (hgraph : Tendsto (fun j => finiteGraphon (G j)) atTop (𝓝 W))
    (hparameter : Tendsto (fun j => (k j : ℝ)/Fintype.card (V j)) atTop (𝓝 x)) :
    graphonSpaceTilingNumber unitMeasure r (by omega) W ≤ x := by
  by_contra! hbad
  let a : ℝ := (x+graphonSpaceTilingNumber unitMeasure r (by omega) W)/2
  have hxa : x < a := by dsimp [a]; linarith
  have ha : a < graphonSpaceTilingNumber unitMeasure r (by omega) W := by
    dsimp [a]; linarith
  obtain ⟨δ,hδ,hnear⟩ := Metric.eventually_nhds_iff.mp
    (lowerSemicontinuous_graphonSpaceTilingNumber unitMeasure (by omega : 0 < r) W a ha)
  let τ := (a-x)/4
  have hτ : 0 < τ := by dsimp [τ]; linarith
  obtain ⟨n₀,hmodel⟩ := exists_finiteGraphon_model.{u} hr (half_pos hδ) hτ
  have hn : ∀ᶠ j in atTop, n₀ ≤ Fintype.card (V j) :=
    horder.eventually (eventually_ge_atTop n₀)
  have hd : ∀ᶠ j in atTop, dist (finiteGraphon (G j)) W < δ/2 :=
    Metric.tendsto_nhds.mp hgraph _ (half_pos hδ)
  have hx : ∀ᶠ j in atTop, (k j : ℝ)/Fintype.card (V j) < x+τ :=
    hparameter.eventually_lt_const (by linarith)
  obtain ⟨j,hjn,hjd,hjx⟩ := (hn.and (hd.and hx)).exists
  obtain ⟨U,hU,htil⟩ := hmodel (G j) hjn (k j) (hpack j)
  let Uq := Vendor.GraphonSpace.mk (U.toVendorGraphon unitMeasure)
  have hdist : dist Uq W < δ := by
    calc
      dist Uq W ≤ dist Uq (finiteGraphon (G j))+dist (finiteGraphon (G j)) W :=
        dist_triangle _ _ _
      _ = dist (finiteGraphon (G j)) Uq+dist (finiteGraphon (G j)) W := by
        rw [dist_comm Uq (finiteGraphon (G j))]
      _ < δ := by dsimp [Uq]; linarith
  have hlower := hnear hdist
  change a < graphonSpaceTilingNumber unitMeasure r (by omega) Uq at hlower
  rw [graphonSpaceTilingNumber_kernel] at hlower
  dsimp [τ] at htil hjx
  linarith

end DensityHS.Graphon
