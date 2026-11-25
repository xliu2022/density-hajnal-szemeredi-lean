module

public import DensityHS.Stability.ConstructionRounding
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Sequences

/-!
# The finite stability compactness implication

Author and maintainer: Xizhi Liu.

This intermediate theorem isolates the equality-classification input.
All finite-to-graphon transference and the exact integer edit rounding are
the concrete proved theorems, and are not hypotheses of the implication.
-/

@[expose] public section

namespace DensityHS.Stability

open MeasureTheory Filter Set Finset Graphon Constructions
open scoped Topology

attribute [local instance] Classical.propDecidable

theorem graphonSpaceTilingNumber_nonneg {r : ℕ} (hr : 0 < r)
    (W : Vendor.GraphonSpace ℝ unitMeasure) :
    0 ≤ graphonSpaceTilingNumber unitMeasure r hr W := by
  obtain ⟨U, rfl⟩ := Vendor.GraphonSpace.surjective_mk W
  exact tilingNumber_nonneg _ _ _ hr

theorem graphon_density_le_Phi_of_tiling_le {r : ℕ} (hr : 3 ≤ r)
    {x : ℝ} (hx : x ∈ Icc 0 (1/(r : ℝ))) (W : Vendor.GraphonSpace ℝ unitMeasure)
    (ht : graphonSpaceTilingNumber unitMeasure r (by omega) W ≤ x) :
    graphonSpaceDensity unitMeasure W ≤ Phi r x := by
  apply (graphonSpace_density_bound unitMeasure (by omega : 2 ≤ r) W).trans
  exact Phi_monotoneOn hr ⟨graphonSpaceTilingNumber_nonneg (by omega) W, ht.trans hx.2⟩ hx ht

/-- Equality classification plus local approximation at the original
parameter implies the finite stability theorem. The final application
supplies these two inputs from the concrete graphon classification. -/
theorem finite_stability_of_classification {r : ℕ} (hr : 3 ≤ r)
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
    ∃ δ > 0, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ k : ℕ, r*k ≤ n →
      ∀ G : SimpleGraph (Fin n), HasPackingNumberAtMost r G k →
      (Phi r ((k : ℝ)/n)-δ)*(n : ℝ)^2 ≤ (G.edgeFinset.card : ℝ) →
      ∃ H : SimpleGraph (Fin n), H ∈ nearActiveFiniteFamily r k η ∧
        (editDistance G H : ℝ) < ε*(n : ℝ)^2 := by
  classical
  by_contra! hbad
  have hcounter : ∀ j : ℕ, ∃ n : ℕ, j+1 ≤ n ∧ ∃ k : ℕ, r*k ≤ n ∧
      ∃ G : SimpleGraph (Fin n), HasPackingNumberAtMost r G k ∧
        (Phi r ((k : ℝ)/n)-1/((j : ℝ)+1))*(n : ℝ)^2 ≤ (G.edgeFinset.card : ℝ) ∧
        ∀ H : SimpleGraph (Fin n), H ∈ nearActiveFiniteFamily r k η →
          ε*(n : ℝ)^2 ≤ (editDistance G H : ℝ) := by
    intro j
    exact hbad (1/((j : ℝ)+1)) (by positivity) (j+1)
  choose n hn k hk G hpack hlow hfar using hcounter
  have hnpos (j : ℕ) : 0 < n j := by have := hn j; omega
  letI : ∀ j : ℕ, Nonempty (Fin (n j)) := fun j => ⟨⟨0, hnpos j⟩⟩
  let x : ℕ → ℝ := fun j => (k j : ℝ)/n j
  have hx (j : ℕ) : x j ∈ Icc 0 (1/(r : ℝ)) := by
    have hnr : (0 : ℝ) < n j := by exact_mod_cast hnpos j
    have hrr : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
    refine ⟨by dsimp [x]; positivity, ?_⟩
    apply (div_le_div_iff₀ hnr hrr).mpr
    have h : (r : ℝ)*k j ≤ n j := by exact_mod_cast hk j
    simpa only [mul_comm, one_mul, mul_one] using h
  let Z := Vendor.GraphonSpace ℝ unitMeasure
  let sequence : ℕ → ℝ × Z := fun j => (x j, finiteGraphon (G j))
  have hcompact : IsCompact ((Icc (0 : ℝ) (1/(r : ℝ))) ×ˢ (Set.univ : Set Z)) :=
    isCompact_Icc.prod isCompact_univ
  obtain ⟨p, hp, f, hf, hconv⟩ := hcompact.tendsto_subseq (fun j => ⟨hx j, trivial⟩)
    (x := sequence)
  have hxlim : Tendsto (fun j => x (f j)) atTop (𝓝 p.1) := continuous_fst.tendsto p |>.comp hconv
  have hWlim : Tendsto (fun j => finiteGraphon (G (f j))) atTop (𝓝 p.2) :=
    continuous_snd.tendsto p |>.comp hconv
  have hnlim : Tendsto (fun j => n (f j)) atTop atTop :=
    (Filter.tendsto_atTop_mono (fun j => (Nat.le_succ j).trans (hn j)) tendsto_id).comp hf.tendsto_atTop
  have htil : graphonSpaceTilingNumber unitMeasure r (by omega) p.2 ≤ p.1 := by
    apply finite_graphon_tiling_transference hr (fun j => G (f j)) (fun j => k (f j))
      (fun j => hpack (f j)) _ hWlim
    · simpa only [x, Fintype.card_fin] using hxlim
    · simpa only [Fintype.card_fin] using hnlim
  have hφlim : Tendsto (fun j => Phi r (x (f j))) atTop (𝓝 (Phi r p.1)) := by
    have heq : (fun j => Phi r (x (f j))) = fun j => continuousEnvelope r (x (f j)) :=
      funext (fun j => Phi_eq_continuousEnvelope hr (hx (f j)))
    rw [heq, Phi_eq_continuousEnvelope hr hp.1]
    exact (continuous_continuousEnvelope r).tendsto p.1 |>.comp hxlim
  have helim : Tendsto (fun j => graphonSpaceDensity unitMeasure (finiteGraphon (G (f j))))
      atTop (𝓝 (graphonSpaceDensity unitMeasure p.2)) :=
    (continuous_graphonSpaceDensity unitMeasure).tendsto p.2 |>.comp hWlim
  have hδlim : Tendsto (fun j => 1/((f j : ℝ)+1)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hf.tendsto_atTop
  have hlower : Phi r p.1 ≤ graphonSpaceDensity unitMeasure p.2 := by
    apply le_of_tendsto_of_tendsto (by simpa only [sub_zero] using hφlim.sub hδlim) helim
    apply Eventually.of_forall
    intro j
    change Phi r (x (f j))-1/((f j : ℝ)+1) ≤
      graphonSpaceDensity unitMeasure (finiteGraphon (G (f j)))
    rw [density_finiteGraphon (G (f j)), Fintype.card_fin]
    apply (le_div_iff₀ (sq_pos_of_pos (show (0 : ℝ) < n (f j) by exact_mod_cast hnpos (f j)))).mpr
    exact hlow (f j)
  have he : graphonSpaceDensity unitMeasure p.2 = Phi r p.1 :=
    le_antisymm (graphon_density_le_Phi_of_tiling_le hr hp.1 p.2 htil) hlower
  have hactive := hclassification p.1 hp.1 p.2 htil he
  obtain ⟨ρ, hρ, N, hround⟩ := finite_construction_edit_rounding hr hε
  obtain ⟨a, ha, hlocal⟩ := happrox p.1 hp.1 p.2 hactive (ρ/2) η (half_pos hρ) hη
  have hnx : ∀ᶠ j in atTop, |x (f j)-p.1| < a := by
    simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp hxlim a ha
  have hnW : ∀ᶠ j in atTop, dist (finiteGraphon (G (f j))) p.2 < ρ/2 :=
    Metric.tendsto_nhds.mp hWlim _ (half_pos hρ)
  have hnN : ∀ᶠ j in atTop, N ≤ n (f j) := hnlim.eventually (eventually_ge_atTop N)
  obtain ⟨j, hjx, hjW, hjN⟩ := (hnx.and (hnW.and hnN)).exists
  obtain ⟨U, hU, hdistU⟩ := hlocal (x (f j)) (hx (f j)) hjx
  obtain ⟨t, z, _, hz, hd, hnear, hmodel⟩ := (mem_nearActiveGraph_iff hr).mp hU
  have hdist : dist (finiteGraphon (G (f j))) (constructionGraphon r t (x (f j),z)) < ρ := by
    rw [← hmodel]
    exact (dist_triangle _ p.2 _).trans_lt (by linarith)
  obtain ⟨H, hH, hEdit⟩ := hround (G (f j)) (by simpa using hjN)
    (k (f j)) (by simpa using hk (f j)) t z hz (by simpa only [Fintype.card_fin] using hd)
    (by simpa only [Fintype.card_fin] using hdist)
  have hHnear : H ∈ nearActiveFiniteFamily r (k (f j)) η :=
    ⟨t, by simpa only [Fintype.card_fin] using hd,
      by simpa only [Fintype.card_fin] using hnear, hH⟩
  have hcontr := hfar (f j) H hHnear
  simp only [Fintype.card_fin] at hEdit
  exact (not_lt_of_ge hcontr) hEdit

end DensityHS.Stability
