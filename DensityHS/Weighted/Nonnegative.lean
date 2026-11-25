module

public import DensityHS.Basic.Restriction
public import DensityHS.Weighted.Clique

/-!
# Density bounds with zero vertex weights

Author and maintainer: Xizhi Liu.
The compact optimization domains used later include zero coordinates. Exact
restriction to the positive support extends the already proved density bounds.
-/

@[expose] public section

namespace DensityHS

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

/-- The matching base case for an arbitrary nonnegative probability vector. -/
theorem weighted_matching_cover_bound_nonneg {G : SimpleGraph V} {p c : V → ℝ}
    (hp : IsProbabilityWeight p) (hc : IsCliqueCover 2 G c)
    (hcost : coverCost p c ≤ 1 / 2) :
    edgeMass G p ≤ Phi 2 (coverCost p c) := by
  classical
  have hcost' : coverCost (fun v : PositiveSupport p => p v)
      (fun v : PositiveSupport p => c v) ≤ 1 / 2 := by
    rwa [coverCost_positiveSupport hp.1]
  have hc' : IsCliqueCover 2 (G.induce {v | 0 < p v})
      (fun v : PositiveSupport p => c v) := hc.restrict {v | 0 < p v}
  have h := weighted_matching_cover_bound (V := PositiveSupport p)
    (probabilityWeight_positiveSupport hp) (fun v => v.property)
    hc' hcost'
  simpa only [coverCost_positiveSupport hp.1, edgeMass_positiveSupport hp.1] using h

/-- The complete-support case for an arbitrary nonnegative probability vector. -/
theorem weighted_complete_cover_bound_nonneg {r : ℕ} (hr : 2 ≤ r)
    {p c : V → ℝ} (hp : IsProbabilityWeight p)
    (hc : IsCliqueCover r (⊤ : SimpleGraph V) c)
    (hcost : coverCost p c ≤ 1 / (r : ℝ)) :
    edgeMass (⊤ : SimpleGraph V) p ≤ Phi r (coverCost p c) := by
  classical
  have hcost' : coverCost (fun v : PositiveSupport p => p v)
      (fun v : PositiveSupport p => c v) ≤ 1 / (r : ℝ) := by
    rwa [coverCost_positiveSupport hp.1]
  have hc' : IsCliqueCover r (⊤ : SimpleGraph (PositiveSupport p))
      (fun v : PositiveSupport p => c v) := by
    have hci : IsCliqueCover r ((⊤ : SimpleGraph V).induce {v | 0 < p v})
        (fun v : PositiveSupport p => c v) := hc.restrict {v | 0 < p v}
    simpa only [SimpleGraph.induce_top] using hci
  have h := weighted_complete_cover_bound hr
    (probabilityWeight_positiveSupport hp) (fun v => v.property) hc' hcost'
  have he : edgeMass (⊤ : SimpleGraph (PositiveSupport p))
      (fun v : PositiveSupport p => p v) = edgeMass (⊤ : SimpleGraph V) p := by
    simpa using edgeMass_positiveSupport hp.1 (⊤ : SimpleGraph V)
  simpa only [coverCost_positiveSupport hp.1, he] using h

end DensityHS
