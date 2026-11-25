module

public import DensityHS.Basic.Envelope
public import DensityHS.Weighted.CoverPerturbation

/-!
# The weighted matching base case

Author and maintainer: Xizhi Liu.

Extreme fractional vertex covers are half-integral.  Their three cover levels
give the two-branch weighted Erdős--Gallai bound directly, without using an
integral matching theorem or a rational blow-up approximation.
-/

@[expose] public section

namespace DensityHS

open Finset Set

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

/-- Opposite shifts on complementary cover levels. -/
noncomputable def matchingLevelDirection (c : V → ℝ) (a : ℝ) (v : V) : ℝ := by
  classical
  exact if c v = a then 1 else if c v = 1 - a then -1 else 0

omit [Fintype V] in
theorem matchingLevelDirection_tight {c : V → ℝ} {a : ℝ} {u v : V}
    (ha : a ≠ 1 / 2) (huv : c u + c v = 1) :
    matchingLevelDirection c a u + matchingLevelDirection c a v = 0 := by
  classical
  have hac : 1 - a ≠ a := by intro h; apply ha; linarith
  by_cases hu : c u = a
  · have hv : c v = 1 - a := by linarith
    simp [matchingLevelDirection, hu, hv, hac]
  by_cases hv : c v = a
  · have hu' : c u = 1 - a := by linarith
    simp [matchingLevelDirection, hu', hv, hac]
  have hu' : c u ≠ 1 - a := by intro h; apply hv; linarith
  have hv' : c v ≠ 1 - a := by intro h; apply hu; linarith
  simp [matchingLevelDirection, hu, hu', hv, hv']

/-- Every extreme point of the fractional vertex-cover polyhedron has only
the coordinates `0`, `1/2`, and `1`. -/
theorem extreme_matching_cover_half_integral {G : SimpleGraph V} {c : V → ℝ}
    (hc : c ∈ ({d | IsCliqueCover 2 G d} : Set (V → ℝ)).extremePoints ℝ) :
    ∀ v, c v = 0 ∨ c v = 1 / 2 ∨ c v = 1 := by
  classical
  intro v
  by_contra h
  have h0 : c v ≠ 0 := fun h0 => h (Or.inl h0)
  have hh : c v ≠ 1 / 2 := fun hh => h (Or.inr (Or.inl hh))
  have h1 : c v ≠ 1 := fun h1 => h (Or.inr (Or.inr h1))
  let z := matchingLevelDirection c (c v)
  have hz0 : ∀ w, c w = 0 → z w = 0 := by
    intro w hw
    have hn : (0 : ℝ) ≠ 1 - c v := by intro he; apply h1; linarith
    simp [z, matchingLevelDirection, hw, Ne.symm h0, hn]
  have hzt : ∀ K : Finset V, G.IsNClique 2 K →
      (∑ w ∈ K, c w) = 1 → (∑ w ∈ K, z w) = 0 := by
    intro K hK hsum
    obtain ⟨u, w, huw, rfl⟩ := Finset.card_eq_two.mp hK.card_eq
    simp only [Finset.sum_pair huw] at hsum ⊢
    exact matchingLevelDirection_tight hh hsum
  have heq : z = 0 := extreme_cover_direction_eq_zero hc hz0 hzt
  have hv := congrFun heq v
  simp [z, matchingLevelDirection] at hv

omit [Fintype V] in
/-- The clique-cover formulation specializes to the familiar edge inequality. -/
theorem IsCliqueCover.edge_le {G : SimpleGraph V} {c : V → ℝ}
    (hc : IsCliqueCover 2 G c) {u v : V} (huv : G.Adj u v) :
    1 ≤ c u + c v := by
  classical
  have hne : u ≠ v := huv.ne
  have hclique : G.IsNClique 2 ({u, v} : Finset V) := by
    rw [SimpleGraph.isNClique_iff]
    constructor
    · simpa [hne] using huv
    · simp [hne]
  simpa [Finset.sum_pair hne] using hc.2 {u, v} hclique

/-- Total vertex weight on one fixed cover level. -/
noncomputable def coverLevelMass (p c : V → ℝ) (a : ℝ) : ℝ := by
  classical
  exact ∑ v, if c v = a then p v else 0

theorem coverLevelMass_nonneg {p c : V → ℝ} (hp : ∀ v, 0 ≤ p v) (a : ℝ) :
    0 ≤ coverLevelMass p c a := by
  classical
  apply Finset.sum_nonneg
  intro v _
  split_ifs
  · exact hp v
  · exact le_rfl

theorem halfIntegral_coverCost {p c : V → ℝ}
    (hh : ∀ v, c v = 0 ∨ c v = 1 / 2 ∨ c v = 1) :
    coverCost p c = coverLevelMass p c 1 + coverLevelMass p c (1 / 2) / 2 := by
  classical
  calc
    coverCost p c = ∑ v, ((if c v = 1 then p v else 0) +
        (if c v = 1 / 2 then p v else 0) / 2) := by
      apply Finset.sum_congr rfl
      intro v _
      rcases hh v with h | h | h <;> simp [h] <;> ring
    _ = _ := by simp [coverLevelMass, Finset.sum_add_distrib, Finset.sum_div]

/-- An edge can only join a level-one vertex to any vertex, or two
level-one-half vertices. This gives a pointwise bound before summing. -/
theorem halfIntegral_edge_term_bound {G : SimpleGraph V} {p c : V → ℝ}
    (hp : ∀ v, 0 ≤ p v) (hc : IsCliqueCover 2 G c)
    (hh : ∀ v, c v = 0 ∨ c v = 1 / 2 ∨ c v = 1) (u v : V) :
    (if G.Adj u v then p u * p v else 0) ≤
      (if c u = 1 then p u else 0) * p v +
      p u * (if c v = 1 then p v else 0) -
      (if c u = 1 then p u else 0) * (if c v = 1 then p v else 0) +
      (if c u = 1 / 2 then p u else 0) *
        (if c v = 1 / 2 then p v else 0) := by
  classical
  have hpq := mul_nonneg (hp u) (hp v)
  by_cases ha : G.Adj u v
  · have hedge := hc.edge_le ha
    rcases hh u with hu | hu | hu <;>
      rcases hh v with hv | hv | hv <;>
      norm_num [hu, hv] at hedge <;> norm_num [ha, hu, hv]
  · rcases hh u with hu | hu | hu <;>
      rcases hh v with hv | hv | hv <;>
      norm_num [ha, hu, hv] <;> linarith

/-- The edge bound arising from the three half-integral cover classes. -/
theorem edgeMass_le_halfIntegral {G : SimpleGraph V} {p c : V → ℝ}
    (hp : IsProbabilityWeight p) (hc : IsCliqueCover 2 G c)
    (hh : ∀ v, c v = 0 ∨ c v = 1 / 2 ∨ c v = 1) :
    edgeMass G p ≤ coverLevelMass p c 1 - (coverLevelMass p c 1) ^ 2 / 2 +
      (coverLevelMass p c (1 / 2)) ^ 2 / 2 := by
  classical
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun u _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun v _ =>
      halfIntegral_edge_term_bound hp.1 hc hh u v))
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul, hp.2, mul_one, one_mul] at hsum
  unfold edgeMass coverLevelMass
  nlinarith

/-- The matching density inequality for any half-integral fractional cover. -/
theorem halfIntegral_matching_bound {G : SimpleGraph V} {p c : V → ℝ}
    (hp : IsProbabilityWeight p) (hc : IsCliqueCover 2 G c)
    (hh : ∀ v, c v = 0 ∨ c v = 1 / 2 ∨ c v = 1) :
    edgeMass G p ≤ Phi2 (coverCost p c) := by
  have hcost := halfIntegral_coverCost (p := p) hh
  have ha := coverLevelMass_nonneg (c := c) hp.1 1
  have hb := coverLevelMass_nonneg (c := c) hp.1 (1 / 2)
  have hax : coverLevelMass p c 1 ≤ coverCost p c := by linarith
  have hquadratic := matching_mass_bound ha hax
  have he := edgeMass_le_halfIntegral hp hc hh
  have hmass : 2 * (coverCost p c - coverLevelMass p c 1) =
      coverLevelMass p c (1 / 2) := by linarith
  rw [hmass] at hquadratic
  exact he.trans hquadratic

/-- The full weighted matching base case, expressed using an arbitrary cover.
Positive vertex weights are the support convention in the manuscript. -/
theorem weighted_matching_cover_bound {G : SimpleGraph V} {p c : V → ℝ}
    (hp : IsProbabilityWeight p) (hpos : ∀ v, 0 < p v)
    (hc : IsCliqueCover 2 G c) (hcost : coverCost p c ≤ 1 / 2) :
    edgeMass G p ≤ Phi 2 (coverCost p c) := by
  obtain ⟨d, hd, hext⟩ := exists_extreme_optimal_cover 2 G (by norm_num) p hpos
  have hh := extreme_matching_cover_half_integral hext
  have hedge := halfIntegral_matching_bound hp hd.1 hh
  have hnonnegd := coverCost_nonneg hp.1 hd.1.1
  have hnonnegc := coverCost_nonneg hp.1 hc.1
  have hdc : coverCost p d ≤ coverCost p c := hd.2 c hc
  have hmon := Phi2_monotoneOn
    (show coverCost p d ∈ Set.Icc (0 : ℝ) (1 / 2) from
      ⟨hnonnegd, hdc.trans hcost⟩)
    (show coverCost p c ∈ Set.Icc (0 : ℝ) (1 / 2) from ⟨hnonnegc, hcost⟩) hdc
  simpa using hedge.trans hmon

end DensityHS
