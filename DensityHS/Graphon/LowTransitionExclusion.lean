module

public import DensityHS.Graphon.LowTransitionAlgebra
public import DensityHS.Graphon.LowTransitionStructure
public import DensityHS.Graphon.StrictTransitionReduction

/-!
# Exclusion of the low and last strict transition multipliers

Author and maintainer: Xizhi Liu.

The witness is the actual finite-uncrossing output of
`exists_uncrossedPeelingWitness`.  The cost cap, zero-set bound, degree
parameter identity, and lower-order density recursion are all derived
from its actual kernel and measure.  The only additional hypotheses are
that the multiplier lies strictly between the native branch derivatives.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory MeasureTheory.Measure Set
open DensityHS.Appendix

variable {Ω : Type*} [MeasurableSpace Ω]

namespace UncrossedPeelingWitness

variable {W : Kernel Ω} {c : Ω → ℝ} {L θ : ℝ}

/-- The exceptional first transition in clique size three is impossible
for every strict interior multiplier. -/
theorem r3_transition_exclusion (T : UncrossedPeelingWitness 3 W c (2 / 9) L θ)
    (hθ0 : 7 / 18 < θ) (hθ1 : θ < 8 / 9) : False := by
  letI := T.invariant.probability
  have hL := affine_degree_peel_parameter T.invariant.cover T.invariant.cost
    T.invariant.extremal T.invariant.degree
  have hb := r3_transition_native_bounds hL hθ0 hθ1
  have hZ : (1 : ℝ) / 3 ≤ T.zeroMass := by
    have h := T.zeroMass_lower (by norm_num : 2 ≤ 3) (by norm_num)
    norm_num at h
    exact h
  have hcap : T.defectCost ≤ (L - 1 / 3) ^ 2 / θ :=
    T.twins.triangle_defect_strong_cap T.invariant.cover hb.1 hb.2.1 hb.2.2.2
      T.invariant.degree T.positive hZ T.defectCost_bound
  have hstrict := r3_native_transition_estimate hL hθ0 hθ1 T.defectCost_range.1 hcap
  have hrec := T.recursion (by norm_num : 3 ≤ 3) (by linarith [hb.2.2.2])
    (by norm_num; linarith [hb.2.2.2])
  exact not_lt_of_ge hrec hstrict

/-- The same conclusion with the actual phase-diagram parameter and
ordinary/exceptional derivative formulas. -/
theorem AStart_three_transition_exclusion
    (T : UncrossedPeelingWitness 3 W c (AStart 3) L θ)
    (hθ0 : (1 - AStart 3) / (3 - 1 : ℝ) < θ)
    (hθ1 : θ < 4 * AStart 3) : False := by
  have hx : AStart 3 = (2 : ℝ) / 9 := by norm_num [AStart]
  have T' : UncrossedPeelingWitness 3 W c (2 / 9) L θ := by simpa only [hx] using T
  apply T'.r3_transition_exclusion
  · norm_num [hx] at hθ0
    exact hθ0
  · norm_num [hx] at hθ1
    exact hθ1

/-- The last ordinary transition in clique size four, including the
actual strong cap and the full rank-three restricted envelope. -/
theorem r4_transition_exclusion
    (T : UncrossedPeelingWitness 4 W c (BCrossing 4 2 3) L θ)
    (hθ0 : 1 - 2 * BCrossing 4 2 3 < θ)
    (hθ1 : θ < 3 * (1 - 3 * BCrossing 4 2 3)) : False := by
  letI := T.invariant.probability
  have hL := affine_degree_peel_parameter T.invariant.cover T.invariant.cost
    T.invariant.extremal T.invariant.degree
  obtain ⟨_, hlow, _, hθ, hell, _⟩ := r4_transition_native_parameters hL hθ0 hθ1
  have hθpos : 0 < θ := hθ ▸ r4Theta_pos hlow
  have hellL : 1 - 4 * BCrossing 4 2 3 ≤ L := by
    rw [hell]
    have hsmall : r4Ell < r4L2 := by
      unfold r4Ell r4L2
      linarith [r4S_bounds.2]
    exact (hsmall.trans hlow).le
  have hx : BCrossing 4 2 3 ∈ Icc 0 (1 / (4 : ℝ)) :=
    ⟨(BCrossing_pos (by norm_num : 0 < 4)).le,
      (BCrossing_lt_right_endpoint (by norm_num : 2 < 4) (by norm_num : 3 < 4)).le⟩
  have hcap := T.defectCost_cap hθpos (T.zeroMass_lower (by norm_num : 2 ≤ 4) hx) hellL
  have hstrict := r4_native_transition_estimate hL hθ0 hθ1 T.defectCost_range.1 hcap
  have hpeel := last_native_peel_bound (by norm_num : 4 ≤ 4) hL
    (by norm_num; exact hθ1)
  exact not_lt_of_ge (T.recursion (by norm_num : 3 ≤ 4) hpeel.2 hpeel.1.le) hstrict

theorem last_transition_exclusion_of_five {r : ℕ} (hr : 5 ≤ r)
    (T : UncrossedPeelingWitness r W c (BCrossing r (r - 2) (r - 1)) L θ)
    (hθ0 : ((r - 2 : ℕ) : ℝ) * (1 - (r - 2 : ℕ) * BCrossing r (r - 2) (r - 1)) /
      ((r : ℝ) - (r - 2 : ℕ)) < θ)
    (hθ1 : θ < ((r - 1 : ℕ) : ℝ) * (1 - (r - 1 : ℕ) * BCrossing r (r - 2) (r - 1)) /
      ((r : ℝ) - (r - 1 : ℕ))) : False := by
  letI := T.invariant.probability
  have hL := affine_degree_peel_parameter T.invariant.cover T.invariant.cost
    T.invariant.extremal T.invariant.degree
  obtain ⟨_, hlow, hhigh, hθ, hell⟩ :=
    last_transition_native_parameters (by omega : 4 ≤ r) hL hθ0 hθ1
  have hd : (3 : ℝ) ≤ (r - 2 : ℕ) := by exact_mod_cast (show 3 ≤ r - 2 by omega)
  have hrange := lastTheta_range hd hlow hhigh
  have hθpos : 0 < θ := hθ ▸ hrange.2.2.2.1
  have hellL : 1 - r * BCrossing r (r - 2) (r - 1) ≤ L := by
    rw [hell]
    exact hrange.2.2.1.le
  have hx : BCrossing r (r - 2) (r - 1) ∈ Icc 0 (1 / (r : ℝ)) :=
    ⟨(BCrossing_pos (by omega : 0 < r)).le,
      (BCrossing_lt_right_endpoint (by omega : r - 2 < r) (by omega : r - 1 < r)).le⟩
  have hcap := T.defectCost_cap hθpos (T.zeroMass_lower (by omega : 2 ≤ r) hx) hellL
  have hstrict := last_native_transition_estimate hr hL hθ0 hθ1 T.defectCost_range.1 hcap
  have hpeel := last_native_peel_bound (by omega : 4 ≤ r) hL hθ1
  exact not_lt_of_ge (T.recursion (by omega : 3 ≤ r) hpeel.2 hpeel.1.le) hstrict

/-- Uniform final-ordinary-crossing exclusion for every clique size at
least four, in exactly the native ordinary-derivative notation. -/
theorem last_transition_exclusion {r : ℕ} (hr : 4 ≤ r)
    (T : UncrossedPeelingWitness r W c (BCrossing r (r - 2) (r - 1)) L θ)
    (hθ0 : ((r - 2 : ℕ) : ℝ) * (1 - (r - 2 : ℕ) * BCrossing r (r - 2) (r - 1)) /
      ((r : ℝ) - (r - 2 : ℕ)) < θ)
    (hθ1 : θ < ((r - 1 : ℕ) : ℝ) * (1 - (r - 1 : ℕ) * BCrossing r (r - 2) (r - 1)) /
      ((r : ℝ) - (r - 1 : ℕ))) : False := by
  by_cases hr4 : r = 4
  · subst r
    apply T.r4_transition_exclusion
    · norm_num at hθ0
      linarith
    · norm_num at hθ1
      exact hθ1
  · exact T.last_transition_exclusion_of_five (by omega) hθ0 hθ1

end UncrossedPeelingWitness

end DensityHS.Graphon
