module

public import DensityHS.Weighted.CoverMass
public import DensityHS.Weighted.SupportCertificates
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix

/-!+# Weight variations at a support-minimal maximum

Author and maintainer: Xizhi Liu.

The hypotheses in this file are explicit finite optimization properties. The
quadratic conclusion is proved by feasible perturbations and by moving a flat
direction to the boundary of the probability simplex.
-/

@[expose] public section

namespace DensityHS

open Finset Filter
open scoped Topology BigOperators

variable {V : Type*} [Fintype V]

/-- The bilinear adjacency pairing, with each orientation counted. -/
noncomputable def edgePair (G : SimpleGraph V) (p q : V → ℝ) : ℝ := by
  classical
  exact ∑ u, ∑ v, if G.Adj u v then p u * q v else 0

theorem edgeMass_eq_edgePair (G : SimpleGraph V) (p : V → ℝ) :
    edgeMass G p = edgePair G p p / 2 := rfl

theorem edgePair_comm (G : SimpleGraph V) (p q : V → ℝ) :
    edgePair G p q = edgePair G q p := by
  classical
  unfold edgePair
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  simp only [G.adj_comm, mul_comm]

theorem edgePair_neg_right (G : SimpleGraph V) (p z : V → ℝ) :
    edgePair G p (-z) = -edgePair G p z := by
  classical
  simp only [edgePair, Pi.neg_apply, mul_neg, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  split_ifs <;> simp

theorem edgeMass_affine (G : SimpleGraph V) (p z : V → ℝ) (t : ℝ) :
    edgeMass G (fun v => p v + t * z v) =
      edgeMass G p + t * edgePair G p z + t ^ 2 * edgeMass G z := by
  classical
  have hterm (u v : V) :
      (if G.Adj u v then (p u + t * z u) * (p v + t * z v) else 0) =
      (if G.Adj u v then p u * p v else 0) +
      t * (if G.Adj u v then p u * z v else 0) +
      t * (if G.Adj u v then z u * p v else 0) +
      t ^ 2 * (if G.Adj u v then z u * z v else 0) := by
    split_ifs <;> ring
  unfold edgeMass
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  change (edgePair G p p + t * edgePair G p z + t * edgePair G z p +
      t ^ 2 * edgePair G z z) / 2 = _
  rw [edgePair_comm G z p]
  unfold edgePair
  ring

theorem probability_affine {p z : V → ℝ} (hp : IsProbabilityWeight p)
    (hz : ∑ v, z v = 0) (t : ℝ) (hnn : ∀ v, 0 ≤ p v + t * z v) :
    IsProbabilityWeight (fun v => p v + t * z v) := by
  refine ⟨hnn, ?_⟩
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hp.2, hz, mul_zero, add_zero]

theorem coverCost_affine_left (p z c : V → ℝ) (t : ℝ) :
    coverCost (fun v => p v + t * z v) c =
      coverCost p c + t * coverCost z c := by
  simp only [coverCost, add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Maximal density among all weights with a fixed cover and cost budget. -/
def IsWeightMaximum (G : SimpleGraph V) (c : V → ℝ) (x : ℝ) (p : V → ℝ) : Prop :=
  ∀ q, IsProbabilityWeight q → coverCost q c ≤ x → edgeMass G q ≤ edgeMass G p

/-- Minimal support on the present positive support: no feasible point of at
least the same density lies on the boundary of this simplex. -/
def HasMinimalPositiveSupport (G : SimpleGraph V) (c : V → ℝ)
    (x : ℝ) (p : V → ℝ) : Prop :=
  ∀ q, IsProbabilityWeight q → coverCost q c ≤ x → edgeMass G p ≤ edgeMass G q →
    ∀ v, 0 < q v

/-- Every feasible one-sided direction has nonpositive first variation. -/
theorem weightMaximum_direction_nonpos {G : SimpleGraph V} {p c z : V → ℝ}
    {x : ℝ} (hp : IsProbabilityWeight p) (hpos : ∀ v, 0 < p v)
    (hbudget : coverCost p c ≤ x) (hmax : IsWeightMaximum G c x p)
    (hsum : ∑ v, z v = 0) (hcost : coverCost z c ≤ 0) :
    edgePair G p z ≤ 0 := by
  by_contra hn
  have hlin : 0 < edgePair G p z := lt_of_not_ge hn
  have hnn := nonnegative_perturbation_eventually hp.1
    (z := z) (fun v hv => False.elim ((ne_of_gt (hpos v)) hv))
  have htend : Tendsto (fun t : ℝ => edgePair G p z + t * edgeMass G z)
      (𝓝 0) (𝓝 (edgePair G p z)) := by
    convert (show Continuous (fun t : ℝ => edgePair G p z + t * edgeMass G z)
      by fun_prop).tendsto 0 using 1 <;> simp
  have hgood := htend.eventually_const_lt hlin
  have hall := (hnn.and hgood).filter_mono
    (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have hpositive : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht, hnt, hgt⟩ := Filter.Eventually.exists
    (Filter.Eventually.and hpositive hall)
  have hfeas : coverCost (fun v => p v + t * z v) c ≤ x := by
    rw [coverCost_affine_left]
    have hm := mul_nonpos_of_nonneg_of_nonpos ht.le hcost
    linarith
  have hm := hmax _ (probability_affine hp hsum t hnt) hfeas
  rw [edgeMass_affine] at hm
  have hstrict := mul_pos ht hgt
  nlinarith

/-- The first variation vanishes on the mass and cover-cost tangent space. -/
theorem weightMaximum_direction_eq_zero {G : SimpleGraph V} {p c z : V → ℝ}
    {x : ℝ} (hp : IsProbabilityWeight p) (hpos : ∀ v, 0 < p v)
    (hbudget : coverCost p c ≤ x) (hmax : IsWeightMaximum G c x p)
    (hsum : ∑ v, z v = 0) (hcost : coverCost z c = 0) :
    edgePair G p z = 0 := by
  have hle := weightMaximum_direction_nonpos hp hpos hbudget hmax hsum hcost.le
  have hsn : ∑ v, (-z) v = 0 := by simp [hsum]
  have hcn : coverCost (-z) c = 0 := by
    simp only [coverCost, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
    exact neg_eq_zero.mpr hcost
  have hge := weightMaximum_direction_nonpos hp hpos hbudget hmax hsn hcn.le
  rw [edgePair_neg_right] at hge
  linarith

/-- A nonzero zero-sum direction reaches the boundary of the simplex. -/
theorem exists_affine_boundary {p z : V → ℝ}
    (hpos : ∀ v, 0 < p v) (hz : z ≠ 0) (hsum : ∑ v, z v = 0) :
    ∃ t : ℝ, 0 < t ∧ (∀ v, 0 ≤ p v + t * z v) ∧
      ∃ v, p v + t * z v = 0 := by
  classical
  have hneg : ∃ v, z v < 0 := by
    by_contra hn
    push Not at hn
    have hall : ∀ v, z v = 0 := by
      intro v
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hn i)).mp hsum v
        (Finset.mem_univ v)
    exact hz (funext hall)
  let S : Finset V := Finset.univ.filter (fun v => z v < 0)
  have hS : S.Nonempty := by
    obtain ⟨v, hv⟩ := hneg
    exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩⟩
  obtain ⟨v, hv, hmin⟩ := S.exists_min_image (fun v => p v / (-z v)) hS
  have hvn : z v < 0 := (Finset.mem_filter.mp hv).2
  let t : ℝ := p v / (-z v)
  have ht : 0 < t := div_pos (hpos v) (neg_pos.mpr hvn)
  refine ⟨t, ht, ?_, v, ?_⟩
  · intro w
    by_cases hw : z w < 0
    · have htw : t ≤ p w / (-z w) := hmin w (by simp [S, hw])
      have hm := (le_div_iff₀ (neg_pos.mpr hw)).mp htw
      nlinarith
    · exact add_nonneg (hpos w).le (mul_nonneg ht.le (le_of_not_gt hw))
  · dsimp [t]
    field_simp [ne_of_lt hvn]
    <;> ring

/-- The quadratic form is strictly negative on the two-kernel tangent space.
The flat case is excluded by an actual boundary point of equal density. -/
theorem minimal_weightMaximum_quadratic_negative
    {G : SimpleGraph V} {p c : V → ℝ} {x : ℝ}
    (hp : IsProbabilityWeight p) (hpos : ∀ v, 0 < p v)
    (hbudget : coverCost p c ≤ x) (hmax : IsWeightMaximum G c x p)
    (hminimal : HasMinimalPositiveSupport G c x p)
    {z : V → ℝ} (hz : z ≠ 0) (hsum : ∑ v, z v = 0)
    (hcost : coverCost z c = 0) : edgeMass G z < 0 := by
  have hlin := weightMaximum_direction_eq_zero hp hpos hbudget hmax hsum hcost
  obtain ⟨t, ht, hnn, v, hv⟩ := exists_affine_boundary hpos hz hsum
  have hpq := probability_affine hp hsum t hnn
  have hcq : coverCost (fun v => p v + t * z v) c ≤ x := by
    rw [coverCost_affine_left, hcost, mul_zero, add_zero]
    exact hbudget
  have heq := edgeMass_affine G p z t
  rw [hlin, mul_zero, add_zero] at heq
  have hm := hmax _ hpq hcq
  have hnonpos : edgeMass G z ≤ 0 := by
    have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
    nlinarith
  by_contra hn
  have hzero : edgeMass G z = 0 := le_antisymm hnonpos (le_of_not_gt hn)
  rw [hzero, mul_zero, add_zero] at heq
  have hstrict := hminimal _ hpq hcq heq.ge v
  rw [hv] at hstrict
  exact lt_irrefl 0 hstrict

theorem edgeMass_eq_adjacency_quadratic (G : SimpleGraph V)
    [DecidableRel G.Adj] (z : V → ℝ) :
    2 * edgeMass G z = Weighted.Support.quadratic (G.adjMatrix ℝ) z := by
  classical
  unfold edgeMass Weighted.Support.quadratic
  have hh : (∑ i, ∑ j, if G.Adj i j then z i * z j else 0) =
      ∑ i, ∑ j, z i * G.adjMatrix ℝ i j * z j := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : G.Adj i j <;> simp [SimpleGraph.adjMatrix_apply, h]
  rw [← hh]
  ring

/-- The exact tangent-space hypothesis used by support classification. -/
theorem minimal_weightMaximum_negativeOnTwoKernels
    {G : SimpleGraph V} [DecidableRel G.Adj] {p c : V → ℝ} {x : ℝ}
    (hp : IsProbabilityWeight p) (hpos : ∀ v, 0 < p v)
    (hbudget : coverCost p c ≤ x) (hmax : IsWeightMaximum G c x p)
    (hminimal : HasMinimalPositiveSupport G c x p) :
    Weighted.Support.NegativeOnTwoKernels
      (Weighted.Support.quadratic (G.adjMatrix ℝ))
      Weighted.Support.totalFunctional (Weighted.Support.costFunctional c) := by
  intro z hz hsum hcost
  have h := minimal_weightMaximum_quadratic_negative hp hpos hbudget hmax hminimal
    hz hsum hcost
  rw [← edgeMass_eq_adjacency_quadratic]
  linarith

/-- Weighted degree (incoming adjacency, equal to outgoing by symmetry). -/
noncomputable def weightedDegree (G : SimpleGraph V) (p : V → ℝ) (v : V) : ℝ := by
  classical
  exact ∑ u, if G.Adj u v then p u else 0

theorem edgePair_eq_degree_cost (G : SimpleGraph V) (p z : V → ℝ) :
    edgePair G p z = coverCost z (weightedDegree G p) := by
  classical
  unfold edgePair coverCost weightedDegree
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  split_ifs <;> ring

@[simp] theorem coverCost_single_left [DecidableEq V]
    (v : V) (a : ℝ) (c : V → ℝ) :
    coverCost (Pi.single v a) c = a * c v := by
  simp [coverCost, Pi.single_apply, ite_mul]

@[simp] theorem coverCost_add_left (p q c : V → ℝ) :
    coverCost (p + q) c = coverCost p c + coverCost q c := by
  simp [coverCost, add_mul, Finset.sum_add_distrib]

@[simp] theorem coverCost_neg_left (p c : V → ℝ) :
    coverCost (-p) c = -coverCost p c := by
  simp [coverCost, neg_mul, Finset.sum_neg_distrib]

/-- A linear functional nonpositive on the mass-zero, nonpositive-cost cone
is a nonnegative multiple of the cost, up to a constant. This is the elementary
finite-dimensional multiplier argument used by the manuscript. -/
theorem stationary_of_direction_nonpos [Nonempty V] (c g : V → ℝ)
    (hdir : ∀ z : V → ℝ, (∑ v, z v) = 0 → coverCost z c ≤ 0 →
      coverCost z g ≤ 0) :
    ∃ lam μ : ℝ, 0 ≤ μ ∧ ∀ v, g v = lam + μ * c v := by
  classical
  have hz : ∀ z : V → ℝ, (∑ v, z v) = 0 → coverCost z c = 0 →
      coverCost z g = 0 := by
    intro z hs hc
    have h1 := hdir z hs hc.le
    have h2 := hdir (-z) (by simp [hs]) (by simp [hc])
    simp only [coverCost_neg_left] at h2
    linarith
  by_cases hconstant : ∀ u v, c u = c v
  · let a : V := Classical.arbitrary V
    refine ⟨g a, 0, le_rfl, ?_⟩
    intro v
    have h := hz (Pi.single v 1 + Pi.single a (-1))
      (by simp [Finset.sum_add_distrib]) (by simp [hconstant v a])
    simp only [coverCost_add_left, coverCost_single_left, one_mul, neg_one_mul] at h
    simp only [zero_mul, add_zero]
    linarith
  · have hneq : ∃ u v, c u ≠ c v := by simpa only [not_forall] using hconstant
    obtain ⟨u, v, huv⟩ := hneq
    have hlt : ∃ a b, c a < c b := by
      rcases lt_or_gt_of_ne huv with h | h
      · exact ⟨u, v, h⟩
      · exact ⟨v, u, h⟩
    obtain ⟨a, b, hab⟩ := hlt
    have hgb : g a ≤ g b := by
      have h := hdir (Pi.single a 1 + Pi.single b (-1))
        (by simp [Finset.sum_add_distrib]) (by simp; linarith)
      simp only [coverCost_add_left, coverCost_single_left, one_mul, neg_one_mul] at h
      linarith
    let μ := (g b - g a) / (c b - c a)
    refine ⟨g a - μ * c a, μ, div_nonneg (sub_nonneg.mpr hgb)
      (sub_pos.mpr hab).le, ?_⟩
    intro w
    let z : V → ℝ := Pi.single w (c b - c a) + Pi.single a (c w - c b) +
      Pi.single b (c a - c w)
    have hs : ∑ v, z v = 0 := by
      simp [z, Finset.sum_add_distrib]
      <;> ring
    have hc : coverCost z c = 0 := by
      simp only [z, coverCost_add_left, coverCost_single_left]
      ring
    have hg := hz z hs hc
    simp only [z, coverCost_add_left, coverCost_single_left] at hg
    dsimp [μ]
    field_simp [ne_of_gt (sub_pos.mpr hab)]
    nlinarith

/-- First-order stationarity, including the sign of the cover multiplier. -/
theorem weightMaximum_stationary {G : SimpleGraph V} {p c : V → ℝ} {x : ℝ}
    (hp : IsProbabilityWeight p) (hpos : ∀ v, 0 < p v)
    (hbudget : coverCost p c ≤ x) (hmax : IsWeightMaximum G c x p) :
    ∃ lam μ : ℝ, 0 ≤ μ ∧ ∀ v, weightedDegree G p v = lam + μ * c v := by
  have hne : Nonempty V := by
    by_contra h
    haveI : IsEmpty V := not_nonempty_iff.mp h
    have := hp.2
    simp at this
  letI : Nonempty V := hne
  apply stationary_of_direction_nonpos
  intro z hsum hcost
  rw [← edgePair_eq_degree_cost]
  exact weightMaximum_direction_nonpos hp hpos hbudget hmax hsum hcost

end DensityHS
