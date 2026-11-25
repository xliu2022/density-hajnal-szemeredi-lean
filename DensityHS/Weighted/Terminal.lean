module

public import DensityHS.Weighted.UniversalPeeling
public import DensityHS.Weighted.CoverMass
public import DensityHS.Weighted.SupportP3

/-!
# The terminal weighted case without a marked-set extremal theorem

The finite estimates here apply when every zero-cover vertex has all of its
neighbors in a fixed set of `r-2` positive-cover atoms. Cauchy's inequality
on those atoms gives the two marked-set bounds directly.

Author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS

open Finset

attribute [local instance] Classical.propDecidable

theorem marked_quadratic_small {r z b : ℝ} (hr : 2 < r) :
    2 * z - (r - 1) * z ^ 2 ≤ 2 * z - z ^ 2 - 2 * z * b + b ^ 2 / (r - 2) := by
  have hrm2 : r - 2 ≠ 0 := by linarith
  have hid : (2 * z - z ^ 2 - 2 * z * b + b ^ 2 / (r - 2)) -
      (2 * z - (r - 1) * z ^ 2) = (b - (r - 2) * z) ^ 2 / (r - 2) := by
    field_simp
    <;> ring
  have hp : 0 ≤ (b - (r - 2) * z) ^ 2 / (r - 2) :=
    div_nonneg (sq_nonneg _) (by linarith)
  linarith

theorem marked_quadratic_large {r z b : ℝ} (hr : 2 < r)
    (hz : 1 / (r - 1) ≤ z) (hbz : b + z ≤ 1) :
    1 / (r - 1) ≤ 2 * z - z ^ 2 - 2 * z * b + b ^ 2 / (r - 2) := by
  have hrm : r - 1 ≠ 0 := by linarith
  have hrm2 : r - 2 ≠ 0 := by linarith
  have hzr : 1 ≤ (r - 1) * z := by
    have h := (div_le_iff₀ (by linarith : 0 < r - 1)).mp hz
    nlinarith
  have ht : 0 ≤ 1 - z - b := by linarith
  have hp1 : 0 ≤ ((r - 1) * z - 1) ^ 2 / ((r - 1) * (r - 2)) :=
    div_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (by linarith))
  have hp2 : 0 ≤ (1 - z - b) * (2 * (r - 1) * z - 2 + (1 - z - b)) / (r - 2) :=
    div_nonneg (mul_nonneg ht (by linarith)) (by linarith)
  have hid : (2 * z - z ^ 2 - 2 * z * b + b ^ 2 / (r - 2)) - 1 / (r - 1) =
      ((r - 1) * z - 1) ^ 2 / ((r - 1) * (r - 2)) +
        (1 - z - b) * (2 * (r - 1) * z - 2 + (1 - z - b)) / (r - 2) := by
    field_simp
    <;> ring
  linarith

/-- The marked-set quadratic bound and the zero-mass lower bound suffice for
the density envelope. -/
theorem marked_algebra_bound {r : ℕ} (hr : 3 ≤ r) {x z b e : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / (r : ℝ)) (hz0 : 0 ≤ z)
    (hbz : b + z ≤ 1) (hz : 1 - (r : ℝ) * x ≤ z)
    (hdef : 2 * z - z ^ 2 - 2 * z * b + b ^ 2 / ((r : ℝ) - 2) ≤ 1 - 2 * e) :
    e ≤ Phi r x := by
  have hr2 : (2 : ℝ) < r := by exact_mod_cast (by omega : 2 < r)
  by_cases hlarge : 1 / ((r : ℝ) - 1) ≤ z
  · have hd := (marked_quadratic_large hr2 hlarge hbz).trans hdef
    have he : e ≤ B r 1 0 := by
      simp only [B, Nat.cast_one, mul_zero, sub_zero, one_pow]
      linarith
    exact he.trans ((B_monotoneOn (by omega) (by omega : 1 < r)
      ⟨le_rfl, by positivity⟩ ⟨hx0, hx1⟩ hx0).trans (B_le_Phi hr le_rfl (by omega) x))
  · have hz1 : z ≤ 1 / ((r : ℝ) - 1) := le_of_not_ge hlarge
    have hrp : (0 : ℝ) < r := by linarith
    have hell0 : 0 ≤ 1 - (r : ℝ) * x := by
      have h := (le_div_iff₀ hrp).mp hx1
      nlinarith
    have hell1 : 1 - (r : ℝ) * x ≤ 1 / ((r : ℝ) - 1) := hz.trans hz1
    have hdomain : RDomain r x := by
      refine ⟨?_, hx1⟩
      apply (div_le_iff₀ (mul_pos hrp (by linarith : 0 < (r : ℝ) - 1))).mpr
      have h := (le_div_iff₀ (by linarith : 0 < (r : ℝ) - 1)).mp hell1
      nlinarith
    have hzmul : ((r : ℝ) - 1) * z ≤ 1 := by
      have h := (le_div_iff₀ (by linarith : 0 < (r : ℝ) - 1)).mp hz1
      nlinarith
    have hellmul : ((r : ℝ) - 1) * (1 - (r : ℝ) * x) ≤ 1 := by
      have h := (le_div_iff₀ (by linarith : 0 < (r : ℝ) - 1)).mp hell1
      nlinarith
    have hp := mul_nonneg (sub_nonneg.mpr hz)
      (show 0 ≤ 2 - ((r : ℝ) - 1) * (z + (1 - (r : ℝ) * x)) by nlinarith)
    have hd := (marked_quadratic_small (z := z) (b := b) hr2).trans hdef
    have he : e ≤ R r x := by
      unfold R
      nlinarith
    exact he.trans (R_le_Phi hr hdomain)

variable {V : Type*} [Fintype V]

theorem marked_edge_term_bound {G : SimpleGraph V} {p : V → ℝ} {S Z : Finset V}
    (hp : ∀ v, 0 ≤ p v) (hdisj : Disjoint S Z)
    (hN : ∀ z ∈ Z, ∀ v, G.Adj z v → v ∈ S) (u v : V) :
    (if G.Adj u v then p u * p v else 0) ≤
      (if u ∈ Z then 0 else p u) * (if v ∈ Z then 0 else p v) +
        (if u ∈ Z then p u else 0) * (if v ∈ S then p v else 0) +
        (if u ∈ S then p u else 0) * (if v ∈ Z then p v else 0) -
        (if u = v ∧ u ∈ S then (p u) ^ 2 else 0) := by
  classical
  have huv0 := mul_nonneg (hp u) (hp v)
  by_cases heq : u = v
  · subst v
    by_cases huZ : u ∈ Z
    · have huS : u ∉ S := fun h => Finset.disjoint_left.mp hdisj h huZ
      simp [huZ, huS]
    · by_cases huS : u ∈ S
      · simp [huZ, huS]
        nlinarith
      · simp [huZ, huS]
        exact mul_nonneg (hp u) (hp u)
  by_cases huZ : u ∈ Z
  · have huS : u ∉ S := fun h => Finset.disjoint_left.mp hdisj h huZ
    by_cases ha : G.Adj u v
    · have hvS := hN u huZ v ha
      have hvZ : v ∉ Z := fun h => Finset.disjoint_left.mp hdisj hvS h
      simp [ha, heq, huZ, huS, hvS, hvZ]
    · simp only [ha, ite_false, heq, false_and, huZ, ite_true, huS, zero_mul, mul_zero,
        zero_add, add_zero, sub_zero]
      split_ifs <;> first | exact huv0 | simp
  · by_cases hvZ : v ∈ Z
    · have hvS : v ∉ S := fun h => Finset.disjoint_left.mp hdisj h hvZ
      by_cases ha : G.Adj u v
      · have huS := hN v hvZ u ha.symm
        simp [ha, heq, huZ, hvZ, hvS, huS]
      · simp only [ha, ite_false, heq, false_and, huZ, hvZ, ite_true, hvS,
          zero_mul, mul_zero, zero_add, add_zero, sub_zero]
        split_ifs <;> first | exact huv0 | simp
    · simp only [huZ, hvZ, ite_false, heq, false_and, mul_zero, zero_mul, add_zero, sub_zero]
      split_ifs
      · exact le_rfl
      · exact huv0

theorem marked_edgeMass_bound {G : SimpleGraph V} {p : V → ℝ} {S Z : Finset V}
    (hp : IsProbabilityWeight p) (hdisj : Disjoint S Z)
    (hN : ∀ z ∈ Z, ∀ v, G.Adj z v → v ∈ S) :
    2 * edgeMass G p ≤ (1 - ∑ z ∈ Z, p z) ^ 2 +
      2 * (∑ z ∈ Z, p z) * (∑ v ∈ S, p v) - ∑ v ∈ S, (p v) ^ 2 := by
  classical
  have hpos : (∑ v, if v ∈ Z then 0 else p v) = 1 - ∑ v ∈ Z, p v := by
    have hid : (∑ v, if v ∈ Z then 0 else p v) + (∑ v, if v ∈ Z then p v else 0) = 1 := by
      rw [← Finset.sum_add_distrib]
      convert hp.2 using 1
      apply Finset.sum_congr rfl
      intro v _
      split_ifs <;> simp
    simp only [Finset.sum_ite_mem, Finset.sum_const_zero, add_zero, Finset.univ_inter] at hid
    linarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun u _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun v _ =>
      marked_edge_term_bound hp.1 hdisj hN u v))
  have hdiag : (∑ u, ∑ v, if u = v ∧ u ∈ S then (p u) ^ 2 else 0) =
      ∑ u ∈ S, (p u) ^ 2 := by
    simp [ite_and]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, hdiag,
    ← Finset.mul_sum, ← Finset.sum_mul, hpos] at hsum
  simp only [Finset.sum_ite_mem, Finset.sum_const_zero, add_zero, Finset.univ_inter] at hsum
  unfold edgeMass
  nlinarith

theorem marked_weighted_bound {r : ℕ} (hr : 3 ≤ r)
    {G : SimpleGraph V} {p c : V → ℝ} {S Z : Finset V}
    (hp : IsProbabilityWeight p) (hc : IsOptimalCover r G p c)
    (hZ : ∀ v, v ∈ Z ↔ c v = 0) (hdisj : Disjoint S Z) (hcard : S.card = r - 2)
    (hN : ∀ z ∈ Z, ∀ v, G.Adj z v → v ∈ S) :
    edgeMass G p ≤ Phi r (coverCost p c) := by
  classical
  let z := ∑ v ∈ Z, p v
  let b := ∑ v ∈ S, p v
  have hmass : b + z ≤ 1 := by
    calc
      b + z = ∑ v ∈ S ∪ Z, p v := (Finset.sum_union hdisj).symm
      _ ≤ ∑ v, p v := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (by intro v _ _; exact hp.1 v)
      _ = 1 := hp.2
  have hz0 : 0 ≤ z := Finset.sum_nonneg (fun v _ => hp.1 v)
  have hzero : 1 - (r : ℝ) * coverCost p c ≤ z := by
    have h := zero_mass_ge_one_sub_cover_cost (by omega) hp hc
    have hsum : (∑ v, if c v = 0 then p v else 0) = z := by
      simp only [← hZ, Finset.sum_ite_mem, Finset.sum_const_zero, add_zero, Finset.univ_inter]
      rfl
    simpa [hsum] using h
  have hCauchy : b ^ 2 ≤ ((r : ℝ) - 2) * ∑ v ∈ S, (p v) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := S) (f := p)
    rw [hcard, Nat.cast_sub (by omega : 2 ≤ r), Nat.cast_ofNat] at h
    exact h
  have hr2 : (2 : ℝ) < r := by exact_mod_cast (by omega : 2 < r)
  have hdiag : b ^ 2 / ((r : ℝ) - 2) ≤ ∑ v ∈ S, (p v) ^ 2 :=
    (div_le_iff₀ (by linarith : 0 < (r : ℝ) - 2)).mpr (by nlinarith)
  have he := marked_edgeMass_bound hp hdisj hN
  apply marked_algebra_bound hr (coverCost_nonneg hp.1 hc.1.1)
    (optimal_cover_cost_le (by omega) hp hc) hz0 hmass hzero
  dsimp [z, b] at *
  nlinarith

/-- If no `r`-clique meets the zero set, a universal `(r-2)`-clique of
positive-cover atoms contains every neighbor of every zero-cover atom. -/
theorem terminal_neighbors_in_universal_clique {r : ℕ} (hr : 3 ≤ r)
    {G : SimpleGraph V} {c : V → ℝ} {Q : Finset V}
    (hQ : G.IsNClique (r - 2) Q)
    (hU : ∀ q ∈ Q, Weighted.Support.IsUniversal G q)
    (hpos : ∀ q ∈ Q, c q ≠ 0)
    (havoid : ∀ K : Finset V, G.IsNClique r K → ∀ z ∈ K, c z ≠ 0) :
    ∀ z, c z = 0 → ∀ v, G.Adj z v → v ∈ Q := by
  classical
  intro z hcz v hzv
  by_contra hvQ
  have hzQ : z ∉ Q := fun hz => hpos z hz hcz
  have hQz : G.IsNClique (r - 2 + 1) (insert z Q) := hQ.insert (by
    intro q hq
    exact (hU q hq z (by intro h; subst q; exact hzQ hq)).symm)
  have hQzv : G.IsNClique (r - 2 + 1 + 1) (insert v (insert z Q)) := hQz.insert (by
    intro q hq
    rcases Finset.mem_insert.mp hq with hq | hq
    · subst q
      exact hzv.symm
    · exact (hU q hq v (by intro h; subst q; exact hvQ hq)).symm)
  have hsize : r - 2 + 1 + 1 = r := by omega
  rw [hsize] at hQzv
  exact havoid (insert v (insert z Q)) hQzv z (by simp) hcz

theorem terminal_bound_of_universal_clique {r : ℕ} (hr : 3 ≤ r)
    {G : SimpleGraph V} {p c : V → ℝ} {Q : Finset V}
    (hp : IsProbabilityWeight p) (hc : IsOptimalCover r G p c)
    (hQ : G.IsNClique (r - 2) Q)
    (hU : ∀ q ∈ Q, Weighted.Support.IsUniversal G q)
    (hpos : ∀ q ∈ Q, c q ≠ 0)
    (havoid : ∀ K : Finset V, G.IsNClique r K → ∀ z ∈ K, c z ≠ 0) :
    edgeMass G p ≤ Phi r (coverCost p c) := by
  classical
  let Z := Finset.univ.filter (fun v => c v = 0)
  have hZ : ∀ v, v ∈ Z ↔ c v = 0 := by intro v; simp [Z]
  apply marked_weighted_bound hr hp hc hZ _ hQ.card_eq
  · exact fun z hz v hzv => terminal_neighbors_in_universal_clique hr hQ hU hpos havoid
      z ((hZ z).mp hz) v hzv
  · apply Finset.disjoint_left.mpr
    intro v hvQ hvZ
    exact hpos v hvQ ((hZ v).mp hvZ)

/-- The actual terminal case in a saturated clique-path support. -/
theorem terminal_cliquePath_bound {r : ℕ} (hr : 3 ≤ r)
    {G : SimpleGraph V} {p c : V → ℝ}
    (hp : IsProbabilityWeight p) (hc : IsOptimalCover r G p c)
    (P : Weighted.Support.CliquePathPartition G)
    (hcard : r - 2 ≤ P.middle.card)
    (hpos : ∀ v ∈ P.middle, c v ≠ 0)
    (havoid : ∀ K : Finset V, G.IsNClique r K → ∀ z ∈ K, c z ≠ 0) :
    edgeMass G p ≤ Phi r (coverCost p c) := by
  classical
  obtain ⟨Q, hQsub, hQcard⟩ := Finset.exists_subset_card_eq hcard
  have hQ : G.IsNClique (r - 2) Q :=
    ⟨P.middle_clique.subset (by simpa using hQsub), hQcard⟩
  apply terminal_bound_of_universal_clique hr hp hc hQ
  · intro q hq
    have hm : q ∈ Weighted.Support.universalVertices G := by
      rw [← P.middle_eq_universal]
      exact hQsub hq
    exact (Weighted.Support.mem_universalVertices G q).mp hm
  · exact fun q hq => hpos q (hQsub hq)
  · exact havoid

end DensityHS
