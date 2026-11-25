module

public import DensityHS.Weighted.RigidAlgebra
public import DensityHS.Weighted.Optimization
public import DensityHS.Weighted.SupportCoverLevels

/-!
# The rigid-cover bounds on actual finite graphs

Partition sums, weighted degrees, uniformity of weights on equal-cover
classes, and their conversion to the algebraic certificates.

Author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS

open Finset
open Weighted.Support

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

theorem Weighted.Support.CliquePathPartition.sum_parts {G : SimpleGraph V}
    (P : CliquePathPartition G) (f : V → ℝ) :
    (∑ v ∈ P.left, f v) + (∑ v ∈ P.middle, f v) + (∑ v ∈ P.right, f v) = ∑ v, f v := by
  classical
  have hdisj : Disjoint (P.left ∪ P.middle) P.right :=
    Finset.disjoint_union_left.mpr ⟨P.left_right_disjoint, P.middle_right_disjoint⟩
  have hunion : P.left ∪ P.middle ∪ P.right = Finset.univ := by
    apply Finset.coe_injective
    simpa only [Finset.coe_union, Finset.coe_univ, Set.union_assoc] using P.union_eq
  rw [← Finset.sum_union P.left_middle_disjoint, ← Finset.sum_union hdisj, hunion]

theorem Weighted.Support.CliquePathPartition.degree_middle {G : SimpleGraph V} (P : CliquePathPartition G)
    {p : V → ℝ} (hp : IsProbabilityWeight p) {v : V} (hv : v ∈ P.middle) :
    weightedDegree G p v = 1 - p v := by
  classical
  have hU : IsUniversal G v := by
    apply (mem_universalVertices G v).mp
    rwa [← P.middle_eq_universal]
  have ht : ∀ u, (if G.Adj v u then p u else 0) = p u - if u = v then p u else 0 := by
    intro u
    by_cases hu : u = v
    · subst u
      simp
    · simp [hu, hU u (Ne.symm hu)]
  simp only [weightedDegree, G.adj_comm, ht, Finset.sum_sub_distrib]
  simp [hp.2]

theorem Weighted.Support.CliquePathPartition.degree_left {G : SimpleGraph V} (P : CliquePathPartition G)
    {p : V → ℝ} (hp : IsProbabilityWeight p) {v : V} (hv : v ∈ P.left) :
    weightedDegree G p v = 1 - (∑ u ∈ P.right, p u) - p v := by
  classical
  have hvR : v ∉ P.right := fun h => Finset.disjoint_left.mp P.left_right_disjoint hv h
  have ht : ∀ u, (if G.Adj v u then p u else 0) =
      p u - (if u ∈ P.right then p u else 0) - (if u = v then p u else 0) := by
    intro u
    by_cases hu : u = v
    · subst u
      simp [hvR]
    by_cases huR : u ∈ P.right
    · simp [hu, huR, P.ends_anticomplete v hv u huR]
    · have hadj : G.Adj v u := by
        rcases P.mem_parts u with huL | huB | huR'
        · exact P.left_clique hv huL (Ne.symm hu)
        · exact P.left_middle_adj hv huB
        · exact False.elim (huR huR')
      simp [hu, huR, hadj]
  simp only [weightedDegree, G.adj_comm, ht, Finset.sum_sub_distrib]
  simp [hp.2]

theorem Weighted.Support.CliquePathPartition.degree_right {G : SimpleGraph V} (P : CliquePathPartition G)
    {p : V → ℝ} (hp : IsProbabilityWeight p) {v : V} (hv : v ∈ P.right) :
    weightedDegree G p v = 1 - (∑ u ∈ P.left, p u) - p v := by
  classical
  have hvL : v ∉ P.left := fun h => Finset.disjoint_left.mp P.left_right_disjoint h hv
  have ht : ∀ u, (if G.Adj v u then p u else 0) =
      p u - (if u ∈ P.left then p u else 0) - (if u = v then p u else 0) := by
    intro u
    by_cases hu : u = v
    · subst u
      simp [hvL]
    by_cases huL : u ∈ P.left
    · have hnot : ¬ G.Adj v u := fun h => P.ends_anticomplete u huL v hv h.symm
      simp [hu, huL, hnot]
    · have hadj : G.Adj v u := by
        rcases P.mem_parts u with huL' | huB | huR
        · exact False.elim (huL huL')
        · exact (P.middle_right_adj huB hv).symm
        · exact P.right_clique hv huR (Ne.symm hu)
      simp [hu, huL, hadj]
  simp only [weightedDegree, G.adj_comm, ht, Finset.sum_sub_distrib]
  simp [hp.2]

theorem Weighted.Support.CliquePathPartition.edge_term_identity {G : SimpleGraph V}
    (P : CliquePathPartition G) (p : V → ℝ) (u v : V) :
    (if G.Adj u v then p u * p v else 0) = p u * p v -
      (if u = v then (p u) ^ 2 else 0) -
      (if u ∈ P.left ∧ v ∈ P.right then p u * p v else 0) -
      (if u ∈ P.right ∧ v ∈ P.left then p u * p v else 0) := by
  classical
  by_cases heq : u = v
  · subst v
    have hn : ¬ (u ∈ P.left ∧ u ∈ P.right) := by
      rintro ⟨h1, h2⟩
      exact Finset.disjoint_left.mp P.left_right_disjoint h1 h2
    have hn' : ¬ (u ∈ P.right ∧ u ∈ P.left) := by tauto
    simp [hn, hn']
    ring
  rcases P.mem_parts u with hu | hu | hu <;> rcases P.mem_parts v with hv | hv | hv
  · have huR : u ∉ P.right := fun h => Finset.disjoint_left.mp P.left_right_disjoint hu h
    have hvR : v ∉ P.right := fun h => Finset.disjoint_left.mp P.left_right_disjoint hv h
    simp [heq, hu, hv, huR, hvR, P.left_clique hu hv heq]
  · have huR : u ∉ P.right := fun h => Finset.disjoint_left.mp P.left_right_disjoint hu h
    have hvR : v ∉ P.right := fun h => Finset.disjoint_left.mp P.middle_right_disjoint hv h
    simp [heq, huR, hvR, P.left_middle_adj hu hv]
  · have huR : u ∉ P.right := fun h => Finset.disjoint_left.mp P.left_right_disjoint hu h
    simp [heq, hu, hv, huR, P.ends_anticomplete u hu v hv]
  · have huR : u ∉ P.right := fun h => Finset.disjoint_left.mp P.middle_right_disjoint hu h
    have huL : u ∉ P.left := fun h => Finset.disjoint_left.mp P.left_middle_disjoint h hu
    simp [heq, huR, huL, (P.left_middle_adj hv hu).symm]
  · have huR : u ∉ P.right := fun h => Finset.disjoint_left.mp P.middle_right_disjoint hu h
    have huL : u ∉ P.left := fun h => Finset.disjoint_left.mp P.left_middle_disjoint h hu
    simp [heq, huR, huL, P.middle_clique hu hv heq]
  · have huR : u ∉ P.right := fun h => Finset.disjoint_left.mp P.middle_right_disjoint hu h
    have huL : u ∉ P.left := fun h => Finset.disjoint_left.mp P.left_middle_disjoint h hu
    simp [heq, huR, huL, P.middle_right_adj hu hv]
  · have hvR : v ∉ P.right := fun h => Finset.disjoint_left.mp P.left_right_disjoint hv h
    have hnot : ¬ G.Adj u v := fun h => P.ends_anticomplete v hv u hu h.symm
    simp [heq, hu, hv, hvR, hnot]
  · have hvL : v ∉ P.left := fun h => Finset.disjoint_left.mp P.left_middle_disjoint h hv
    have hvR : v ∉ P.right := fun h => Finset.disjoint_left.mp P.middle_right_disjoint hv h
    simp [heq, hvL, hvR, (P.middle_right_adj hv hu).symm]
  · have huL : u ∉ P.left := fun h => Finset.disjoint_left.mp P.left_right_disjoint h hu
    have hvL : v ∉ P.left := fun h => Finset.disjoint_left.mp P.left_right_disjoint h hv
    simp [heq, huL, hvL, P.right_clique hu hv heq]

theorem Weighted.Support.CliquePathPartition.deficiency_identity {G : SimpleGraph V}
    (P : CliquePathPartition G) {p : V → ℝ} (hp : IsProbabilityWeight p) :
    1 - 2 * edgeMass G p = (∑ v, (p v) ^ 2) +
      2 * (∑ v ∈ P.left, p v) * (∑ v ∈ P.right, p v) := by
  classical
  have hsum := congrArg (fun f : V → V → ℝ => ∑ u, ∑ v, f u v)
    (funext fun u => funext fun v => P.edge_term_identity p u v)
  simp only [Finset.sum_sub_distrib] at hsum
  have hdiag : (∑ u, ∑ v, if u = v then (p u) ^ 2 else 0) = ∑ u, (p u) ^ 2 := by simp
  have hcross : (∑ u, ∑ v, if u ∈ P.left ∧ v ∈ P.right then p u * p v else 0) =
      (∑ u ∈ P.left, p u) * (∑ v ∈ P.right, p v) := by
    simp [ite_and, Finset.sum_ite_irrel, ← Finset.mul_sum, ← Finset.sum_mul]
  have hcross' : (∑ u, ∑ v, if u ∈ P.right ∧ v ∈ P.left then p u * p v else 0) =
      (∑ u ∈ P.right, p u) * (∑ v ∈ P.left, p v) := by
    simp [ite_and, Finset.sum_ite_irrel, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [hdiag, hcross, hcross'] at hsum
  simp only [← Finset.mul_sum, ← Finset.sum_mul, hp.2, one_mul] at hsum
  unfold edgeMass
  nlinarith

theorem rigid_two_singletons_bound {r : ℕ} (hr : 3 ≤ r)
    {G : SimpleGraph V} {p c : V → ℝ} (hp : IsProbabilityWeight p)
    (P : CliquePathPartition G) {a z : V}
    (hA : P.left = {a}) (hC : P.right = {z}) (hca : c a = 0) (hcz : c z = 0)
    (hcB : ∀ b ∈ P.middle, c b = 1 / ((r : ℝ) - 1)) :
    edgeMass G p ≤ Phi r (coverCost p c) := by
  classical
  have hnorm := P.sum_parts p
  rw [hp.2, hA, hC] at hnorm
  simp only [Finset.sum_singleton] at hnorm
  have hcost : coverCost p c = (∑ b ∈ P.middle, p b) / ((r : ℝ) - 1) := by
    have hs := P.sum_parts (fun v => p v * c v)
    rw [hA, hC] at hs
    simp only [Finset.sum_singleton, hca, hcz, mul_zero, zero_add, add_zero] at hs
    unfold coverCost
    rw [← hs]
    rw [Finset.sum_congr rfl (fun b hb => by rw [hcB b hb])]
    simp [Finset.sum_div, div_eq_mul_inv, ← Finset.sum_mul]
  have hdef := P.deficiency_identity hp
  have hsq := P.sum_parts (fun v => (p v) ^ 2)
  rw [hA, hC] at hdef hsq
  simp only [Finset.sum_singleton] at hdef hsq
  have hdiag : 0 ≤ ∑ b ∈ P.middle, (p b) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  apply two_end_edge_bound_Phi hr hnorm hcost hdiag
  nlinarith

/-- The real-variable bridge for the cardinalities and weights of the third
rigid case. Every displayed equation is subsequently derived from the graph. -/
theorem rigid_stationary_masses_bound {r j : ℕ} (hr : 3 ≤ r) (hj : 1 ≤ j)
    {a0 s t w d u μ x e : ℝ}
    (ha0 : (j : ℝ) + 1 ≤ a0) (ht : (j : ℝ) ≤ t)
    (hs : s = (r : ℝ) - 1 - j) (hw : 0 ≤ w) (hu : 0 < u)
    (hμ : μ / (r : ℝ) = (a0 - 1) * w)
    (hhigh : a0 * w + d - u = μ * ((j : ℝ) + 1) / ((r : ℝ) * j))
    (hnorm : a0 * w + s * (d + w) + t * u + d = 1)
    (hcost : x = (a0 * w + s * (d + w)) / (r : ℝ) +
      t * (((j : ℝ) + 1) / ((r : ℝ) * j)) * u)
    (hdef : 1 - 2 * e = a0 * w ^ 2 + s * (d + w) ^ 2 +
      t * u ^ 2 + d ^ 2 + 2 * a0 * w * d)
    (hx : x ≤ 1 / (r : ℝ)) : e ≤ Phi r x := by
  let h : ℝ := a0 - 1 - j
  let κ : ℝ := t - j
  let v : ℝ := ((j : ℝ) + h) * w / j
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hj0 : (j : ℝ) ≠ 0 := by linarith
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  have hh : 0 ≤ h := by dsimp [h]; linarith
  have hκ : 0 ≤ κ := by dsimp [κ]; linarith
  have hN : (j : ℝ) + h ≠ 0 := by linarith
  have ha0' : a0 = (j : ℝ) + h + 1 := by dsimp [h]; ring
  have ht' : t = (j : ℝ) + κ := by dsimp [κ]; ring
  have hμ' : μ / (r : ℝ) = ((j : ℝ) + h) * w := by
    rw [ha0'] at hμ
    simpa only [add_sub_cancel_right] using hμ
  have hhigh' : ((j : ℝ) + h + 1) * w + d - u =
      μ * ((j : ℝ) + 1) / ((r : ℝ) * j) := by rwa [ha0'] at hhigh
  obtain ⟨hw', hd', hlow⟩ := rigid_weights_from_stationarity hr0 hj0 hN hμ'
    hhigh' (show d + w = d + w from rfl) (show v = ((j : ℝ) + h) * w / j from rfl)
  have hv : 0 ≤ v := div_nonneg (mul_nonneg (by linarith) hw) (by linarith)
  have hnorm' : (r : ℝ) * v + ((r : ℝ) + κ) * u = 1 := by
    rw [hlow, ha0', hs, ht', hw', hd', rigid_total_mass_identity hN] at hnorm
    exact hnorm
  have hcost' := hcost
  rw [hlow, ha0', hs, ht', hw'] at hcost'
  have hell : 1 - (r : ℝ) * x = rigidEll j h κ u v := by
    calc
      1 - (r : ℝ) * x = ((r : ℝ) * v + ((r : ℝ) + κ) * u) - (r : ℝ) * x := by
        rw [hnorm']
      _ = rigidEll j h κ u v := by
        rw [hcost']
        exact rigid_cover_cost_identity hr0 hj0 hN
  have hdef' : 1 - 2 * e = rigidDeficiency r j h κ u v := by
    rw [hlow, ha0', hs, ht', hw', hd', rigid_diagonal_deficiency_identity hN] at hdef
    exact hdef
  exact rigid_edge_bound_Phi hr hjR hh hκ hu hv hnorm' hell hdef' hx

theorem sum_uniform_class {S : Finset V} {p : V → ℝ} {w : ℝ}
    (h : ∀ v ∈ S, p v = w) (f : ℝ → ℝ) :
    (∑ v ∈ S, f (p v)) = (S.card : ℝ) * f w := by
  calc
    (∑ v ∈ S, f (p v)) = ∑ _v ∈ S, f w := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [h v hv]
    _ = _ := by simp

/-- The third rigid-cover case, derived from actual graph stationarity.
`L` and `T` are the low and high cover classes in the universal clique. -/
theorem rigid_high_class_bound {r j : ℕ} (hr : 3 ≤ r) (hj : 1 ≤ j)
    {G : SimpleGraph V} {p c : V → ℝ}
    (hp : IsProbabilityWeight p) (hpos : ∀ v, 0 < p v)
    (P : CliquePathPartition G) {z : V} {L T : Finset V}
    (hC : P.right = {z}) (hcz : c z = 0)
    (hLT : L ∪ T = P.middle) (hdisj : Disjoint L T)
    (hA : ∀ a ∈ P.left, c a = 1 / (r : ℝ))
    (hL : ∀ b ∈ L, c b = 1 / (r : ℝ))
    (hT : ∀ b ∈ T, c b = ((j : ℝ) + 1) / ((r : ℝ) * j))
    (hcardL : L.card + j + 1 = r)
    (hcardA : j + 1 ≤ P.left.card) (hcardT : j ≤ T.card)
    {lam μ : ℝ} (hstat : ∀ v, weightedDegree G p v = lam + μ * c v)
    (hx : coverCost p c ≤ 1 / (r : ℝ)) :
    edgeMass G p ≤ Phi r (coverCost p c) := by
  classical
  obtain ⟨a, ha⟩ := P.left_nonempty
  obtain ⟨b, hb⟩ : T.Nonempty := Finset.card_pos.mp (by omega)
  let w : ℝ := p a
  let d : ℝ := p z
  let u : ℝ := p b
  have hz : z ∈ P.right := by simp [hC]
  have hLB : L ⊆ P.middle := by rw [← hLT]; exact Finset.subset_union_left
  have hTB : T ⊆ P.middle := by rw [← hLT]; exact Finset.subset_union_right
  have hsumB (f : V → ℝ) : (∑ v ∈ P.middle, f v) =
      (∑ v ∈ L, f v) + (∑ v ∈ T, f v) := by
    rw [← hLT, Finset.sum_union hdisj]
  have hsumC (f : V → ℝ) : (∑ v ∈ P.right, f v) = f z := by simp [hC]
  have hsA := hstat a
  rw [P.degree_left hp ha, hsumC, hA a ha] at hsA
  have hsT := hstat b
  rw [P.degree_middle hp (hTB hb), hT b hb] at hsT
  have hwpA : ∀ v ∈ P.left, p v = w := by
    intro v hv
    have hv' := hstat v
    rw [P.degree_left hp hv, hsumC, hA v hv] at hv'
    dsimp [w]
    linarith
  have hwpT : ∀ v ∈ T, p v = u := by
    intro v hv
    have hv' := hstat v
    rw [P.degree_middle hp (hTB hv), hT v hv] at hv'
    dsimp [u]
    linarith
  have hwpL : ∀ v ∈ L, p v = d + w := by
    intro v hv
    have hv' := hstat v
    rw [P.degree_middle hp (hLB hv), hL v hv] at hv'
    dsimp [d, w]
    linarith
  have hsumA := sum_uniform_class hwpA (fun x => x)
  have hsumL := sum_uniform_class hwpL (fun x => x)
  have hsumT := sum_uniform_class hwpT (fun x => x)
  have hsZ := hstat z
  rw [P.degree_right hp hz, hsumA, hcz, mul_zero, add_zero] at hsZ
  have hμ : μ / (r : ℝ) = ((P.left.card : ℝ) - 1) * w := by
    have hdiv : μ * (1 / (r : ℝ)) = μ / (r : ℝ) := by ring
    rw [hdiv] at hsA
    dsimp [w] at *
    nlinarith
  have hhigh : (P.left.card : ℝ) * w + d - u =
      μ * ((j : ℝ) + 1) / ((r : ℝ) * j) := by
    have hdiv : μ * (((j : ℝ) + 1) / ((r : ℝ) * j)) =
        μ * ((j : ℝ) + 1) / ((r : ℝ) * j) := by ring
    rw [hdiv] at hsT
    dsimp [d, u]
    linarith
  have hnorm : (P.left.card : ℝ) * w + (L.card : ℝ) * (d + w) +
      (T.card : ℝ) * u + d = 1 := by
    have hn := P.sum_parts p
    rw [hp.2, hsumB, hsumA, hsumL, hsumT, hsumC] at hn
    dsimp [d]
    linarith
  have hcost : coverCost p c =
      ((P.left.card : ℝ) * w + (L.card : ℝ) * (d + w)) / (r : ℝ) +
        (T.card : ℝ) * (((j : ℝ) + 1) / ((r : ℝ) * j)) * u := by
    have ha' : (∑ v ∈ P.left, p v * c v) = (P.left.card : ℝ) * (w / (r : ℝ)) := by
      calc
        _ = ∑ _v ∈ P.left, w / (r : ℝ) := by
          apply Finset.sum_congr rfl
          intro v hv
          rw [hwpA v hv, hA v hv]
          ring
        _ = _ := by simp
    have hl' : (∑ v ∈ L, p v * c v) = (L.card : ℝ) * ((d + w) / (r : ℝ)) := by
      calc
        _ = ∑ _v ∈ L, (d + w) / (r : ℝ) := by
          apply Finset.sum_congr rfl
          intro v hv
          rw [hwpL v hv, hL v hv]
          ring
        _ = _ := by simp
    have ht' : (∑ v ∈ T, p v * c v) =
        (T.card : ℝ) * (u * (((j : ℝ) + 1) / ((r : ℝ) * j))) := by
      calc
        _ = ∑ _v ∈ T, u * (((j : ℝ) + 1) / ((r : ℝ) * j)) := by
          apply Finset.sum_congr rfl
          intro v hv
          rw [hwpT v hv, hT v hv]
        _ = _ := by simp
    have hs := P.sum_parts (fun v => p v * c v)
    rw [hsumB, ha', hl', ht', hsumC, hcz, mul_zero, add_zero] at hs
    unfold coverCost
    rw [← hs]
    ring
  have hdef : 1 - 2 * edgeMass G p = (P.left.card : ℝ) * w ^ 2 +
      (L.card : ℝ) * (d + w) ^ 2 + (T.card : ℝ) * u ^ 2 + d ^ 2 +
        2 * (P.left.card : ℝ) * w * d := by
    have hs := P.sum_parts (fun v => (p v) ^ 2)
    rw [hsumB, sum_uniform_class hwpA (fun x => x ^ 2),
      sum_uniform_class hwpL (fun x => x ^ 2),
      sum_uniform_class hwpT (fun x => x ^ 2), hsumC] at hs
    have hd := P.deficiency_identity hp
    rw [← hs, hsumA, hsumC] at hd
    dsimp [d]
    nlinarith
  have hs : (L.card : ℝ) = (r : ℝ) - 1 - j := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) hcardL
    push_cast at h
    linarith
  apply rigid_stationary_masses_bound hr hj _ _ hs (le_of_lt (hpos a)) (hpos b)
    hμ hhigh hnorm hcost hdef hx
  · exact_mod_cast hcardA
  · exact_mod_cast hcardT

end DensityHS
