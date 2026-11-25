module

public import DensityHS.Basic.Tilings
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# Finite fractional tiling-cover strong duality

Author and maintainer: Xizhi Liu.

The finite packing duality needed here is proved by convex separation. No
linear-programming duality theorem is assumed: a separating functional for the
compact fixed-mass load polytope plus the nonnegative orthant would give a cover
cheaper than the given optimum.
-/

@[expose] public section

namespace DensityHS

open Finset Set
open scoped Pointwise

variable {I V : Type*} [Fintype I] [Fintype V]

/-- Nonnegative vectors of prescribed total mass. -/
def massSimplex (I : Type*) [Fintype I] (x : ℝ) : Set (I → ℝ) :=
  {t | (∀ i, 0 ≤ t i) ∧ ∑ i, t i = x}

theorem isCompact_massSimplex (x : ℝ) : IsCompact (massSimplex I x) := by
  have hclosed : IsClosed (massSimplex I x) := by
    have heq : massSimplex I x =
        (⋂ i, {t : I → ℝ | 0 ≤ t i}) ∩ {t : I → ℝ | ∑ i, t i = x} := by
      ext t
      simp [massSimplex]
    rw [heq]
    exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
      (isClosed_eq (by fun_prop) continuous_const)
  refine (isCompact_Icc : IsCompact (Icc (0 : I → ℝ) (fun _ => x))).of_isClosed_subset
    hclosed ?_
  intro t ht
  refine ⟨ht.1, fun i => ?_⟩
  exact ht.2 ▸ Finset.single_le_sum (fun j _ => ht.1 j) (Finset.mem_univ i)

theorem convex_massSimplex (x : ℝ) : Convex ℝ (massSimplex I x) := by
  intro t ht q hq a b ha hb hab
  refine ⟨fun i => add_nonneg (mul_nonneg ha (ht.1 i)) (mul_nonneg hb (hq.1 i)), ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, ht.2, hq.2]
  calc
    a * x + b * x = (a + b) * x := by ring
    _ = x := by rw [hab, one_mul]

/-- The finite incidence matrix, viewed as a linear map of amount vectors. -/
noncomputable def finiteLoadMap (a : I → V → ℝ) : (I → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun t v := ∑ i, t i * a i v
  map_add' t q := by ext v; simp [add_mul, Finset.sum_add_distrib]
  map_smul' b t := by ext v; simp [Finset.mul_sum, mul_assoc]

@[simp] theorem finiteLoadMap_apply (a : I → V → ℝ) (t : I → ℝ) (v : V) :
    finiteLoadMap a t v = ∑ i, t i * a i v := rfl

/-- Coordinate expansion of a linear functional on a finite product. -/
theorem linear_functional_eq_sum [DecidableEq V]
    (f : (V → ℝ) →ₗ[ℝ] ℝ) (q : V → ℝ) :
    f q = ∑ v, q v * f (Pi.single v 1) := by
  have hq : (∑ v, q v • Pi.single v (1 : ℝ)) = q := by
    ext v
    simp [Pi.single_apply]
  calc
    f q = f (∑ v, q v • Pi.single v (1 : ℝ)) := congrArg f hq.symm
    _ = ∑ v, q v * f (Pi.single v 1) := by
      rw [map_sum]
      simp only [map_smul, smul_eq_mul]

/-- A functional bounded below on a translate of the positive orthant has
nonnegative coordinate coefficients. -/
theorem functional_nonneg_of_orthant_lowerBound [DecidableEq V]
    (f : (V → ℝ) →ₗ[ℝ] ℝ) (b : V → ℝ) (u : ℝ)
    (hf : ∀ q : V → ℝ, (∀ v, 0 ≤ q v) → u < f (b + q)) :
    ∀ v, 0 ≤ f (Pi.single v 1) := by
  intro v
  by_contra! hneg
  let a := (f b - u + 1) / (-f (Pi.single v 1))
  have hb : u < f b := by simpa using hf 0 (fun _ => le_rfl)
  have ha : 0 ≤ a := le_of_lt (div_pos (by linarith) (neg_pos.mpr hneg))
  have hmul : a * (-f (Pi.single v 1)) = f b - u + 1 :=
    div_mul_cancel₀ _ (ne_of_gt (neg_pos.mpr hneg))
  have h := hf (a • Pi.single v 1) (by
    intro w
    simp only [Pi.smul_apply, smul_eq_mul]
    apply mul_nonneg ha
    simp only [Pi.single_apply]
    split_ifs <;> norm_num)
  rw [map_add, map_smul, smul_eq_mul] at h
  nlinarith

/-- A point mass belongs to the fixed-mass simplex. -/
theorem single_mem_massSimplex [DecidableEq I] {x : ℝ} (hx : 0 ≤ x) (i : I) :
    Pi.single i x ∈ massSimplex I x := by
  refine ⟨fun j => ?_, by simp⟩
  simp only [Pi.single_apply]
  split_ifs <;> simp_all

@[simp] theorem finiteLoadMap_single [DecidableEq I]
    (a : I → V → ℝ) (i : I) (x : ℝ) :
    finiteLoadMap a (Pi.single i x) = x • a i := by
  ext v
  simp [finiteLoadMap, Pi.single_apply]

/-- Every nonnegative lower bound on all finite cover costs is attained by a
fractional packing. This is the finite strong-duality step proved by separation. -/
theorem finite_packing_of_cover_lower_bound (a : I → V → ℝ) (p : V → ℝ)
    (hp : ∀ v, 0 ≤ p v) (x : ℝ) (hx : 0 ≤ x)
    (hmin : ∀ d : V → ℝ, (∀ v, 0 ≤ d v) →
      (∀ i, 1 ≤ ∑ v, d v * a i v) → x ≤ ∑ v, p v * d v) :
    ∃ t : I → ℝ, (∀ i, 0 ≤ t i) ∧
      (∀ v, ∑ i, t i * a i v ≤ p v) ∧ ∑ i, t i = x := by
  classical
  by_cases hx0 : x = 0
  · refine ⟨0, by simp, ?_, by simp [hx0]⟩
    simpa using hp
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hI : Nonempty I := by
    by_contra hn
    haveI : IsEmpty I := not_nonempty_iff.mp hn
    have h := hmin 0 (by simp) (fun i => isEmptyElim i)
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h
    exact hxpos.not_ge h
  let i₀ : I := Classical.choice hI
  let L : (I → ℝ) →ₗ[ℝ] (V → ℝ) := finiteLoadMap a
  let C : Set (V → ℝ) := L '' massSimplex I x + Set.Ici 0
  have hcompact : IsCompact (L '' massSimplex I x) :=
    (isCompact_massSimplex x).image L.continuous_of_finiteDimensional
  have hclosed : IsClosed C :=
    (isClosed_Ici : IsClosed (Set.Ici (0 : V → ℝ))).add_left_of_isCompact hcompact
  have hconvex : Convex ℝ C :=
    ((convex_massSimplex x).linear_image L).add (convex_Ici 0)
  have hgen : ∀ i : I, ∀ q : V → ℝ, (∀ v, 0 ≤ q v) → x • a i + q ∈ C := by
    intro i q hq
    refine ⟨x • a i, ?_, q, hq, rfl⟩
    exact ⟨Pi.single i x, single_mem_massSimplex hx i, finiteLoadMap_single a i x⟩
  have hpC : p ∈ C := by
    by_contra hpC
    obtain ⟨f, u, hfp, hsep⟩ := geometric_hahn_banach_point_closed hconvex hclosed hpC
    let d₀ : V → ℝ := fun v => f (Pi.single v 1)
    have hd₀ : ∀ v, 0 ≤ d₀ v :=
      functional_nonneg_of_orthant_lowerBound f.toLinearMap (x • a i₀) u
        (fun q hq => hsep _ (hgen i₀ q hq))
    have hfrepr : ∀ q : V → ℝ, f q = ∑ v, q v * d₀ v :=
      fun q => linear_functional_eq_sum f.toLinearMap q
    have hfp0 : 0 ≤ f p := by
      rw [hfrepr]
      exact Finset.sum_nonneg (fun v _ => mul_nonneg (hp v) (hd₀ v))
    have hu : 0 < u := lt_of_le_of_lt hfp0 hfp
    let d : V → ℝ := fun v => (x / u) * d₀ v
    have hd : ∀ v, 0 ≤ d v := fun v => mul_nonneg (div_nonneg hx hu.le) (hd₀ v)
    have hcover : ∀ i, 1 ≤ ∑ v, d v * a i v := by
      intro i
      have hi : u < x * f (a i) := by
        simpa only [add_zero, map_smul, smul_eq_mul] using hsep _ (hgen i 0 (by simp))
      calc
        1 ≤ (x * f (a i)) / u := (one_le_div hu).2 hi.le
        _ = ∑ v, d v * a i v := by
          rw [hfrepr]
          simp only [d, Finset.mul_sum, Finset.sum_div]
          apply Finset.sum_congr rfl
          intro v _
          ring
    have hcost : (∑ v, p v * d v) = (x / u) * f p := by
      rw [hfrepr, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      dsimp [d]
      ring
    have hcheap : (∑ v, p v * d v) < x := by
      rw [hcost]
      calc
        (x / u) * f p < (x / u) * u := mul_lt_mul_of_pos_left hfp (div_pos hxpos hu)
        _ = x := div_mul_cancel₀ x hu.ne'
    exact hcheap.not_ge (hmin d hd hcover)
  obtain ⟨q, ⟨t, ht, rfl⟩, s, hs, hps⟩ := hpC
  refine ⟨t, ht.1, ?_, ht.2⟩
  intro v
  have heq := congrFun hps v
  have hs' : 0 ≤ s v := hs v
  change (∑ i, t i * a i v) + s v = p v at heq
  linarith

variable [DecidableEq V]

/-- Extend an amount vector indexed by actual cliques by zero elsewhere. -/
noncomputable def extendCliqueAmounts (r : ℕ) (G : SimpleGraph V)
    (t : cliqueFamily r G → ℝ) (K : Finset V) : ℝ := by
  classical
  exact if h : K ∈ cliqueFamily r G then t ⟨K, h⟩ else 0

@[simp] theorem extendCliqueAmounts_coe (r : ℕ) (G : SimpleGraph V)
    (t : cliqueFamily r G → ℝ) (K : cliqueFamily r G) :
    extendCliqueAmounts r G t K = t K := by
  simp [extendCliqueAmounts, K.property]

theorem tilingSize_extendCliqueAmounts (r : ℕ) (G : SimpleGraph V)
    (t : cliqueFamily r G → ℝ) :
    tilingSize r G (extendCliqueAmounts r G t) = ∑ K, t K := by
  classical
  unfold tilingSize
  rw [← Finset.sum_coe_sort]
  simp only [extendCliqueAmounts_coe]

theorem tilingLoad_extendCliqueAmounts (r : ℕ) (G : SimpleGraph V)
    (t : cliqueFamily r G → ℝ) (v : V) :
    tilingLoad r G (extendCliqueAmounts r G t) v =
      ∑ K : cliqueFamily r G, t K * (if v ∈ (K : Finset V) then 1 else 0) := by
  classical
  unfold tilingLoad
  rw [← Finset.sum_coe_sort]
  simp only [extendCliqueAmounts_coe, mul_ite, mul_one, mul_zero]

/-- Every optimal finite clique cover has a fractional tiling of exactly the
same weight. Vertex capacities may vanish. -/
theorem exists_tiling_eq_optimal_cover {r : ℕ} {G : SimpleGraph V} {p c : V → ℝ}
    (hp : ∀ v, 0 ≤ p v) (hc : IsOptimalCover r G p c) :
    ∃ t : Finset V → ℝ, IsFractionalTiling r G p t ∧
      tilingSize r G t = coverCost p c := by
  classical
  let a : cliqueFamily r G → V → ℝ := fun K v => if v ∈ (K : Finset V) then 1 else 0
  obtain ⟨t, ht, hload, hsize⟩ := finite_packing_of_cover_lower_bound a p hp
    (coverCost p c) (coverCost_nonneg hp hc.1.1) (by
      intro d hd hcl
      apply hc.2 d
      refine ⟨hd, ?_⟩
      intro K hK
      have h := hcl ⟨K, mem_cliqueFamily.mpr hK⟩
      simpa [a, mul_ite] using h)
  refine ⟨extendCliqueAmounts r G t, ⟨?_, ?_⟩, ?_⟩
  · intro K hK
    simpa [extendCliqueAmounts, hK] using ht ⟨K, hK⟩
  · intro v
    rw [tilingLoad_extendCliqueAmounts]
    exact hload v
  · rwa [tilingSize_extendCliqueAmounts]

/-- A fractional tiling whose size dominates every feasible fractional tiling. -/
def IsOptimalFractionalTiling (r : ℕ) (G : SimpleGraph V)
    (p : V → ℝ) (t : Finset V → ℝ) : Prop :=
  IsFractionalTiling r G p t ∧ ∀ q : Finset V → ℝ,
    IsFractionalTiling r G p q → tilingSize r G q ≤ tilingSize r G t

/-- Finite fractional clique tilings and clique covers have attained equal
optima. The proof combines compact cover minimization with the separation
argument above and the elementary weak-duality inequality. -/
theorem fractional_strong_duality (r : ℕ) (G : SimpleGraph V) (hr : 0 < r)
    (p : V → ℝ) (hp : ∀ v, 0 ≤ p v) :
    ∃ (c : V → ℝ) (t : Finset V → ℝ), IsOptimalCover r G p c ∧
      IsOptimalFractionalTiling r G p t ∧ tilingSize r G t = coverCost p c := by
  obtain ⟨c, hc, _⟩ := exists_optimal_cover r G hr p hp
  obtain ⟨t, ht, heq⟩ := exists_tiling_eq_optimal_cover hp hc
  refine ⟨c, t, hc, ⟨ht, ?_⟩, heq⟩
  intro q hq
  rw [heq]
  exact fractional_weak_duality hq hc.1

/-- The finite fractional tiling number, normalized as the mass of copies. -/
noncomputable def fractionalTilingNumber (r : ℕ) (G : SimpleGraph V) (p : V → ℝ) : ℝ :=
  sSup {x : ℝ | ∃ t : Finset V → ℝ, IsFractionalTiling r G p t ∧ tilingSize r G t = x}

/-- The infimum of finite fractional cover costs. -/
noncomputable def fractionalCoverNumber (r : ℕ) (G : SimpleGraph V) (p : V → ℝ) : ℝ :=
  sInf {x : ℝ | ∃ c : V → ℝ, IsCliqueCover r G c ∧ coverCost p c = x}

theorem IsOptimalFractionalTiling.size_eq_number {r : ℕ} {G : SimpleGraph V}
    {p : V → ℝ} {t : Finset V → ℝ} (ht : IsOptimalFractionalTiling r G p t) :
    tilingSize r G t = fractionalTilingNumber r G p := by
  symm
  apply IsGreatest.csSup_eq
  refine ⟨⟨t, ht.1, rfl⟩, ?_⟩
  rintro x ⟨q, hq, rfl⟩
  exact ht.2 q hq

theorem IsOptimalCover.cost_eq_number {r : ℕ} {G : SimpleGraph V}
    {p c : V → ℝ} (hc : IsOptimalCover r G p c) :
    coverCost p c = fractionalCoverNumber r G p := by
  symm
  apply IsLeast.csInf_eq
  refine ⟨⟨c, hc.1, rfl⟩, ?_⟩
  rintro x ⟨d, hd, rfl⟩
  exact hc.2 d hd

/-- Equality of the finite fractional tiling and fractional cover numbers. -/
theorem fractional_tiling_cover_duality (r : ℕ) (G : SimpleGraph V) (hr : 0 < r)
    (p : V → ℝ) (hp : ∀ v, 0 ≤ p v) :
    fractionalTilingNumber r G p = fractionalCoverNumber r G p := by
  obtain ⟨c, t, hc, ht, heq⟩ := fractional_strong_duality r G hr p hp
  exact ht.size_eq_number.symm.trans (heq.trans hc.cost_eq_number)

/-- An upper bound on the fractional tiling number is equivalent to an
attained cover certificate with that cost bound. -/
theorem fractional_tiling_bound_iff_cover (r : ℕ) (G : SimpleGraph V) (hr : 0 < r)
    (p : V → ℝ) (hp : ∀ v, 0 ≤ p v) (x : ℝ) :
    fractionalTilingNumber r G p ≤ x ↔
      ∃ c : V → ℝ, IsCliqueCover r G c ∧ coverCost p c ≤ x := by
  obtain ⟨c, t, hc, ht, heq⟩ := fractional_strong_duality r G hr p hp
  constructor
  · intro h
    refine ⟨c, hc.1, ?_⟩
    rwa [← heq, ht.size_eq_number]
  · rintro ⟨d, hd, hcost⟩
    rw [← ht.size_eq_number]
    exact (fractional_weak_duality ht.1 hd).trans hcost

end DensityHS
