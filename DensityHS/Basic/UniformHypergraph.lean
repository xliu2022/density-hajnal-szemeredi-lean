module

public import DensityHS.Basic.FiniteDuality

/-!
# Perfect fractional tilings and normalized finite cover certificates

This finite uniform-hypergraph duality and normalization is proved directly
from the separation theorem in `FiniteDuality`.

Author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A nonnegative fractional cover of a finite family of vertex sets. -/
def IsFamilyCover (F : Finset (Finset V)) (c : V → ℝ) : Prop :=
  (∀ v, 0 ≤ c v) ∧ ∀ K ∈ F, 1 ≤ ∑ v ∈ K, c v

/-- The load on a vertex of a fractional family tiling. -/
noncomputable def familyLoad (F : Finset (Finset V)) (t : F → ℝ) (v : V) : ℝ :=
  ∑ K : F, t K * (if v ∈ (K : Finset V) then 1 else 0)

/-- Every vertex has load exactly one. -/
def IsPerfectFamilyTiling (F : Finset (Finset V)) (t : F → ℝ) : Prop :=
  (∀ K, 0 ≤ t K) ∧ ∀ v, familyLoad F t v = 1

theorem sum_familyLoad {r : ℕ} {F : Finset (Finset V)}
    (hcard : ∀ K ∈ F, K.card = r) (t : F → ℝ) :
    (∑ v, familyLoad F t v) = (r : ℝ) * ∑ K, t K := by
  classical
  unfold familyLoad
  rw [Finset.sum_comm]
  calc
    _ = ∑ K : F, (r : ℝ) * t K := by
      apply Finset.sum_congr rfl
      intro K _
      simp [hcard K K.property, mul_comm]
    _ = _ := by rw [Finset.mul_sum]

/-- If every cover costs at least `|V|/r`, the finite family has a perfect
fractional tiling. -/
theorem perfect_family_tiling_of_cover_lower_bound {r : ℕ} (hr : 0 < r)
    {F : Finset (Finset V)} (hcard : ∀ K ∈ F, K.card = r)
    (hmin : ∀ c : V → ℝ, IsFamilyCover F c →
      (Fintype.card V : ℝ) / r ≤ ∑ v, c v) :
    ∃ t : F → ℝ, IsPerfectFamilyTiling F t := by
  classical
  let a : F → V → ℝ := fun K v => if v ∈ (K : Finset V) then 1 else 0
  obtain ⟨t, ht, hload, hsize⟩ := finite_packing_of_cover_lower_bound a (fun _ => 1)
    (by intro; norm_num) ((Fintype.card V : ℝ) / r) (by positivity) (by
      intro c hc hcov
      simp only [one_mul]
      apply hmin c
      refine ⟨hc, ?_⟩
      intro K hK
      simpa [a, mul_ite] using hcov ⟨K, hK⟩)
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  have htotal : (∑ v, familyLoad F t v) = Fintype.card V := by
    rw [sum_familyLoad hcard, hsize]
    field_simp
  have hslack : ∑ v, (1 - familyLoad F t v) = 0 := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one, htotal, sub_self]
  refine ⟨t, ht, ?_⟩
  intro v
  have hv := (Finset.sum_eq_zero_iff_of_nonneg
    (fun w (_hw : w ∈ Finset.univ) => sub_nonneg.mpr (hload w))).mp hslack v
      (Finset.mem_univ v)
  change 1 - familyLoad F t v = 0 at hv
  linarith

/-- The strict cover certificate when no perfect tiling exists. -/
theorem family_cover_certificate {r : ℕ} (hr : 0 < r)
    {F : Finset (Finset V)} (hcard : ∀ K ∈ F, K.card = r)
    (hnone : ¬ ∃ t : F → ℝ, IsPerfectFamilyTiling F t) :
    ∃ c : V → ℝ, IsFamilyCover F c ∧ ∑ v, c v < (Fintype.card V : ℝ) / r := by
  classical
  by_contra hn
  apply hnone
  apply perfect_family_tiling_of_cover_lower_bound hr hcard
  intro c hc
  exact le_of_not_gt (fun h => hn ⟨c, hc, h⟩)

/-- Subtracting the least cover coordinate and renormalizing preserves a
strict cover deficit and produces a zero coordinate. -/
theorem normalize_family_cover {r : ℕ} (hr : 0 < r) [Nonempty V]
    {F : Finset (Finset V)} (hcard : ∀ K ∈ F, K.card = r)
    {c : V → ℝ} (hc : IsFamilyCover F c)
    (hcost : ∑ v, c v < (Fintype.card V : ℝ) / r) :
    ∃ d : V → ℝ, IsFamilyCover F d ∧
      (∑ v, d v < (Fintype.card V : ℝ) / r) ∧ ∃ v, d v = 0 := by
  classical
  obtain ⟨v₀, _hv₀, hmin⟩ := Finset.exists_min_image Finset.univ c Finset.univ_nonempty
  let a : ℝ := c v₀
  have hN : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hr0 : (r : ℝ) ≠ 0 := ne_of_gt hrR
  have hmin' : ∀ v, a ≤ c v := fun v => hmin v (Finset.mem_univ v)
  have hsumlower : (Fintype.card V : ℝ) * a ≤ ∑ v, c v := by
    calc
      _ = ∑ _v : V, a := by simp
      _ ≤ _ := Finset.sum_le_sum (fun v _ => hmin' v)
  have ha : a < 1 / (r : ℝ) := by
    apply (mul_lt_mul_iff_right₀ hN).mp
    simpa only [div_eq_mul_inv, one_mul] using hsumlower.trans_lt hcost
  have hden : 0 < 1 - (r : ℝ) * a := by
    have h := (lt_div_iff₀ hrR).mp ha
    nlinarith
  let d : V → ℝ := fun v => (c v - a) / (1 - (r : ℝ) * a)
  have hd : IsFamilyCover F d := by
    refine ⟨fun v => div_nonneg (sub_nonneg.mpr (hmin' v)) hden.le, ?_⟩
    intro K hK
    change 1 ≤ ∑ v ∈ K, (c v - a) / (1 - (r : ℝ) * a)
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul, hcard K hK]
    apply (le_div_iff₀ hden).mpr
    have hcov := hc.2 K hK
    linarith
  have hdcost : ∑ v, d v < (Fintype.card V : ℝ) / r := by
    dsimp [d]
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    apply (div_lt_iff₀ hden).mpr
    have heq : (Fintype.card V : ℝ) / r * (1 - (r : ℝ) * a) =
        (Fintype.card V : ℝ) / r - (Fintype.card V : ℝ) * a := by field_simp
    rw [heq]
    linarith
  exact ⟨d, hd, hdcost, v₀, by simp [d, a]⟩

theorem normalized_family_cover_certificate {r : ℕ} (hr : 0 < r) [Nonempty V]
    {F : Finset (Finset V)} (hcard : ∀ K ∈ F, K.card = r)
    (hnone : ¬ ∃ t : F → ℝ, IsPerfectFamilyTiling F t) :
    ∃ c : V → ℝ, IsFamilyCover F c ∧
      (∑ v, c v < (Fintype.card V : ℝ) / r) ∧ ∃ v, c v = 0 := by
  obtain ⟨c, hc, hcost⟩ := family_cover_certificate hr hcard hnone
  exact normalize_family_cover hr hcard hc hcost

end DensityHS
