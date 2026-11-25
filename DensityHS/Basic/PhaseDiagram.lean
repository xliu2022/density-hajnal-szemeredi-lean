module

public import DensityHS.Basic.EnvelopeStrict

/-!
# Exact branch crossings of the density envelope

The statements here use the restricted domains of the exceptional branches.
Crossings of ordinary branches are compared on the whole admissible parameter
interval, including its endpoints.

Author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS

/-- Intersection parameter of two distinct ordinary branches. -/
noncomputable def BCrossing (r i j : ℕ) : ℝ :=
  1 / ((r : ℝ) + Real.sqrt (((r : ℝ) - i) * ((r : ℝ) - j)))

/-- The first nonzero exceptional crossing. -/
noncomputable def AStart (r : ℕ) : ℝ := 2 / (4 * (r : ℝ) - 3)

/-- The tangential endpoint of the exceptional `A` branch. -/
noncomputable def AEnd (r : ℕ) : ℝ := 1 / (2 * ((r : ℝ) - 1))

theorem B_difference {r i j : ℕ} (hi : i < r) (hj : j < r) (x : ℝ) :
    B r j x - B r i x = ((j : ℝ) - i) / 2 *
      (x ^ 2 - (1 - (r : ℝ) * x) ^ 2 / (((r : ℝ) - i) * ((r : ℝ) - j))) := by
  have hiR : (i : ℝ) < r := by exact_mod_cast hi
  have hjR : (j : ℝ) < r := by exact_mod_cast hj
  have hi0 : (r : ℝ) - i ≠ 0 := by linarith
  have hj0 : (r : ℝ) - j ≠ 0 := by linarith
  unfold B
  field_simp
  <;> ring

theorem B_le_B_iff_square {r i j : ℕ} (hij : i < j) (hj : j < r) (x : ℝ) :
    B r i x ≤ B r j x ↔
      (1 - (r : ℝ) * x) ^ 2 ≤ (((r : ℝ) - i) * ((r : ℝ) - j)) * x ^ 2 := by
  have hi : i < r := hij.trans hj
  have hijR : (i : ℝ) < j := by exact_mod_cast hij
  have hjR : (j : ℝ) < r := by exact_mod_cast hj
  have hprod : 0 < ((r : ℝ) - i) * ((r : ℝ) - j) := mul_pos (by linarith) (by linarith)
  rw [← sub_nonneg, B_difference hi hj, mul_nonneg_iff_of_pos_left (by linarith)]
  rw [sub_nonneg, div_le_iff₀ hprod]
  constructor <;> intro h <;> nlinarith

theorem B_lt_B_iff_square {r i j : ℕ} (hij : i < j) (hj : j < r) (x : ℝ) :
    B r i x < B r j x ↔
      (1 - (r : ℝ) * x) ^ 2 < (((r : ℝ) - i) * ((r : ℝ) - j)) * x ^ 2 := by
  have hi : i < r := hij.trans hj
  have hijR : (i : ℝ) < j := by exact_mod_cast hij
  have hjR : (j : ℝ) < r := by exact_mod_cast hj
  have hprod : 0 < ((r : ℝ) - i) * ((r : ℝ) - j) := mul_pos (by linarith) (by linarith)
  rw [← sub_pos, B_difference hi hj, mul_pos_iff_of_pos_left (by linarith)]
  rw [sub_pos, div_lt_iff₀ hprod]
  constructor <;> intro h <;> nlinarith

/-- Each pair of ordinary branches has one intersection on `[0,1/r]`. -/
theorem B_le_B_iff_crossing {r i j : ℕ} (hij : i < j) (hj : j < r)
    {x : ℝ} (hx0 : 0 ≤ x) (hxr : x ≤ 1 / (r : ℝ)) :
    B r i x ≤ B r j x ↔ BCrossing r i j ≤ x := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hiR : (i : ℝ) < r := by exact_mod_cast (hij.trans hj)
  have hjR : (j : ℝ) < r := by exact_mod_cast hj
  let p : ℝ := ((r : ℝ) - i) * ((r : ℝ) - j)
  have hp : 0 < p := mul_pos (by linarith) (by linarith)
  have hs : 0 ≤ Real.sqrt p := Real.sqrt_nonneg _
  have hsq : (Real.sqrt p) ^ 2 = p := Real.sq_sqrt hp.le
  have hell : 0 ≤ 1 - (r : ℝ) * x := by
    have h := (le_div_iff₀ hr0).mp hxr
    nlinarith
  rw [B_le_B_iff_square hij hj]
  change (1 - (r : ℝ) * x) ^ 2 ≤ p * x ^ 2 ↔ 1 / ((r : ℝ) + Real.sqrt p) ≤ x
  rw [div_le_iff₀ (by positivity : 0 < (r : ℝ) + Real.sqrt p)]
  have hsx : 0 ≤ Real.sqrt p * x := mul_nonneg hs hx0
  have hid : (Real.sqrt p * x) ^ 2 = p * x ^ 2 := by rw [mul_pow, hsq]
  constructor
  · intro h
    have hle : 1 - (r : ℝ) * x ≤ Real.sqrt p * x := by nlinarith
    nlinarith
  · intro h
    have hle : 1 - (r : ℝ) * x ≤ Real.sqrt p * x := by nlinarith
    nlinarith

theorem B_lt_B_iff_crossing {r i j : ℕ} (hij : i < j) (hj : j < r)
    {x : ℝ} (hx0 : 0 ≤ x) (hxr : x ≤ 1 / (r : ℝ)) :
    B r i x < B r j x ↔ BCrossing r i j < x := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hiR : (i : ℝ) < r := by exact_mod_cast (hij.trans hj)
  have hjR : (j : ℝ) < r := by exact_mod_cast hj
  let p : ℝ := ((r : ℝ) - i) * ((r : ℝ) - j)
  have hp : 0 < p := mul_pos (by linarith) (by linarith)
  have hs : 0 ≤ Real.sqrt p := Real.sqrt_nonneg _
  have hsq : (Real.sqrt p) ^ 2 = p := Real.sq_sqrt hp.le
  have hell : 0 ≤ 1 - (r : ℝ) * x := by
    have h := (le_div_iff₀ hr0).mp hxr
    nlinarith
  rw [B_lt_B_iff_square hij hj]
  change (1 - (r : ℝ) * x) ^ 2 < p * x ^ 2 ↔ 1 / ((r : ℝ) + Real.sqrt p) < x
  rw [div_lt_iff₀ (by positivity : 0 < (r : ℝ) + Real.sqrt p)]
  have hsx : 0 ≤ Real.sqrt p * x := mul_nonneg hs hx0
  have hid : (Real.sqrt p * x) ^ 2 = p * x ^ 2 := by rw [mul_pow, hsq]
  constructor
  · intro h
    have hle : 1 - (r : ℝ) * x < Real.sqrt p * x := by nlinarith
    nlinarith
  · intro h
    have hle : 1 - (r : ℝ) * x < Real.sqrt p * x := by nlinarith
    nlinarith

theorem B_eq_B_iff_crossing {r i j : ℕ} (hij : i < j) (hj : j < r)
    {x : ℝ} (hx0 : 0 ≤ x) (hxr : x ≤ 1 / (r : ℝ)) :
    B r i x = B r j x ↔ x = BCrossing r i j := by
  constructor
  · intro h
    have hle := (B_le_B_iff_crossing hij hj hx0 hxr).mp h.le
    have hn : ¬ B r i x < B r j x := not_lt_of_ge h.ge
    rw [B_lt_B_iff_crossing hij hj hx0 hxr, not_lt] at hn
    exact le_antisymm hn hle
  · intro h
    have hle := (B_le_B_iff_crossing hij hj hx0 hxr).mpr h.ge
    have hn : ¬ B r i x < B r j x := by
      rw [B_lt_B_iff_crossing hij hj hx0 hxr]
      simp [h]
    exact le_antisymm hle (le_of_not_gt hn)

/-- Ordinary branches attain their envelope precisely when neither adjacent
branch is larger. This also includes the first and last ordinary branches. -/
theorem B_dominates_iff_adjacent {r i : ℕ} (hi : 1 ≤ i) (hir : i < r) (x : ℝ) :
    (∀ j, 1 ≤ j → j < r → B r j x ≤ B r i x) ↔
      (1 < i → B r (i - 1) x ≤ B r i x) ∧
      (i + 1 < r → B r (i + 1) x ≤ B r i x) := by
  constructor
  · intro h
    exact ⟨fun hprev => h (i - 1) (by omega) (by omega),
      fun hnext => h (i + 1) (by omega) hnext⟩
  · rintro ⟨hprev, hnext⟩ j hj hjr
    rcases lt_trichotomy j i with hji | rfl | hij
    · have hi1 : 1 < i := by omega
      have hlocal := (B_le_B_iff_square (by omega : i - 1 < i) hir x).mp (hprev hi1)
      apply (B_le_B_iff_square hji hir x).mpr
      have hjR : (j : ℝ) ≤ (i : ℝ) - 1 := by
        have h : (j : ℝ) + 1 ≤ i := by exact_mod_cast (by omega : j + 1 ≤ i)
        linarith
      have hirR : (i : ℝ) < r := by exact_mod_cast hir
      rw [Nat.cast_sub (by omega : 1 ≤ i), Nat.cast_one] at hlocal
      have hmul := mul_nonneg (mul_nonneg (by linarith : 0 ≤ (i : ℝ) - 1 - j)
        (by linarith : 0 ≤ (r : ℝ) - i)) (sq_nonneg x)
      nlinarith
    · exact le_rfl
    · have hnextR : i + 1 < r := by omega
      have hlocal : (((r : ℝ) - i) * ((r : ℝ) - (i + 1 : ℕ))) * x ^ 2 ≤
          (1 - (r : ℝ) * x) ^ 2 := by
        have hn : ¬ B r i x < B r (i + 1) x := not_lt_of_ge (hnext hnextR)
        simpa only [B_lt_B_iff_square (by omega : i < i + 1) hnextR, not_lt] using hn
      apply le_of_not_gt
      rw [B_lt_B_iff_square hij hjr]
      have hjR : (i : ℝ) + 1 ≤ j := by exact_mod_cast (by omega : i + 1 ≤ j)
      have hirR : (i : ℝ) < r := by exact_mod_cast hir
      simp only [Nat.cast_add, Nat.cast_one] at hlocal
      have hmul := mul_nonneg (mul_nonneg (by linarith : 0 ≤ (r : ℝ) - i)
        (by linarith : 0 ≤ (j : ℝ) - (i + 1))) (sq_nonneg x)
      nlinarith

theorem A_sub_B_one {r : ℕ} (hr : 3 ≤ r) (x : ℝ) :
    A r x - B r 1 x = x * ((4 * (r : ℝ) - 3) * x - 2) / (2 * ((r : ℝ) - 1)) := by
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hrm1 : 0 < (r : ℝ) - 1 := by linarith
  have hrm2 : 0 < (r : ℝ) - 2 := by linarith
  have hden : (r : ℝ) - 1 ≠ 0 := by linarith
  unfold A B
  norm_num only [Nat.cast_one]
  field_simp
  <;> ring

theorem A_sub_B_two {r : ℕ} (hr : 3 ≤ r) (x : ℝ) :
    A r x - B r 2 x = (2 * ((r : ℝ) - 1) * x - 1) ^ 2 /
      (2 * ((r : ℝ) - 2) * ((r : ℝ) - 1)) := by
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hrm1 : 0 < (r : ℝ) - 1 := by linarith
  have hrm2 : 0 < (r : ℝ) - 2 := by linarith
  have hden1 : (r : ℝ) - 1 ≠ 0 := by linarith
  have hden2 : (r : ℝ) - 2 ≠ 0 := by linarith
  unfold A B
  norm_num only [Nat.cast_ofNat]
  field_simp
  <;> ring

theorem B_two_le_A {r : ℕ} (hr : 3 ≤ r) (x : ℝ) : B r 2 x ≤ A r x := by
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hrm1 : 0 < (r : ℝ) - 1 := by linarith
  have hrm2 : 0 < (r : ℝ) - 2 := by linarith
  have h := div_nonneg (sq_nonneg (2 * ((r : ℝ) - 1) * x - 1))
    (by positivity : 0 ≤ 2 * ((r : ℝ) - 2) * ((r : ℝ) - 1))
  rw [← A_sub_B_two hr] at h
  linarith

theorem A_eq_B_one_iff {r : ℕ} (hr : 3 ≤ r) (x : ℝ) :
    A r x = B r 1 x ↔ x = 0 ∨ x = AStart r := by
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hrm1 : 0 < (r : ℝ) - 1 := by linarith
  have hrm2 : 0 < (r : ℝ) - 2 := by linarith
  have hden : 2 * ((r : ℝ) - 1) ≠ 0 := by positivity
  have hcoef : 4 * (r : ℝ) - 3 ≠ 0 := by linarith
  rw [← sub_eq_zero, A_sub_B_one hr, div_eq_zero_iff, or_iff_left hden, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · right
      unfold AStart
      apply (eq_div_iff hcoef).mpr
      linarith
  · rintro (rfl | h)
    · exact Or.inl rfl
    · right
      rw [h]
      unfold AStart
      field_simp
      <;> ring

theorem A_eq_B_two_iff {r : ℕ} (hr : 3 ≤ r) (x : ℝ) :
    A r x = B r 2 x ↔ x = AEnd r := by
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hrm1 : 0 < (r : ℝ) - 1 := by linarith
  have hrm2 : 0 < (r : ℝ) - 2 := by linarith
  have hden : 2 * ((r : ℝ) - 2) * ((r : ℝ) - 1) ≠ 0 := by positivity
  have hcoef : 2 * ((r : ℝ) - 1) ≠ 0 := by positivity
  rw [← sub_eq_zero, A_sub_B_two hr, div_eq_zero_iff, or_iff_left hden, sq_eq_zero_iff]
  unfold AEnd
  constructor
  · intro h
    apply (eq_div_iff hcoef).mpr
    linarith
  · intro h
    rw [h]
    field_simp [ne_of_gt hrm1]
    <;> ring

theorem A_le_B_one_iff {r : ℕ} (hr : 3 ≤ r) {x : ℝ} (hx : 0 ≤ x) :
    A r x ≤ B r 1 x ↔ x ≤ AStart r := by
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hrm1 : 0 < (r : ℝ) - 1 := by linarith
  have hrm2 : 0 < (r : ℝ) - 2 := by linarith
  have hden : 0 < 2 * ((r : ℝ) - 1) := by positivity
  have hcoef : 0 < 4 * (r : ℝ) - 3 := by linarith
  rw [← sub_nonpos, A_sub_B_one hr, div_le_iff₀ hden, zero_mul]
  unfold AStart
  rw [le_div_iff₀ hcoef]
  constructor
  · intro h
    nlinarith
  · intro h
    have hm := mul_nonpos_of_nonneg_of_nonpos hx (by nlinarith : (4 * (r : ℝ) - 3) * x - 2 ≤ 0)
    exact hm

theorem B_one_le_A_iff {r : ℕ} (hr : 3 ≤ r) {x : ℝ} (hx : 0 ≤ x) :
    B r 1 x ≤ A r x ↔ x = 0 ∨ AStart r ≤ x := by
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hrm1 : 0 < (r : ℝ) - 1 := by linarith
  have hrm2 : 0 < (r : ℝ) - 2 := by linarith
  have hden : 0 < 2 * ((r : ℝ) - 1) := by positivity
  have hcoef : 0 < 4 * (r : ℝ) - 3 := by linarith
  rw [← sub_nonneg, A_sub_B_one hr, le_div_iff₀ hden, zero_mul]
  unfold AStart
  rw [div_le_iff₀ hcoef]
  constructor
  · intro h
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    · right
      have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
      have hfactor := nonneg_of_mul_nonneg_right h hxpos
      nlinarith
  · rintro (rfl | h)
    · simp
    · exact mul_nonneg hx (by nlinarith)

theorem AStart_lt_AEnd {r : ℕ} (hr : 3 ≤ r) : AStart r < AEnd r := by
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hrm1 : 0 < (r : ℝ) - 1 := by linarith
  have hrm2 : 0 < (r : ℝ) - 2 := by linarith
  unfold AStart AEnd
  apply (div_lt_div_iff₀ (by linarith : 0 < 4 * (r : ℝ) - 3) (by positivity)).mpr
  linarith

/-- While `A` is admissible, no ordinary branch after `B₂` can intervene. -/
theorem B_le_B_two_on_ADomain {r j : ℕ} (hr : 3 ≤ r) (hj : 2 ≤ j) (hjr : j < r)
    {x : ℝ} (hx : ADomain r x) : B r j x ≤ B r 2 x := by
  by_cases hj2 : j = 2
  · subst j
    exact le_rfl
  have hj2' : 2 < j := by omega
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hrm1 : 0 < (r : ℝ) - 1 := by linarith
  have hrm2 : 0 < (r : ℝ) - 2 := by linarith
  have hjR : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have hjrR : (j : ℝ) < r := by exact_mod_cast hjr
  have hxcoef := (le_div_iff₀ (by positivity : 0 < 2 * ((r : ℝ) - 1))).mp hx.2
  have hell : (r : ℝ) - 2 ≥ 0 := by linarith
  have hbase : 0 ≤ ((r : ℝ) - 2) * x := mul_nonneg hell hx.1
  have hgap : ((r : ℝ) - 2) * x ≤ 1 - (r : ℝ) * x := by nlinarith
  have hsq : (((r : ℝ) - 2) * x) ^ 2 ≤ (1 - (r : ℝ) * x) ^ 2 := by nlinarith
  have hmul := mul_nonneg (mul_nonneg hell (by linarith : 0 ≤ (j : ℝ) - 2)) (sq_nonneg x)
  apply le_of_not_gt
  rw [B_lt_B_iff_square hj2' hjr]
  norm_num only [Nat.cast_ofNat]
  nlinarith

theorem B_one_dominates_before_A {r : ℕ} (hr : 3 ≤ r) {x : ℝ}
    (hx0 : 0 ≤ x) (hx : x ≤ AStart r) :
    ∀ j, 1 ≤ j → j < r → B r j x ≤ B r 1 x := by
  apply (B_dominates_iff_adjacent le_rfl (by omega) x).mpr
  refine ⟨by omega, ?_⟩
  intro _
  exact (B_two_le_A hr x).trans ((A_le_B_one_iff hr hx0).mpr hx)

theorem A_dominates_on_middle_interval {r : ℕ} (hr : 3 ≤ r) {x : ℝ}
    (hx : ADomain r x) (hxl : AStart r ≤ x) :
    ∀ j, 1 ≤ j → j < r → B r j x ≤ A r x := by
  intro j hj hjr
  by_cases hj1 : j = 1
  · subst j
    exact (B_one_le_A_iff hr hx.1).mpr (Or.inr hxl)
  · exact (B_le_B_two_on_ADomain hr (by omega) hjr hx).trans (B_two_le_A hr x)

theorem BCrossing_pos {r i j : ℕ} (hr : 0 < r) : 0 < BCrossing r i j := by
  unfold BCrossing
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  positivity

theorem BCrossing_lt_right_endpoint {r i j : ℕ} (hi : i < r) (hj : j < r) :
    BCrossing r i j < 1 / (r : ℝ) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hiR : (i : ℝ) < r := by exact_mod_cast hi
  have hjR : (j : ℝ) < r := by exact_mod_cast hj
  have hp : 0 < ((r : ℝ) - i) * ((r : ℝ) - j) := mul_pos (by linarith) (by linarith)
  have hs := Real.sqrt_pos.mpr hp
  unfold BCrossing
  apply (div_lt_div_iff₀ (by positivity : 0 < (r : ℝ) + Real.sqrt (((r : ℝ) - i) * ((r : ℝ) - j))) hrR).mpr
  linarith

/-- Consecutive ordinary crossings occur in strictly increasing order. -/
theorem BCrossing_adjacent_strict {r i : ℕ} (hi : i + 2 < r) :
    BCrossing r i (i + 1) < BCrossing r (i + 1) (i + 2) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hiR : (i : ℝ) + 2 < r := by exact_mod_cast hi
  have hprod0 : 0 ≤ ((r : ℝ) - (i + 1)) * ((r : ℝ) - (i + 2)) :=
    mul_nonneg (by linarith) (by linarith)
  have hprod : ((r : ℝ) - (i + 1)) * ((r : ℝ) - (i + 2)) <
      ((r : ℝ) - i) * ((r : ℝ) - (i + 1)) := by nlinarith
  have hs := Real.sqrt_lt_sqrt hprod0 hprod
  unfold BCrossing
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
  linarith

/-- An ordinary branch is maximal exactly between its adjacent crossing
parameters, with the expected missing condition at either endpoint index. -/
theorem B_dominates_iff_crossing_interval {r i : ℕ} (hi : 1 ≤ i) (hir : i < r)
    {x : ℝ} (hx0 : 0 ≤ x) (hxr : x ≤ 1 / (r : ℝ)) :
    (∀ j, 1 ≤ j → j < r → B r j x ≤ B r i x) ↔
      (1 < i → BCrossing r (i - 1) i ≤ x) ∧
      (i + 1 < r → x ≤ BCrossing r i (i + 1)) := by
  rw [B_dominates_iff_adjacent hi hir]
  constructor
  · rintro ⟨hp, hn⟩
    refine ⟨fun h => (B_le_B_iff_crossing (by omega) hir hx0 hxr).mp (hp h), ?_⟩
    intro h
    have hs : ¬ B r i x < B r (i + 1) x := not_lt_of_ge (hn h)
    simpa only [B_lt_B_iff_crossing (by omega : i < i + 1) h hx0 hxr, not_lt] using hs
  · rintro ⟨hp, hn⟩
    refine ⟨fun h => (B_le_B_iff_crossing (by omega) hir hx0 hxr).mpr (hp h), ?_⟩
    intro h
    apply le_of_not_gt
    rw [B_lt_B_iff_crossing (by omega) h hx0 hxr]
    exact not_lt_of_ge (hn h)

/-- Two nonconsecutive ordinary branches cannot both attain the envelope. -/
theorem ordinary_active_indices_adjacent {r i j : ℕ} (hi : 1 ≤ i) (hij : i < j)
    (hjr : j < r) {x : ℝ} (hx0 : 0 ≤ x) (hxr : x ≤ 1 / (r : ℝ))
    (hiMax : ∀ k, 1 ≤ k → k < r → B r k x ≤ B r i x)
    (heq : B r i x = B r j x) : j = i + 1 := by
  by_contra hn
  have hgap : i + 1 < j := by omega
  have hcross := (B_eq_B_iff_crossing hij hjr hx0 hxr).mp heq
  have hxpos : 0 < x := hcross ▸ BCrossing_pos (by omega)
  have hx2 : 0 < x ^ 2 := sq_pos_of_pos hxpos
  have hlocal := hiMax (i + 1) (by omega) (by omega)
  have hsquare : (1 - (r : ℝ) * x) ^ 2 =
      (((r : ℝ) - i) * ((r : ℝ) - j)) * x ^ 2 := by
    have hle := (B_le_B_iff_square hij hjr x).mp heq.le
    have hn : ¬ B r i x < B r j x := not_lt_of_ge heq.ge
    rw [B_lt_B_iff_square hij hjr, not_lt] at hn
    exact le_antisymm hle hn
  have hni : ¬ B r i x < B r (i + 1) x := not_lt_of_ge hlocal
  rw [B_lt_B_iff_square (by omega : i < i + 1) (by omega), not_lt] at hni
  simp only [Nat.cast_add, Nat.cast_one] at hni
  have hjR : (i : ℝ) + 1 < j := by exact_mod_cast hgap
  have hirR : (i : ℝ) < r := by exact_mod_cast (hij.trans hjr)
  have hprod := mul_pos (mul_pos (by linarith : 0 < (r : ℝ) - i)
    (by linarith : 0 < (j : ℝ) - (i + 1))) hx2
  nlinarith

theorem AEnd_tangent {r : ℕ} (hr : 3 ≤ r) : A r (AEnd r) = B r 2 (AEnd r) :=
  A_tangent_eq_B_two hr

/-- The exclusion of later ordinary branches on the `A` domain is strict. -/
theorem B_lt_B_two_on_ADomain {r j : ℕ} (hr : 3 ≤ r) (hj : 2 < j) (hjr : j < r)
    {x : ℝ} (hx : ADomain r x) : B r j x < B r 2 x := by
  apply lt_of_not_ge
  rw [B_le_B_iff_square hj hjr]
  intro h
  by_cases hx0 : x = 0
  · norm_num [hx0] at h
  have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hjR : (2 : ℝ) < j := by exact_mod_cast hj
  have hrm1 : 0 < (r : ℝ) - 1 := by linarith
  have hrm2 : 0 < (r : ℝ) - 2 := by linarith
  have hxcoef := (le_div_iff₀ (by positivity : 0 < 2 * ((r : ℝ) - 1))).mp hx.2
  have hbase : 0 ≤ ((r : ℝ) - 2) * x := mul_nonneg hrm2.le hx.1
  have hgap : ((r : ℝ) - 2) * x ≤ 1 - (r : ℝ) * x := by nlinarith
  have hsq : (((r : ℝ) - 2) * x) ^ 2 ≤ (1 - (r : ℝ) * x) ^ 2 := by nlinarith
  have hmul := mul_pos (mul_pos hrm2 (by linarith : 0 < (j : ℝ) - 2)) (sq_pos_of_pos hxpos)
  norm_num only [Nat.cast_ofNat] at h
  nlinarith

theorem AEnd_lt_next_BCrossing {r : ℕ} (hr : 4 ≤ r) :
    AEnd r < BCrossing r 2 3 := by
  have hxA : ADomain r (AEnd r) := ⟨A_endpoint_nonneg (by omega), le_rfl⟩
  have hlt := B_lt_B_two_on_ADomain (by omega : 3 ≤ r) (by omega : 2 < 3) (by omega : 3 < r) hxA
  have hzero : 0 ≤ AEnd r := A_endpoint_nonneg (by omega)
  have hright : AEnd r ≤ 1 / (r : ℝ) := A_endpoint_le (by omega)
  apply lt_of_not_ge
  intro h
  have hle := (B_le_B_iff_crossing (by omega : 2 < 3) (by omega : 3 < r) hzero hright).mpr h
  exact not_lt_of_ge hle hlt

/-- The square-root deficiency equation is equivalent to the actual branch
intersection on the parameter interval. -/
theorem B_eq_B_iff_sqrt_equation {r i j : ℕ} (hi : i < r) (hj : j < r)
    {x : ℝ} (hx0 : 0 ≤ x) (hxr : x ≤ 1 / (r : ℝ)) :
    B r i x = B r j x ↔
      (1 - (i : ℝ) * x) / Real.sqrt ((r : ℝ) - i) =
        (1 - (j : ℝ) * x) / Real.sqrt ((r : ℝ) - j) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hiR : (i : ℝ) < r := by exact_mod_cast hi
  have hjR : (j : ℝ) < r := by exact_mod_cast hj
  have hxbound := (le_div_iff₀ hr0).mp hxr
  have hni : 0 ≤ 1 - (i : ℝ) * x := by nlinarith
  have hnj : 0 ≤ 1 - (j : ℝ) * x := by nlinarith
  have hdi : 0 ≤ (1 - (i : ℝ) * x) / Real.sqrt ((r : ℝ) - i) :=
    div_nonneg hni (Real.sqrt_nonneg _)
  have hdj : 0 ≤ (1 - (j : ℝ) * x) / Real.sqrt ((r : ℝ) - j) :=
    div_nonneg hnj (Real.sqrt_nonneg _)
  have hsi : ((1 - (i : ℝ) * x) / Real.sqrt ((r : ℝ) - i)) ^ 2 =
      (1 - (i : ℝ) * x) ^ 2 / ((r : ℝ) - i) := by
    rw [div_pow, Real.sq_sqrt (by linarith)]
  have hsj : ((1 - (j : ℝ) * x) / Real.sqrt ((r : ℝ) - j)) ^ 2 =
      (1 - (j : ℝ) * x) ^ 2 / ((r : ℝ) - j) := by
    rw [div_pow, Real.sq_sqrt (by linarith)]
  unfold B
  constructor <;> intro h <;> nlinarith

theorem adjacent_crossing_equation_iff {r i : ℕ} (hi : i + 1 < r)
    {x : ℝ} (hx0 : 0 ≤ x) (hxr : x ≤ 1 / (r : ℝ)) :
    (1 - (i : ℝ) * x) / Real.sqrt ((r : ℝ) - i) =
      (1 - ((i + 1 : ℕ) : ℝ) * x) / Real.sqrt ((r : ℝ) - (i + 1 : ℕ)) ↔
        x = BCrossing r i (i + 1) := by
  rw [← B_eq_B_iff_sqrt_equation (by omega) hi hx0 hxr]
  exact B_eq_B_iff_crossing (by omega) hi hx0 hxr

/-- The first ordinary crossing lies strictly inside the exceptional `A`
interval, which is why it is never an active ordinary intersection. -/
theorem first_BCrossing_between_A_endpoints {r : ℕ} (hr : 3 ≤ r) :
    AStart r < BCrossing r 1 2 ∧ BCrossing r 1 2 < AEnd r := by
  have hstart0 : 0 ≤ AStart r := by
    have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
    exact le_of_lt (div_pos (by norm_num) (by linarith))
  have hend0 : 0 ≤ AEnd r := A_endpoint_nonneg (by omega)
  have hendr : AEnd r ≤ 1 / (r : ℝ) := A_endpoint_le (by omega)
  have hstartr : AStart r ≤ 1 / (r : ℝ) := (AStart_lt_AEnd hr).le.trans hendr
  constructor
  · have hAB1 : A r (AStart r) = B r 1 (AStart r) :=
      (A_eq_B_one_iff hr _).mpr (Or.inr rfl)
    have hB2A : B r 2 (AStart r) < A r (AStart r) := by
      apply lt_of_le_of_ne (B_two_le_A hr _)
      intro h
      exact (AStart_lt_AEnd hr).ne ((A_eq_B_two_iff hr _).mp h.symm)
    have hn : ¬ B r 1 (AStart r) ≤ B r 2 (AStart r) := by rw [← hAB1]; exact not_le_of_gt hB2A
    rw [B_le_B_iff_crossing (by omega : 1 < 2) (by omega) hstart0 hstartr, not_le] at hn
    exact hn
  · have hB1A : B r 1 (AEnd r) < A r (AEnd r) := by
      apply lt_of_le_of_ne ((B_one_le_A_iff hr hend0).mpr (Or.inr (AStart_lt_AEnd hr).le))
      intro h
      rcases (A_eq_B_one_iff hr _).mp h.symm with h | h
      · have hp : 0 < AEnd r := lt_of_le_of_lt hstart0 (AStart_lt_AEnd hr)
        exact hp.ne' h
      · exact (AStart_lt_AEnd hr).ne h.symm
    rw [AEnd_tangent hr] at hB1A
    exact (B_lt_B_iff_crossing (by omega : 1 < 2) (by omega) hend0 hendr).mp hB1A

end DensityHS
