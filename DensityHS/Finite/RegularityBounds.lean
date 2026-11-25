module

public import DensityHS.Finite.EquitableRefinement

/-!
# Uniform bounds for the simultaneous energy iteration

Author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS.MatrixRegularity

def atomBound (k : ℕ) : ℕ := k * 2^(2*k^2)

theorem atomBound_mono : Monotone atomBound := by
  intro a b hab
  unfold atomBound
  gcongr

theorem atomBound_pos {k : ℕ} (hk : 0 < k) : 0 < atomBound k := by
  unfold atomBound
  positivity

theorem le_atomBound (k : ℕ) : k ≤ atomBound k := by
  unfold atomBound
  exact Nat.le_mul_of_pos_right _ (by positivity)

noncomputable def equalRefineBound (δ : ℝ) (k : ℕ) : ℕ :=
  ⌈(2/δ+1)*(k : ℝ)⌉₊

theorem le_equalRefineBound (δ : ℝ) (k : ℕ) :
    (2/δ+1)*(k : ℝ) ≤ (equalRefineBound δ k : ℝ) := Nat.le_ceil _

theorem nat_le_equalRefineBound {δ : ℝ} {k n : ℕ}
    (hn : (n : ℝ) ≤ (2/δ+1)*(k : ℝ)) : n ≤ equalRefineBound δ k := by
  exact_mod_cast hn.trans (le_equalRefineBound δ k)

noncomputable def regularitySizeBound (δ : ℝ) : ℕ → ℕ
  | 0 => max 1 (equalRefineBound δ 1)
  | i+1 => max (regularitySizeBound δ i) (equalRefineBound δ (atomBound (regularitySizeBound δ i)))

theorem regularitySizeBound_mono (δ : ℝ) : Monotone (regularitySizeBound δ) := by
  apply monotone_nat_of_le_succ
  intro i
  exact le_max_left _ _

theorem regularitySizeBound_pos (δ : ℝ) (i : ℕ) : 0 < regularitySizeBound δ i := by
  have hbase : 1 ≤ regularitySizeBound δ 0 := le_max_left _ _
  exact lt_of_lt_of_le (by omega : 0 < regularitySizeBound δ 0)
    (regularitySizeBound_mono δ (Nat.zero_le i))

theorem equalRefineBound_le_next (δ : ℝ) (i : ℕ) :
    equalRefineBound δ (atomBound (regularitySizeBound δ i)) ≤ regularitySizeBound δ (i+1) :=
  le_max_right _ _

noncomputable def regularityOrderThreshold (δ : ℝ) (T : ℕ) : ℕ :=
  max 1 ⌈2*(atomBound (regularitySizeBound δ T) : ℝ)/δ⌉₊

theorem regularityOrderThreshold_pos (δ : ℝ) (T : ℕ) : 0 < regularityOrderThreshold δ T := by
  have h : 1 ≤ regularityOrderThreshold δ T := le_max_left _ _
  omega

theorem regularityOrderThreshold_large {δ : ℝ} (hδ : 0 < δ) {T i n : ℕ}
    (hi : i ≤ T) (hn : regularityOrderThreshold δ T ≤ n) :
    2*(atomBound (regularitySizeBound δ i) : ℝ)/δ ≤ n := by
  calc
    _ ≤ 2*(atomBound (regularitySizeBound δ T) : ℝ)/δ := by
      gcongr
      exact atomBound_mono (regularitySizeBound_mono δ hi)
    _ ≤ (⌈2*(atomBound (regularitySizeBound δ T) : ℝ)/δ⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ (regularityOrderThreshold δ T : ℝ) := by
      exact_mod_cast (show ⌈2*(atomBound (regularitySizeBound δ T) : ℝ)/δ⌉₊ ≤
        regularityOrderThreshold δ T from le_max_right _ _)
    _ ≤ _ := by exact_mod_cast hn

noncomputable def energySteps (ε : ℝ) (c : ℕ) : ℕ := ⌊16*(c : ℝ)/ε^8⌋₊+1

theorem energySteps_pos (ε : ℝ) (c : ℕ) : 0 < energySteps ε c := Nat.succ_pos _

theorem energySteps_gain {ε : ℝ} (hε : 0 < ε) (c : ℕ) :
    (c : ℝ) < (energySteps ε c : ℝ)*(ε^8/16) := by
  have h := Nat.lt_floor_add_one (16*(c : ℝ)/ε^8)
  have hp : 0 < ε^8/16 := by positivity
  have hmul := mul_lt_mul_of_pos_right h hp
  have heq : (16*(c : ℝ)/ε^8)*(ε^8/16) = c := by field_simp
  rw [heq] at hmul
  simpa only [energySteps, Nat.cast_add, Nat.cast_one] using hmul

end DensityHS.MatrixRegularity
