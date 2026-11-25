module

public import DensityHS.Constructions.FiniteTemplate
public import DensityHS.Basic.Envelope

/-!
# Concrete exceptional Turán-part graphons

Author and maintainer: Xizhi Liu.

The first Turán part is divided into a clique cell and its independent
remainder. All the other parts are independent and completely joined to it.
-/

@[expose] public section

namespace DensityHS.Constructions

open MeasureTheory Set

noncomputable def exceptionalDefect (t : ℕ) :
    Option (Option (Fin t)) → Option (Option (Fin t)) → ℝ := by
  classical
  exact fun u v => match u, v with
    | none, some none => 1
    | some none, none => 1
    | some none, some none => 1
    | some (some i), some (some j) => if i = j then 1 else 0
    | _, _ => 0

noncomputable def exceptionalTemplate (t : ℕ) : FiniteTemplate (Option (Option (Fin t))) where
  entry u v := 1 - exceptionalDefect t u v
  symmetric u v := by
    cases u with
    | none => cases v with
      | none => rfl
      | some v => cases v <;> rfl
    | some u => cases u with
      | none => cases v with
        | none => rfl
        | some v => cases v <;> rfl
      | some i => cases v with
        | none => rfl
        | some v => cases v <;> simp [exceptionalDefect, eq_comm]
  nonneg u v := by
    classical
    cases u with
    | none => cases v with
      | none => norm_num [exceptionalDefect]
      | some v => cases v <;> norm_num [exceptionalDefect]
    | some u => cases u with
      | none => cases v with
        | none => norm_num [exceptionalDefect]
        | some v => cases v <;> norm_num [exceptionalDefect]
      | some i => cases v with
        | none => norm_num [exceptionalDefect]
        | some v => cases v <;> simp [exceptionalDefect] <;> split_ifs <;> norm_num
  le_one u v := by
    classical
    cases u with
    | none => cases v with
      | none => norm_num [exceptionalDefect]
      | some v => cases v <;> norm_num [exceptionalDefect]
    | some u => cases u with
      | none => cases v with
        | none => norm_num [exceptionalDefect]
        | some v => cases v <;> norm_num [exceptionalDefect]
      | some i => cases v with
        | none => norm_num [exceptionalDefect]
        | some v => cases v <;> simp [exceptionalDefect] <;> split_ifs <;> norm_num

noncomputable def exceptionalWeight (t : ℕ) (x : ℝ) : Option (Option (Fin t)) → ℝ
  | none => 2 * x
  | some none => 1 / ((t : ℝ) + 1) - 2 * x
  | some (some _) => 1 / ((t : ℝ) + 1)

theorem exceptionalWeight_probability {t : ℕ} {x : ℝ}
    (hx : x ∈ Icc 0 (1 / (2 * ((t : ℝ) + 1)))) :
    IsProbabilityWeight (exceptionalWeight t x) := by
  have ht : (0 : ℝ) < (t : ℝ) + 1 := by positivity
  have hx2 : 2 * x ≤ 1 / ((t : ℝ) + 1) := by
    apply (le_div_iff₀ ht).mpr
    have h := (le_div_iff₀ (mul_pos (by norm_num) ht)).mp hx.2
    nlinarith
  refine ⟨?_, ?_⟩
  · intro i
    cases i with
    | none => exact mul_nonneg (by norm_num) hx.1
    | some i => cases i with
      | none => exact sub_nonneg.mpr hx2
      | some j => exact (one_div_pos.mpr ht).le
  · simp only [Fintype.sum_option, exceptionalWeight, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring

theorem exceptionalTemplate_density (t : ℕ) {p : Option (Option (Fin t)) → ℝ}
    (hp : IsProbabilityWeight p) :
    Graphon.density unitMeasure ((exceptionalTemplate t).kernel p) =
      (1 - (p none + p (some none)) ^ 2 -
        (∑ i : Fin t, (p (some (some i))) ^ 2) + (p none) ^ 2) / 2 := by
  classical
  rw [FiniteTemplate.density _ hp]
  congr 1
  change (∑ u, ∑ v, p u * p v * (1 - exceptionalDefect t u v)) = _
  simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib]
  have hfirst : (∑ u, ∑ v, p u * p v) = 1 := by
    simp_rw [← Finset.mul_sum, hp.2, mul_one]
    exact hp.2
  rw [hfirst]
  have hdiag : (∑ u, ∑ v, p u * p v * exceptionalDefect t u v) =
      2 * p none * p (some none) + (p (some none)) ^ 2 +
        ∑ i : Fin t, (p (some (some i))) ^ 2 := by
    simp [Fintype.sum_option, exceptionalDefect, mul_ite, sq]
    ring
  rw [hdiag]
  ring

noncomputable def exceptionalKernel (r : ℕ) (x : ℝ) : Graphon.Kernel ℝ :=
  (exceptionalTemplate (r - 2)).kernel (exceptionalWeight (r - 2) x)

noncomputable def exceptionalGraphon (r : ℕ) (x : ℝ) :
    Vendor.GraphonSpace ℝ unitMeasure :=
  (exceptionalTemplate (r - 2)).graphon (exceptionalWeight (r - 2) x)

theorem exceptionalWeight_admissible {r : ℕ} (hr : 2 ≤ r) {x : ℝ}
    (hx : ADomain r x) : IsProbabilityWeight (exceptionalWeight (r - 2) x) := by
  apply exceptionalWeight_probability
  have hcast : ((r - 2 : ℕ) : ℝ) + 1 = (r : ℝ) - 1 := by
    rw [Nat.cast_sub hr]
    norm_num
    ring
  simpa only [hcast, Set.mem_Icc, ADomain] using hx

theorem density_exceptionalKernel {r : ℕ} (hr : 2 ≤ r) {x : ℝ}
    (hx : ADomain r x) :
    Graphon.density unitMeasure (exceptionalKernel r x) = A r x := by
  have hrp : (0 : ℝ) < (r : ℝ) - 1 := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  have hrr : (r : ℝ) - 2 + 1 = (r : ℝ) - 1 := by ring
  rw [exceptionalKernel, exceptionalTemplate_density _ (exceptionalWeight_admissible hr hx)]
  simp only [exceptionalWeight, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub hr, Nat.cast_ofNat, hrr, A]
  field_simp [ne_of_gt hrp]
  <;> ring

theorem continuous_exceptionalWeight (t : ℕ) : Continuous (exceptionalWeight t) := by
  apply continuous_pi
  intro i
  cases i with
  | none => simp only [exceptionalWeight]; fun_prop
  | some i => cases i <;> simp only [exceptionalWeight] <;> fun_prop

theorem continuous_exceptionalGraphon (r : ℕ) : Continuous (exceptionalGraphon r) :=
  (exceptionalTemplate (r - 2)).continuous_graphon.comp (continuous_exceptionalWeight (r - 2))

end DensityHS.Constructions
