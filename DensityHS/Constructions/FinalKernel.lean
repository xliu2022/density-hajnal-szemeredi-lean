module

public import DensityHS.Constructions.FiniteTemplate
public import DensityHS.Basic.Envelope

/-!
# Concrete simplex family of final extremal graphons

Author and maintainer: Xizhi Liu.

Each independent part has mass `L`. Its `true` subcell is the portion
anticomplete to the clique cell. The simplex parameter specifies the
relative sizes of these portions, including all boundary degenerations.
-/

@[expose] public section

namespace DensityHS.Constructions

open MeasureTheory Set

noncomputable def finalDefect (s : ℕ) :
    Option (Fin s × Bool) → Option (Fin s × Bool) → ℝ := by
  classical
  exact fun u v => match u, v with
    | none, none => 0
    | none, some (_, b) => if b then 1 else 0
    | some (_, b), none => if b then 1 else 0
    | some (i, _), some (j, _) => if i = j then 1 else 0

noncomputable def finalTemplate (s : ℕ) : FiniteTemplate (Option (Fin s × Bool)) where
  entry u v := 1 - finalDefect s u v
  symmetric u v := by
    cases u with
    | none => cases v with
      | none => rfl
      | some v => rcases v with ⟨j, b⟩; cases b <;> rfl
    | some u => rcases u with ⟨i, b⟩
                cases v with
                | none => cases b <;> rfl
                | some v => rcases v with ⟨j, c⟩; simp only [finalDefect, eq_comm]
  nonneg u v := by
    classical
    cases u <;> cases v <;> simp [finalDefect] <;> split_ifs <;> norm_num
  le_one u v := by
    classical
    cases u <;> cases v <;> simp [finalDefect] <;> split_ifs <;> norm_num

noncomputable def finalWeight (s : ℕ) (L : ℝ) (z : Fin s → ℝ) :
    Option (Fin s × Bool) → ℝ
  | none => 1 - s * L
  | some (j, b) => if b then z j * L else (1 - z j) * L

theorem probabilityWeight_le_one {I : Type*} [Fintype I] {z : I → ℝ}
    (hz : IsProbabilityWeight z) (i : I) : z i ≤ 1 := by
  classical
  have h := Finset.single_le_sum (fun j _ => hz.1 j) (Finset.mem_univ i)
  exact h.trans_eq hz.2

theorem finalWeight_probability {s : ℕ} {L : ℝ} {z : Fin s → ℝ}
    (hL : 0 ≤ L) (hsL : (s : ℝ) * L ≤ 1) (hz : IsProbabilityWeight z) :
    IsProbabilityWeight (finalWeight s L z) := by
  refine ⟨?_, ?_⟩
  · intro u
    cases u with
    | none => exact sub_nonneg.mpr hsL
    | some u => rcases u with ⟨j, b⟩
                cases b
                · exact mul_nonneg (sub_nonneg.mpr (probabilityWeight_le_one hz j)) hL
                · exact mul_nonneg (hz.1 j) hL
  · simp only [Fintype.sum_option, Fintype.sum_prod_type, Fintype.sum_bool,
      finalWeight, Bool.false_eq_true, ↓reduceIte]
    have hterm (j : Fin s) : z j * L + (1 - z j) * L = L := by ring
    simp_rw [hterm]
    simp

theorem finalTemplate_density (s : ℕ) {p : Option (Fin s × Bool) → ℝ}
    (hp : IsProbabilityWeight p) :
    Graphon.density unitMeasure ((finalTemplate s).kernel p) =
      (1 - (∑ i : Fin s, (p (some (i, false)) + p (some (i, true))) ^ 2) -
        2 * p none * (∑ i : Fin s, p (some (i, true)))) / 2 := by
  classical
  rw [FiniteTemplate.density _ hp]
  congr 1
  change (∑ u, ∑ v, p u * p v * (1 - finalDefect s u v)) = _
  simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib]
  have hfirst : (∑ u, ∑ v, p u * p v) = 1 := by
    simp_rw [← Finset.mul_sum, hp.2, mul_one]
    exact hp.2
  rw [hfirst]
  have hdiag : (∑ u, ∑ v, p u * p v * finalDefect s u v) =
      (∑ i : Fin s, (p (some (i, false)) + p (some (i, true))) ^ 2) +
        2 * p none * (∑ i : Fin s, p (some (i, true))) := by
    simp only [Fintype.sum_option, Fintype.sum_prod_type, Fintype.sum_bool,
      finalDefect, Bool.false_eq_true, ↓reduceIte, mul_zero, add_zero,
      zero_add, mul_one, mul_ite, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.sum_ite_eq, Finset.sum_const_zero, Finset.mem_univ, ↓reduceIte]
    simp_rw [sq, add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
    ring
  rw [hdiag]
  ring

noncomputable def finalKernel (r : ℕ) (x : ℝ) (z : Fin (r - 1) → ℝ) : Graphon.Kernel ℝ :=
  (finalTemplate (r - 1)).kernel (finalWeight (r - 1) (1 - (r : ℝ) * x) z)

noncomputable def finalGraphon (r : ℕ) (x : ℝ) (z : Fin (r - 1) → ℝ) :
    Vendor.GraphonSpace ℝ unitMeasure :=
  (finalTemplate (r - 1)).graphon (finalWeight (r - 1) (1 - (r : ℝ) * x) z)

theorem finalWeight_admissible {r : ℕ} (hr : 2 ≤ r) {x : ℝ}
    (hx : RDomain r x) {z : Fin (r - 1) → ℝ} (hz : IsProbabilityWeight z) :
    IsProbabilityWeight (finalWeight (r - 1) (1 - (r : ℝ) * x) z) := by
  have hrp : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hr1 : (0 : ℝ) < (r : ℝ) - 1 := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  have hhi := (le_div_iff₀ hrp).mp hx.2
  have hlo := (div_le_iff₀ (mul_pos hrp hr1)).mp hx.1
  apply finalWeight_probability (by nlinarith) _ hz
  rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
  nlinarith

/-- The density is independent of every simplex coordinate. -/
theorem density_finalKernel {r : ℕ} (hr : 2 ≤ r) {x : ℝ}
    (hx : RDomain r x) {z : Fin (r - 1) → ℝ} (hz : IsProbabilityWeight z) :
    Graphon.density unitMeasure (finalKernel r x z) = R r x := by
  rw [finalKernel, finalTemplate_density _ (finalWeight_admissible hr hx hz)]
  have hterm (j : Fin (r - 1)) :
      finalWeight (r - 1) (1 - (r : ℝ) * x) z (some (j, false)) +
        finalWeight (r - 1) (1 - (r : ℝ) * x) z (some (j, true)) = 1 - (r : ℝ) * x := by
    simp [finalWeight]
    ring
  simp_rw [hterm]
  simp only [finalWeight, ↓reduceIte, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_mul, hz.2, one_mul,
    Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one, R]
  ring

theorem continuous_finalWeight (s : ℕ) :
    Continuous (fun p : ℝ × (Fin s → ℝ) => finalWeight s p.1 p.2) := by
  apply continuous_pi
  intro i
  cases i with
  | none => simp only [finalWeight]; fun_prop
  | some i => rcases i with ⟨j, b⟩
              cases b <;> simp only [finalWeight, Bool.false_eq_true, ↓reduceIte] <;> fun_prop

theorem continuous_finalGraphon (r : ℕ) :
    Continuous (fun p : ℝ × (Fin (r - 1) → ℝ) => finalGraphon r p.1 p.2) :=
  (finalTemplate (r - 1)).continuous_graphon.comp
    ((continuous_finalWeight (r - 1)).comp
      ((continuous_const.sub (continuous_const.mul continuous_fst)).prodMk continuous_snd))

end DensityHS.Constructions
