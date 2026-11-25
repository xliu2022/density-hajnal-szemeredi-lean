module

public import DensityHS.Constructions.FiniteTemplate
public import DensityHS.Basic.Envelope

/-!
# Concrete ordinary extremal graphons

Author and maintainer: Xizhi Liu.

The `none` cell is a clique; the `some` cells are independent and are
completely joined to each other and to the clique cell.
-/

@[expose] public section

namespace DensityHS.Constructions

open MeasureTheory Set

/-- A clique joined to a complete multipartite graph. -/
noncomputable def ordinaryTemplate (s : ℕ) : FiniteTemplate (Option (Fin s)) := by
  classical
  exact
    { entry := fun u v => 1 - match u, v with
        | some i, some j => if i = j then 1 else 0
        | _, _ => 0
      symmetric := by
        intro u v
        cases u <;> cases v <;> simp [eq_comm]
      nonneg := by intro u v; cases u <;> cases v <;> simp <;> split_ifs <;> norm_num
      le_one := by intro u v; cases u <;> cases v <;> simp <;> split_ifs <;> norm_num }

/-- One clique cell of mass `a`, and `s` equal independent cells. -/
noncomputable def ordinaryWeight (s : ℕ) (a : ℝ) : Option (Fin s) → ℝ
  | none => a
  | some _ => (1 - a) / s

theorem ordinaryWeight_probability {s : ℕ} (hs : 0 < s) {a : ℝ}
    (ha : a ∈ Icc 0 1) : IsProbabilityWeight (ordinaryWeight s a) := by
  have hsp : (0 : ℝ) < s := by exact_mod_cast hs
  refine ⟨?_, ?_⟩
  · intro i
    cases i with
    | none => exact ha.1
    | some j => exact div_nonneg (sub_nonneg.mpr ha.2) hsp.le
  · simp only [Fintype.sum_option, ordinaryWeight, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring

theorem ordinaryTemplate_density (s : ℕ) {p : Option (Fin s) → ℝ}
    (hp : IsProbabilityWeight p) :
    Graphon.density unitMeasure ((ordinaryTemplate s).kernel p) =
      (1 - ∑ i : Fin s, (p (some i)) ^ 2) / 2 := by
  classical
  rw [FiniteTemplate.density _ hp]
  congr 1
  let d : Option (Fin s) → Option (Fin s) → ℝ := fun u v => match u, v with
    | some i, some j => if i = j then 1 else 0
    | _, _ => 0
  change (∑ u, ∑ v, p u * p v * (1 - d u v)) = _
  simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib]
  have hfirst : (∑ u, ∑ v, p u * p v) = 1 := by
    simp_rw [← Finset.mul_sum, hp.2, mul_one]
    exact hp.2
  have hdiag : (∑ u, ∑ v, p u * p v * d u v) = ∑ i : Fin s, (p (some i)) ^ 2 := by
    simp [Fintype.sum_option, d, mul_ite, sq]
  rw [hfirst, hdiag]

/-- The paper's `B_i` graphon, on a fixed atomless probability space. -/
noncomputable def ordinaryKernel (r i : ℕ) (x : ℝ) : Graphon.Kernel ℝ :=
  (ordinaryTemplate (r - i)).kernel (ordinaryWeight (r - i) ((i : ℝ) * x))

noncomputable def ordinaryGraphon (r i : ℕ) (x : ℝ) :
    Vendor.GraphonSpace ℝ unitMeasure :=
  (ordinaryTemplate (r - i)).graphon (ordinaryWeight (r - i) ((i : ℝ) * x))

theorem ordinaryWeight_admissible {r i : ℕ} (hir : i < r) {x : ℝ}
    (hx : x ∈ Icc 0 (1 / (r : ℝ))) :
    IsProbabilityWeight (ordinaryWeight (r - i) ((i : ℝ) * x)) := by
  have hr : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hi : (i : ℝ) ≤ r := by exact_mod_cast hir.le
  apply ordinaryWeight_probability (by omega)
  refine ⟨mul_nonneg (Nat.cast_nonneg _) hx.1, ?_⟩
  have h := (le_div_iff₀ hr).mp hx.2
  nlinarith

theorem density_ordinaryKernel {r i : ℕ} (hir : i < r) {x : ℝ}
    (hx : x ∈ Icc 0 (1 / (r : ℝ))) :
    Graphon.density unitMeasure (ordinaryKernel r i x) = B r i x := by
  have hs : (0 : ℝ) < (r - i : ℕ) := by exact_mod_cast (by omega : 0 < r - i)
  rw [ordinaryKernel, ordinaryTemplate_density _ (ordinaryWeight_admissible hir hx)]
  simp only [ordinaryWeight, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, B, ← Nat.cast_sub hir.le]
  field_simp
  <;> ring

theorem continuous_ordinaryWeight (s : ℕ) : Continuous (ordinaryWeight s) := by
  apply continuous_pi
  intro i
  cases i <;> simp only [ordinaryWeight] <;> fun_prop

theorem continuous_ordinaryGraphon (r i : ℕ) : Continuous (ordinaryGraphon r i) :=
  (ordinaryTemplate (r - i)).continuous_graphon.comp
    ((continuous_ordinaryWeight (r - i)).comp (continuous_const.mul continuous_id))

end DensityHS.Constructions
