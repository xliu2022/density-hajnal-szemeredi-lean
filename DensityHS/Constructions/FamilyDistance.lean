module

public import DensityHS.Constructions.CompactFamilies
public import DensityHS.Constructions.Alignment

/-!
# Uniform cut-to-edit control for every construction kernel

Author and maintainer: Xizhi Liu.

Every model has at most 2r-1 cells and a binary template. The actual
cut-distance bound therefore controls its infimum L1 distance over
measure-preserving measurable bijections with one common coefficient.
-/

@[expose] public section

namespace DensityHS.Constructions

open MeasureTheory

theorem ordinaryTemplate_binary (s : ℕ) (u v : Option (Fin s)) :
    (ordinaryTemplate s).entry u v = 0 ∨ (ordinaryTemplate s).entry u v = 1 := by
  classical
  cases u <;> cases v <;> simp [ordinaryTemplate] <;> split_ifs <;> simp_all

theorem exceptionalTemplate_binary (t : ℕ) (u v : Option (Option (Fin t))) :
    (exceptionalTemplate t).entry u v = 0 ∨ (exceptionalTemplate t).entry u v = 1 := by
  classical
  rcases u with _ | (_ | i) <;> rcases v with _ | (_ | j) <;>
    simp [exceptionalTemplate, exceptionalDefect] <;> split_ifs <;> simp_all

theorem finalTemplate_binary (s : ℕ) (u v : Option (Fin s × Bool)) :
    (finalTemplate s).entry u v = 0 ∨ (finalTemplate s).entry u v = 1 := by
  classical
  rcases u with _ | ⟨i, b⟩ <;> rcases v with _ | ⟨j, c⟩ <;>
    simp [finalTemplate, finalDefect] <;> split_ifs <;> simp_all

theorem FiniteTemplate.relabelL1_le_card_sq_cut {I : Type*} [Fintype I] [Nonempty I]
    (A : FiniteTemplate I) (hA : ∀ i j, A.entry i j = 0 ∨ A.entry i j = 1)
    (p : I → ℝ) (W : Graphon.Kernel ℝ) :
    Graphon.relabelL1Distance unitMeasure W (A.kernel p) ≤ (Fintype.card I : ℝ)^2 *
      Vendor.Graphon.cutDistance (W.toVendorGraphon unitMeasure)
        ((A.kernel p).toVendorGraphon unitMeasure) := by
  letI : MeasurableSpace I := ⊤
  exact Graphon.binary_step_relabelL1_le_card_sq_mul_cutDistance unitMeasure W (A.kernel p)
    (intervalLabel p) (fun i => (measurable_intervalLabel p) (measurableSet_singleton i))
    A.entry hA (fun _ _ => rfl)

theorem FiniteTemplate.relabelL1_le_bound_sq_cut {I : Type*} [Fintype I] [Nonempty I]
    (A : FiniteTemplate I) (hA : ∀ i j, A.entry i j = 0 ∨ A.entry i j = 1)
    (p : I → ℝ) (W : Graphon.Kernel ℝ) {m : ℕ} (hm : Fintype.card I ≤ m) :
    Graphon.relabelL1Distance unitMeasure W (A.kernel p) ≤ (m : ℝ)^2 *
      Vendor.Graphon.cutDistance (W.toVendorGraphon unitMeasure)
        ((A.kernel p).toVendorGraphon unitMeasure) := by
  apply (A.relabelL1_le_card_sq_cut hA p W).trans
  apply mul_le_mul_of_nonneg_right _ (Vendor.Graphon.cutDistance_nonneg _ _)
  have hmr : (Fintype.card I : ℝ) ≤ m := by exact_mod_cast hm
  nlinarith [(Nat.cast_nonneg (Fintype.card I) : (0 : ℝ) ≤ Fintype.card I),
    (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

/-- One quantitative coefficient works for all branches and all simplex
parameters, including zero-mass and merged-cell degenerations. -/
theorem construction_relabelL1_bound {r : ℕ} (hr : 2 ≤ r) (t : ConstructionKind r)
    (p : ℝ × (Fin (r - 1) → ℝ)) (W : Graphon.Kernel ℝ) :
    Graphon.relabelL1Distance unitMeasure W (constructionKernel r t p) ≤
      ((2 * r - 1 : ℕ) : ℝ)^2 *
        Vendor.Graphon.cutDistance (W.toVendorGraphon unitMeasure)
          ((constructionKernel r t p).toVendorGraphon unitMeasure) := by
  cases t with
  | ordinary i =>
    apply (ordinaryTemplate (r - (i.val + 1))).relabelL1_le_bound_sq_cut
      (ordinaryTemplate_binary _) _ W
    simp only [Fintype.card_option, Fintype.card_fin]
    omega
  | exceptional =>
    apply (exceptionalTemplate (r - 2)).relabelL1_le_bound_sq_cut
      (exceptionalTemplate_binary _) _ W
    simp only [Fintype.card_option, Fintype.card_fin]
    omega
  | final =>
    apply (finalTemplate (r - 1)).relabelL1_le_bound_sq_cut (finalTemplate_binary _) _ W
    simp only [Fintype.card_option, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    omega

end DensityHS.Constructions

