module

public import DensityHS.Constructions.OrdinaryAlignment
public import DensityHS.Constructions.ExceptionalKernel
public import DensityHS.Basic.PhaseActive

/-!
# Exact model coincidence at the exceptional endpoint

Author and maintainer: Xizhi Liu.

At the right endpoint of the A domain its zero cell has measure zero.
The remaining measurable cells form exactly the B2 construction. The
identity below is in the actual cut-distance quotient.
-/

@[expose] public section

namespace DensityHS.Constructions

open MeasureTheory Set Filter

def collapseExceptional {t : ℕ} : Option (Option (Fin t)) → Option (Fin t)
  | none => none
  | some none => none
  | some (some i) => some i

theorem collapseExceptional_some_iff {t : ℕ} (u : Option (Option (Fin t))) (i : Fin t) :
    collapseExceptional u = some i ↔ u = some (some i) := by
  rcases u with _ | (_ | j) <;> simp [collapseExceptional]

theorem exceptionalTemplate_collapse {t : ℕ} (u v : Option (Option (Fin t)))
    (hu : u ≠ some none) (hv : v ≠ some none) :
    (exceptionalTemplate t).entry u v =
      (ordinaryTemplate t).entry (collapseExceptional u) (collapseExceptional v) := by
  classical
  rcases u with _ | (_ | i) <;> rcases v with _ | (_ | j) <;>
    simp_all [exceptionalTemplate, exceptionalDefect, ordinaryTemplate, collapseExceptional]

theorem exceptionalGraphon_at_end {r : ℕ} (hr : 3 ≤ r) :
    exceptionalGraphon r (AEnd r) = ordinaryGraphon r 2 (AEnd r) := by
  classical
  letI : MeasurableSpace (Option (Option (Fin (r - 2)))) := ⊤
  let p := exceptionalWeight (r - 2) (AEnd r)
  have hx : ADomain r (AEnd r) := ⟨A_endpoint_nonneg (by omega), le_rfl⟩
  have hp : IsProbabilityWeight p := exceptionalWeight_admissible (by omega) hx
  let label := intervalLabel p
  let C : Fin (r - 2) → Set ℝ := fun j => {x | label x = some (some j)}
  have hr1 : (0 : ℝ) < (r : ℝ) - 1 := by
    have : (3 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  have hr2 : (0 : ℝ) < (r : ℝ) - 2 := by
    have : (3 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  have hrr : ((r - 2 : ℕ) : ℝ) + 1 = (r : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 2 ≤ r)]
    norm_num
    ring
  have hzero : unitMeasure.real {x | label x = some none} = 0 := by
    rw [intervalLabel_mass hp]
    change 1 / (((r - 2 : ℕ) : ℝ) + 1) - 2 * AEnd r = 0
    rw [hrr, AEnd]
    field_simp
    ring
  have hazero : ∀ᵐ x ∂unitMeasure, label x ≠ some none := by
    exact measure_eq_zero_iff_ae_notMem.mp ((measureReal_eq_zero_iff).mp hzero)
  let P : Graphon.OrdinaryPartition r 2 (AEnd r) (exceptionalKernel r (AEnd r)) unitMeasure :=
    { Index := Fin (r - 2)
      fintype := inferInstance
      cardinality := by simp
      block := C
      measurable := fun j => (measurable_intervalLabel p) (measurableSet_singleton _)
      disjoint := by
        intro i j hij
        apply Set.disjoint_left.mpr
        intro x hxi hxj
        have h : some (some i) = some (some j) := hxi.symm.trans hxj
        exact hij (Option.some.inj (Option.some.inj h))
      mass := by
        intro j
        rw [intervalLabel_mass hp]
        change 1 / (((r - 2 : ℕ) : ℝ) + 1) =
          (1 - (2 : ℝ) * AEnd r) / ((r - 2 : ℕ) : ℝ)
        rw [hrr, Nat.cast_sub (by omega : 2 ≤ r), Nat.cast_ofNat, AEnd]
        field_simp [hr1.ne', hr2.ne']
        ring
      independent := by
        intro j
        exact Eventually.of_forall fun z hxz hyz => by
          change (exceptionalTemplate (r - 2)).entry (label z.1) (label z.2) = 0
          rw [hxz, hyz]
          simp [exceptionalTemplate, exceptionalDefect]
      complete_outside := by
        filter_upwards [Measure.quasiMeasurePreserving_fst.ae hazero,
          Measure.quasiMeasurePreserving_snd.ae hazero] with z hxz hyz hnone
        change (exceptionalTemplate (r - 2)).entry (label z.1) (label z.2) = 1
        rw [exceptionalTemplate_collapse _ _ hxz hyz]
        apply ordinaryTemplate_entry_one_of_not_same
        rintro ⟨j, hxi, hyi⟩
        exact hnone ⟨j, (collapseExceptional_some_iff _ _).mp hxi,
          (collapseExceptional_some_iff _ _).mp hyi⟩ }
  exact P.graphon_eq (by omega) ⟨A_endpoint_nonneg (by omega), A_endpoint_le (by omega)⟩

end DensityHS.Constructions

