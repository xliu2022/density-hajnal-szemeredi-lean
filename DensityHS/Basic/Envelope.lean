module

public import Mathlib

/-!
# The density envelope

The branch functions and their exact domains from Section 2 of
*The density Hajnal–Szemerédi theorem*.

Formalization author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS

/-- The `i`th clique-and-multipartite branch. -/
noncomputable def B (r i : ℕ) (x : ℝ) : ℝ :=
  (1 - (1 - (i : ℝ) * x) ^ 2 / ((r : ℝ) - i)) / 2

/-- The exceptional Turán-part branch. -/
noncomputable def A (r : ℕ) (x : ℝ) : ℝ :=
  ((r : ℝ) - 2) / (2 * ((r : ℝ) - 1)) + 2 * x ^ 2

/-- The final, simplex-parameterized branch. -/
noncomputable def R (r : ℕ) (x : ℝ) : ℝ :=
  1 / 2 - (1 - (r : ℝ) * x) + ((r : ℝ) - 1) / 2 * (1 - (r : ℝ) * x) ^ 2

/-- The matching envelope, used for the base of induction. -/
noncomputable def Phi2 (x : ℝ) : ℝ := max (x - x ^ 2 / 2) (2 * x ^ 2)

/-- The admissible domain of the exceptional branch. -/
def ADomain (r : ℕ) (x : ℝ) : Prop :=
  0 ≤ x ∧ x ≤ 1 / (2 * ((r : ℝ) - 1))

/-- The admissible domain of the final branch. -/
def RDomain (r : ℕ) (x : ℝ) : Prop :=
  ((r : ℝ) - 2) / ((r : ℝ) * ((r : ℝ) - 1)) ≤ x ∧ x ≤ 1 / (r : ℝ)

/-- Only admissible values occur: the restricted branches are omitted outside
their domains, rather than evaluated as unrestricted polynomials. -/
def branchValues (r : ℕ) (x : ℝ) : Set ℝ :=
  {y | (∃ i : ℕ, 1 ≤ i ∧ i < r ∧ y = B r i x) ∨
    (ADomain r x ∧ y = A r x) ∨ (RDomain r x ∧ y = R r x)}

/-- The paper's density envelope. Values at `r < 2` are irrelevant to the
theorems. -/
noncomputable def Phi (r : ℕ) (x : ℝ) : ℝ :=
  if r = 2 then Phi2 x else sSup (branchValues r x)

theorem branchValues_finite (r : ℕ) (x : ℝ) : (branchValues r x).Finite := by
  apply ((Set.finite_range (fun i : Fin r => B r i.val x)).union
    (Set.toFinite ({A r x, R r x} : Set ℝ))).subset
  intro y hy
  rcases hy with ⟨i, hi, hir, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact Or.inl ⟨⟨i, hir⟩, rfl⟩
  · exact Or.inr (by simp)
  · exact Or.inr (by simp)

theorem branchValues_nonempty {r : ℕ} (hr : 2 ≤ r) (x : ℝ) :
    (branchValues r x).Nonempty :=
  ⟨B r 1 x, Or.inl ⟨1, le_rfl, by omega, rfl⟩⟩

theorem branchValues_bddAbove (r : ℕ) (x : ℝ) : BddAbove (branchValues r x) :=
  (branchValues_finite r x).bddAbove

theorem Phi_eq_sSup {r : ℕ} (hr : 3 ≤ r) (x : ℝ) :
    Phi r x = sSup (branchValues r x) := by
  simp [Phi, show r ≠ 2 by omega]

@[simp] theorem Phi_two (x : ℝ) : Phi 2 x = Phi2 x := by simp [Phi]

theorem B_le_Phi {r i : ℕ} (hr : 3 ≤ r) (hi : 1 ≤ i) (hir : i < r) (x : ℝ) :
    B r i x ≤ Phi r x := by
  rw [Phi_eq_sSup hr]
  exact le_csSup (branchValues_bddAbove r x) (Or.inl ⟨i, hi, hir, rfl⟩)

theorem A_le_Phi {r : ℕ} (hr : 3 ≤ r) {x : ℝ} (hx : ADomain r x) :
    A r x ≤ Phi r x := by
  rw [Phi_eq_sSup hr]
  exact le_csSup (branchValues_bddAbove r x) (Or.inr (Or.inl ⟨hx, rfl⟩))

theorem R_le_Phi {r : ℕ} (hr : 3 ≤ r) {x : ℝ} (hx : RDomain r x) :
    R r x ≤ Phi r x := by
  rw [Phi_eq_sSup hr]
  exact le_csSup (branchValues_bddAbove r x) (Or.inr (Or.inr ⟨hx, rfl⟩))

theorem Phi_le {r : ℕ} (hr : 3 ≤ r) {x z : ℝ}
    (hB : ∀ i : ℕ, 1 ≤ i → i < r → B r i x ≤ z)
    (hA : ADomain r x → A r x ≤ z) (hR : RDomain r x → R r x ≤ z) :
    Phi r x ≤ z := by
  rw [Phi_eq_sSup hr]
  apply csSup_le (branchValues_nonempty (by omega) x)
  intro y hy
  rcases hy with ⟨i, hi, hir, rfl⟩ | ⟨hx, rfl⟩ | ⟨hx, rfl⟩
  · exact hB i hi hir
  · exact hA hx
  · exact hR hx

/-- Every value of the envelope is attained by an admissible branch. -/
theorem Phi_mem_branchValues {r : ℕ} (hr : 3 ≤ r) (x : ℝ) :
    Phi r x ∈ branchValues r x := by
  rw [Phi_eq_sSup hr]
  exact (branchValues_nonempty (by omega) x).csSup_mem (branchValues_finite r x)

theorem B_le_half {r i : ℕ} (hir : i < r) (x : ℝ) : B r i x ≤ 1 / 2 := by
  have hden : 0 < (r : ℝ) - i := by
    have h : (i : ℝ) < r := by exact_mod_cast hir
    linarith
  have hsq := div_nonneg (sq_nonneg (1 - (i : ℝ) * x)) (le_of_lt hden)
  unfold B
  linarith

theorem B_nonneg {r i : ℕ} (hr : 1 ≤ r) (hir : i < r)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / (r : ℝ)) : 0 ≤ B r i x := by
  have hrp : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hden : (1 : ℝ) ≤ (r : ℝ) - i := by
    have h : (i : ℝ) + 1 ≤ r := by exact_mod_cast (Nat.succ_le_of_lt hir)
    linarith
  have hix0 : 0 ≤ (i : ℝ) * x := mul_nonneg (Nat.cast_nonneg _) hx0
  have hrx : (r : ℝ) * x ≤ 1 := by
    have h := (le_div_iff₀ hrp).mp hx1
    nlinarith
  have hix1 : (i : ℝ) * x ≤ 1 := by
    have hi : (i : ℝ) ≤ r := by exact_mod_cast (Nat.le_of_lt hir)
    nlinarith
  have hnum : (1 - (i : ℝ) * x) ^ 2 ≤ (r : ℝ) - i := by nlinarith
  have hdiv : (1 - (i : ℝ) * x) ^ 2 / ((r : ℝ) - i) ≤ 1 :=
    (div_le_iff₀ (by linarith : 0 < (r : ℝ) - i)).mpr (by simpa using hnum)
  unfold B
  linarith

theorem Phi_nonneg {r : ℕ} (hr : 3 ≤ r) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / (r : ℝ)) : 0 ≤ Phi r x :=
  (B_nonneg (by omega) (by omega : 1 < r) hx0 hx1).trans
    (B_le_Phi hr le_rfl (by omega) x)

/-- The quadratic estimate completing a half-integral matching-cover proof. -/
theorem matching_mass_bound {x a : ℝ} (ha0 : 0 ≤ a) (hax : a ≤ x) :
    a - a ^ 2 / 2 + (2 * (x - a)) ^ 2 / 2 ≤ Phi2 x := by
  by_cases hx : x = 0
  · have ha : a = 0 := by linarith
    simp [hx, ha, Phi2]
  have hxp : 0 < x := lt_of_le_of_ne (ha0.trans hax) (Ne.symm hx)
  have haquad : a * (x - a) ≥ 0 := mul_nonneg ha0 (sub_nonneg.mpr hax)
  by_cases hc : x - x ^ 2 / 2 ≤ 2 * x ^ 2
  · have hcoef : 1 - 5 * x / 2 ≤ 0 := by
      have hp : x * (1 - 5 * x / 2) ≤ 0 := by nlinarith
      exact nonpos_of_mul_nonpos_right hp hxp
    have hprod := mul_nonpos_of_nonneg_of_nonpos ha0 hcoef
    apply le_trans _ (le_max_right _ _)
    nlinarith
  · have hcoef : 0 ≤ 1 - 5 * x / 2 := by nlinarith
    have hprod := mul_nonneg (sub_nonneg.mpr hax) hcoef
    apply le_trans _ (le_max_left _ _)
    nlinarith

theorem continuous_B (r i : ℕ) : Continuous (B r i) := by
  unfold B
  fun_prop

theorem continuous_A (r : ℕ) : Continuous (A r) := by
  unfold A
  fun_prop

theorem continuous_R (r : ℕ) : Continuous (R r) := by
  unfold R
  fun_prop

theorem continuous_Phi2 : Continuous Phi2 := by
  unfold Phi2
  fun_prop

theorem Phi2_monotoneOn : MonotoneOn Phi2 (Set.Icc 0 (1 / 2 : ℝ)) := by
  intro x hx y hy hxy
  rcases hx with ⟨hx0, hx1⟩
  rcases hy with ⟨hy0, hy1⟩
  unfold Phi2
  apply max_le_max <;> nlinarith [sq_nonneg (y - x)]

theorem B_monotoneOn {r i : ℕ} (hr : 1 ≤ r) (hir : i < r) :
    MonotoneOn (B r i) (Set.Icc 0 (1 / (r : ℝ))) := by
  intro x hx y hy hxy
  have hrp : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hri : (i : ℝ) < r := by exact_mod_cast hir
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  have hry : (r : ℝ) * y ≤ 1 := by
    have := (le_div_iff₀ hrp).mp hy.2
    nlinarith
  have hiy : (i : ℝ) * y ≤ 1 := by nlinarith [hy.1]
  have hixy : (i : ℝ) * x ≤ i * y := mul_le_mul_of_nonneg_left hxy hi0
  have hsq : (1 - (i : ℝ) * y) ^ 2 ≤ (1 - (i : ℝ) * x) ^ 2 := by
    nlinarith
  have hdiv := div_le_div_of_nonneg_right hsq (by linarith : 0 ≤ (r : ℝ) - i)
  unfold B
  linarith

theorem A_monotoneOn (r : ℕ) : MonotoneOn (A r) (Set.Ici 0) := by
  intro x hx y hy hxy
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  unfold A
  nlinarith

theorem R_monotoneOn {r : ℕ} (hr : 2 ≤ r) :
    MonotoneOn (R r)
      (Set.Ici (((r : ℝ) - 2) / ((r : ℝ) * ((r : ℝ) - 1)))) := by
  intro x hx y hy hxy
  have hr1 : (1 : ℝ) < r := by exact_mod_cast (by omega : 1 < r)
  have hden : 0 < (r : ℝ) * ((r : ℝ) - 1) := mul_pos (by linarith) (by linarith)
  have hxl := (div_le_iff₀ hden).mp hx
  have hyl := (div_le_iff₀ hden).mp hy
  have hcoef : 0 ≤ (r : ℝ) * ((r : ℝ) - 1) * (x + y) / 2 - ((r : ℝ) - 2) := by
    nlinarith
  have hp := mul_nonneg (mul_nonneg (Nat.cast_nonneg r) (sub_nonneg.mpr hxy)) hcoef
  unfold R
  nlinarith

theorem A_tangent_eq_B_two {r : ℕ} (hr : 3 ≤ r) :
    A r (1 / (2 * ((r : ℝ) - 1))) = B r 2 (1 / (2 * ((r : ℝ) - 1))) := by
  have hr2 : (2 : ℝ) < r := by exact_mod_cast (by omega : 2 < r)
  have h1 : (r : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (r : ℝ) - 2 ≠ 0 := by linarith
  unfold A B
  norm_num only [Nat.cast_ofNat]
  field_simp
  <;> ring

theorem A_endpoint_nonneg {r : ℕ} (hr : 2 ≤ r) :
    0 ≤ 1 / (2 * ((r : ℝ) - 1)) := by
  have hr1 : (1 : ℝ) < r := by exact_mod_cast (by omega : 1 < r)
  positivity

theorem A_endpoint_le {r : ℕ} (hr : 2 ≤ r) :
    1 / (2 * ((r : ℝ) - 1)) ≤ 1 / (r : ℝ) := by
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  apply one_div_le_one_div_of_le (by linarith)
  linarith

theorem A_le_half {r : ℕ} (hr : 3 ≤ r) {x : ℝ} (hx : ADomain r x) :
    A r x ≤ 1 / 2 := by
  calc
    A r x ≤ A r (1 / (2 * ((r : ℝ) - 1))) :=
      A_monotoneOn r hx.1 (A_endpoint_nonneg (by omega)) hx.2
    _ = B r 2 (1 / (2 * ((r : ℝ) - 1))) := A_tangent_eq_B_two hr
    _ ≤ 1 / 2 := B_le_half (by omega) _

theorem R_right_endpoint {r : ℕ} (hr : 1 ≤ r) : R r (1 / (r : ℝ)) = 1 / 2 := by
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  simp [R, hr0]

theorem R_le_half {r : ℕ} (hr : 2 ≤ r) {x : ℝ} (hx : RDomain r x) :
    R r x ≤ 1 / 2 := by
  rw [← R_right_endpoint (by omega : 1 ≤ r)]
  exact R_monotoneOn hr hx.1 (hx.1.trans hx.2) hx.2

theorem Phi_le_half {r : ℕ} (hr : 3 ≤ r) (x : ℝ) : Phi r x ≤ 1 / 2 := by
  apply Phi_le hr
  · intro i _ hir
    exact B_le_half hir x
  · exact A_le_half hr
  · exact R_le_half (by omega)

theorem Phi_monotoneOn {r : ℕ} (hr : 3 ≤ r) :
    MonotoneOn (Phi r) (Set.Icc 0 (1 / (r : ℝ))) := by
  intro x hx y hy hxy
  apply Phi_le hr
  · intro i hi hir
    exact (B_monotoneOn (by omega) hir hx hy hxy).trans (B_le_Phi hr hi hir y)
  · intro hax
    by_cases hay : y ≤ 1 / (2 * ((r : ℝ) - 1))
    · exact (A_monotoneOn r hx.1 hy.1 hxy).trans (A_le_Phi hr ⟨hy.1, hay⟩)
    · calc
        A r x ≤ A r (1 / (2 * ((r : ℝ) - 1))) :=
          A_monotoneOn r hx.1 (A_endpoint_nonneg (by omega)) hax.2
        _ = B r 2 (1 / (2 * ((r : ℝ) - 1))) := A_tangent_eq_B_two hr
        _ ≤ B r 2 y := B_monotoneOn (by omega) (by omega)
          ⟨A_endpoint_nonneg (by omega), A_endpoint_le (by omega)⟩ hy (le_of_not_ge hay)
        _ ≤ Phi r y := B_le_Phi hr (by omega) (by omega) y
  · intro hrx
    exact (R_monotoneOn (by omega) hrx.1 (hrx.1.trans hxy) hxy).trans
      (R_le_Phi hr ⟨hrx.1.trans hxy, hy.2⟩)

/-- A nonempty index set for the ordinary branches; at `r ≥ 2`, this is
exactly the set of integers `1, ..., r-1`. -/
def BIndices (r : ℕ) : Finset ℕ := insert 1 (Finset.Icc 1 (r - 1))

theorem BIndices_nonempty (r : ℕ) : (BIndices r).Nonempty := by
  exact ⟨1, Finset.mem_insert_self _ _⟩

theorem mem_BIndices_iff {r i : ℕ} (hr : 2 ≤ r) :
    i ∈ BIndices r ↔ 1 ≤ i ∧ i < r := by
  simp only [BIndices, Finset.mem_insert, Finset.mem_Icc]
  omega

/-- The finite maximum of the ordinary branches. -/
noncomputable def BMaximum (r : ℕ) (x : ℝ) : ℝ :=
  (BIndices r).sup' (BIndices_nonempty r) (fun i => B r i x)

theorem B_le_BMaximum {r i : ℕ} (hr : 2 ≤ r) (hi : 1 ≤ i) (hir : i < r) (x : ℝ) :
    B r i x ≤ BMaximum r x :=
  Finset.le_sup' (fun j => B r j x) ((mem_BIndices_iff hr).mpr ⟨hi, hir⟩)

theorem BMaximum_le_Phi {r : ℕ} (hr : 3 ≤ r) (x : ℝ) : BMaximum r x ≤ Phi r x := by
  apply Finset.sup'_le
  intro i hi
  rcases (mem_BIndices_iff (by omega)).mp hi with ⟨hi, hir⟩
  exact B_le_Phi hr hi hir x

theorem continuous_BMaximum (r : ℕ) : Continuous (BMaximum r) :=
  Continuous.finset_sup'_apply (BIndices_nonempty r) (fun i _ => continuous_B r i)

theorem R_left_eq_B_one_zero {r : ℕ} (hr : 3 ≤ r) :
    R r (((r : ℝ) - 2) / ((r : ℝ) * ((r : ℝ) - 1))) = B r 1 0 := by
  have hr2 : (2 : ℝ) < r := by exact_mod_cast (by omega : 2 < r)
  have hr0 : (r : ℝ) ≠ 0 := by linarith
  have hr1 : (r : ℝ) - 1 ≠ 0 := by linarith
  unfold R B
  norm_num only [Nat.cast_one, mul_zero, sub_zero, one_pow]
  field_simp
  <;> ring

/-- A continuous model of the restricted maximum. The `A` branch is kept
constant beyond its right endpoint, and `R` before its left endpoint.
Those extensions lie below a `B` branch on the parameter interval. -/
noncomputable def continuousEnvelope (r : ℕ) (x : ℝ) : ℝ :=
  max (BMaximum r x)
    (max (A r (min x (1 / (2 * ((r : ℝ) - 1)))))
      (R r (max x (((r : ℝ) - 2) / ((r : ℝ) * ((r : ℝ) - 1))))))

theorem continuous_continuousEnvelope (r : ℕ) : Continuous (continuousEnvelope r) := by
  apply (continuous_BMaximum r).max
  apply Continuous.max
  · exact (continuous_A r).comp (continuous_id.min continuous_const)
  · exact (continuous_R r).comp (continuous_id.max continuous_const)

theorem Phi_eq_continuousEnvelope {r : ℕ} (hr : 3 ≤ r) {x : ℝ}
    (hx : x ∈ Set.Icc 0 (1 / (r : ℝ))) : Phi r x = continuousEnvelope r x := by
  have hA : A r (min x (1 / (2 * ((r : ℝ) - 1)))) ≤ Phi r x := by
    by_cases hxa : x ≤ 1 / (2 * ((r : ℝ) - 1))
    · rw [min_eq_left hxa]
      exact A_le_Phi hr ⟨hx.1, hxa⟩
    · rw [min_eq_right (le_of_not_ge hxa), A_tangent_eq_B_two hr]
      exact (B_monotoneOn (by omega) (by omega : 2 < r)
        ⟨A_endpoint_nonneg (by omega), A_endpoint_le (by omega)⟩ hx
        (le_of_not_ge hxa)).trans (B_le_Phi hr (by norm_num) (by omega) x)
  have hR : R r (max x (((r : ℝ) - 2) / ((r : ℝ) * ((r : ℝ) - 1)))) ≤ Phi r x := by
    by_cases hxr : ((r : ℝ) - 2) / ((r : ℝ) * ((r : ℝ) - 1)) ≤ x
    · rw [max_eq_left hxr]
      exact R_le_Phi hr ⟨hxr, hx.2⟩
    · rw [max_eq_right (le_of_not_ge hxr), R_left_eq_B_one_zero hr]
      exact (B_monotoneOn (by omega) (by omega : 1 < r)
        ⟨le_rfl, by positivity⟩ hx hx.1).trans (B_le_Phi hr le_rfl (by omega) x)
  apply le_antisymm
  · apply Phi_le hr
    · intro i hi hir
      exact (B_le_BMaximum (by omega) hi hir x).trans (le_max_left _ _)
    · intro hax
      unfold continuousEnvelope
      rw [min_eq_left hax.2]
      exact le_max_of_le_right (le_max_left _ _)
    · intro hrx
      unfold continuousEnvelope
      rw [max_eq_left hrx.1]
      exact le_max_of_le_right (le_max_right _ _)
  · exact max_le (BMaximum_le_Phi hr x) (max_le hA hR)

/-- Continuity includes both restricted-domain endpoints and every crossing;
no explicit phase diagram is needed for this result. -/
theorem continuousOn_Phi {r : ℕ} (hr : 3 ≤ r) :
    ContinuousOn (Phi r) (Set.Icc 0 (1 / (r : ℝ))) := by
  apply (continuous_continuousEnvelope r).continuousOn.congr
  intro x hx
  exact Phi_eq_continuousEnvelope hr hx

end DensityHS
