module

public import DensityHS.Finite.EqualChunks

/-!
# Equitable good cells in an exact partition refinement

Author and maintainer: Xizhi Liu.

All remainder cells are retained in the full partition. The good cells have
exactly equal size, and their complement has a controlled total size.
-/

@[expose] public section

namespace DensityHS.MatrixRegularity

open Finset Fintype
open scoped BigOperators

variable {V : Type*} [DecidableEq V]

theorem small_cells_eq_not_full {S : Finset V} (P : Finpartition S) {m : ℕ}
    (hsize : ∀ A ∈ P.parts, A.card ≤ m) :
    P.parts.filter (fun A => A.card < m) = P.parts.filter (fun A => A.card ≠ m) := by
  ext A
  simp only [Finset.mem_filter]
  constructor <;> rintro ⟨hA, h⟩ <;> refine ⟨hA, ?_⟩
  · omega
  · exact lt_of_le_of_ne (hsize A hA) h

theorem chunk_total_card_mul_le {S : Finset V} (P : Finpartition S) {m : ℕ}
    (hsize : ∀ A ∈ P.parts, A.card ≤ m)
    (hsmall : (P.parts.filter (fun A => A.card < m)).card ≤ 1) :
    P.parts.card*m ≤ S.card + m := by
  have hmass := full_cells_add_remainder P hsize
  have hcount := Finset.card_filter_add_card_filter_not (s := P.parts) (fun A : Finset V => A.card = m)
  rw [← small_cells_eq_not_full P hsize] at hcount
  have hmul := Nat.mul_le_mul_right m hsmall
  rw [← hcount, Nat.add_mul]
  omega

theorem sum_bind_cells {S : Finset V} (P : Finpartition S)
    (Q : ∀ A ∈ P.parts, Finpartition A) {M : Type*} [AddCommMonoid M]
    (f : Finset V → M) :
    (∑ B ∈ (P.bind Q).parts, f B) = ∑ A : P.parts, ∑ B ∈ (Q A.val A.property).parts, f B := by
  unfold Finpartition.bind
  simp only [Finpartition.copy_parts]
  simpa only [Finset.univ_eq_attach] using
    Finpartition.sum_combine (fun A : P.parts => Q A.val A.property) P.supIndep.attach f

/-- Chopping each cell gives an exact refinement with equal good cells,
bounded exceptional mass, and a bound on the total number of cells. -/
theorem exists_equal_refinement {S : Finset V} (P : Finpartition S) {m : ℕ} (hm : 0 < m) :
    ∃ Q : Finpartition S, Q ≤ P ∧
      (∀ A ∈ Q.parts, A.card ≤ m) ∧
      S.card ≤ (Q.parts.filter (fun A => A.card = m)).card*m + P.parts.card*m ∧
      Q.parts.card*m ≤ S.card + P.parts.card*m := by
  classical
  choose R hRsize hRrem hRsmall using fun A : P.parts => exists_equal_chunks A.val hm
  let Q := P.bind (fun A hA => R ⟨A,hA⟩)
  have hQP : Q ≤ P := by
    intro A hA
    obtain ⟨B,hB,hAB⟩ := Finpartition.mem_bind.mp hA
    exact ⟨B,hB,(R ⟨B,hB⟩).le hAB⟩
  have hsize : ∀ A ∈ Q.parts, A.card ≤ m := by
    intro A hA
    obtain ⟨B,hB,hAB⟩ := Finpartition.mem_bind.mp hA
    exact hRsize ⟨B,hB⟩ A hAB
  have hrem : (∑ A ∈ Q.parts.filter (fun A => A.card < m), A.card) ≤ P.parts.card*m := by
    calc
      _ = ∑ A ∈ Q.parts, if A.card < m then A.card else 0 := Finset.sum_filter ..
      _ = ∑ A : P.parts, ∑ B ∈ (R A).parts, if B.card < m then B.card else 0 :=
        sum_bind_cells P _ _
      _ = ∑ A : P.parts, ∑ B ∈ (R A).parts.filter (fun B => B.card < m), B.card := by
        simp only [Finset.sum_filter]
      _ ≤ ∑ _A : P.parts, m := Finset.sum_le_sum (fun A _ => (hRrem A).le)
      _ = _ := by simp
  have hmass := full_cells_add_remainder Q hsize
  have hcard : Q.parts.card*m ≤ S.card + P.parts.card*m := by
    calc
      _ = ∑ A : P.parts, (R A).parts.card*m := by
        change (P.bind (fun A hA => R ⟨A,hA⟩)).parts.card*m = _
        rw [Finpartition.card_bind, Finset.sum_mul]
        rfl
      _ ≤ ∑ A : P.parts, (A.val.card + m) :=
        Finset.sum_le_sum (fun A _ => chunk_total_card_mul_le (R A) (hRsize A) (hRsmall A))
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
        rw [Finset.sum_coe_sort P.parts Finset.card, P.sum_card_parts]
        norm_cast
  exact ⟨Q,hQP,hsize,by omega,hcard⟩

section Parameters

variable [Fintype V] [Nonempty V]

/-- The number of vertices in the exceptional cells is controlled by `δ`,
and the total number of cells is bounded independently of the graph order. -/
theorem exists_bounded_equal_refinement
    (P : Finpartition (Finset.univ : Finset V)) {δ : ℝ} (hδ : 0 < δ)
    {A : ℕ} (hA : P.parts.card ≤ A) (hA0 : 0 < A)
    (hlarge : 2*(A : ℝ)/δ ≤ Fintype.card V) :
    ∃ (Q : Finpartition (Finset.univ : Finset V)) (m : ℕ), Q ≤ P ∧ 0 < m ∧
      (∀ B ∈ Q.parts, B.card ≤ m) ∧
      (1-δ)*(Fintype.card V : ℝ) ≤ (Q.parts.filter (fun B => B.card = m)).card*(m : ℝ) ∧
      (Q.parts.card : ℝ) ≤ (2/δ+1)*A ∧
      (m : ℝ) ≤ δ*(Fintype.card V : ℝ)/A := by
  let m : ℕ := ⌊δ*(Fintype.card V : ℝ)/A⌋₊
  have hN : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hAr : (0 : ℝ) < A := by exact_mod_cast hA0
  have htwo : 2 ≤ δ*(Fintype.card V : ℝ)/A := by
    apply (le_div_iff₀ hAr).mpr
    have h := (div_le_iff₀ hδ).mp hlarge
    nlinarith
  have hmlo : δ*(Fintype.card V : ℝ)/(2*A) ≤ (m : ℝ) := by
    have hf := Nat.lt_floor_add_one (δ*(Fintype.card V : ℝ)/A)
    change δ*(Fintype.card V : ℝ)/A < (m : ℝ)+1 at hf
    have heq : δ*(Fintype.card V : ℝ)/(2*A) = (δ*(Fintype.card V : ℝ)/A)/2 := by ring
    rw [heq]
    linarith
  have hmhi : (m : ℝ) ≤ δ*(Fintype.card V : ℝ)/A := Nat.floor_le (by positivity)
  have hmr : (0 : ℝ) < m := (div_pos (mul_pos hδ hN) (by positivity)).trans_le hmlo
  have hm : 0 < m := by exact_mod_cast hmr
  obtain ⟨Q,hQP,hsize,hmass,hcard⟩ := exists_equal_refinement P hm
  rw [Finset.card_univ] at hmass hcard
  have hAm : (P.parts.card : ℝ)*m ≤ δ*Fintype.card V := by
    calc
      _ ≤ (A : ℝ)*m := by gcongr
      _ ≤ (A : ℝ)*(δ*(Fintype.card V : ℝ)/A) := by gcongr
      _ = _ := by field_simp
  have hmassR : (Fintype.card V : ℝ) ≤
      (Q.parts.filter (fun B => B.card = m)).card*(m : ℝ) + (P.parts.card : ℝ)*m := by
    exact_mod_cast hmass
  have hcardR : (Q.parts.card : ℝ)*m ≤ (Fintype.card V : ℝ)+(P.parts.card : ℝ)*m := by
    exact_mod_cast hcard
  have hNm : (Fintype.card V : ℝ)/m ≤ 2*A/δ := by
    apply (div_le_iff₀ hmr).mpr
    have h := mul_le_mul_of_nonneg_left hmlo (le_of_lt (div_pos (by positivity : (0 : ℝ)<2*A) hδ))
    have heq : (2*(A : ℝ)/δ) * (δ*(Fintype.card V : ℝ)/(2*A)) = Fintype.card V := by
      field_simp
    rwa [heq] at h
  have hQbound : (Q.parts.card : ℝ) ≤ (2/δ+1)*A := by
    calc
      _ ≤ (Fintype.card V : ℝ)/m+P.parts.card := by
        have h := (le_div_iff₀ hmr).mpr hcardR
        simpa only [add_div, mul_div_assoc, div_self (ne_of_gt hmr), mul_one] using h
      _ ≤ 2*A/δ+A := by gcongr
      _ = _ := by ring
  exact ⟨Q,m,hQP,hm,hsize,by nlinarith,hQbound,hmhi⟩

end Parameters

end DensityHS.MatrixRegularity
