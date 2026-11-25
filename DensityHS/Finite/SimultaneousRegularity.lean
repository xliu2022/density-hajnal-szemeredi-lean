module

public import DensityHS.Finite.RegularityIncrement
public import DensityHS.Finite.RegularityBounds

/-!
# Simultaneous regularity for arbitrary finite matrices

Author and maintainer: Xizhi Liu.

The theorem is uniform in the vertex set and applies to nonsymmetric
matrices. In particular it regularizes the directional and double-arc
relations of a digraph at once. All partition construction and energy
increments are proved in the imported modules.
-/

@[expose] public section

namespace DensityHS.MatrixRegularity

open Finset Fintype
open scoped BigOperators

attribute [local instance] Classical.propDecidable

universe u

variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

def goodCells (P : Finpartition (Finset.univ : Finset V)) (m : ℕ) : Finset (Finset V) :=
  P.parts.filter (fun S => S.card = m)

theorem goodCells_subset (P : Finpartition (Finset.univ : Finset V)) (m : ℕ) :
    goodCells P m ⊆ P.parts := Finset.filter_subset _ _

theorem goodCells_card (P : Finpartition (Finset.univ : Finset V)) (m : ℕ)
    {S : Finset V} (hS : S ∈ goodCells P m) : S.card = m := (Finset.mem_filter.mp hS).2

def IsBalanced (P : Finpartition (Finset.univ : Finset V)) (m : ℕ) (δ : ℝ) : Prop :=
  0 < m ∧ (∀ S ∈ P.parts, S.card ≤ m) ∧
    (1-δ)*(Fintype.card V : ℝ) ≤ (goodCells P m).card*(m : ℝ) ∧
    (m : ℝ) ≤ δ*Fintype.card V

def IsSimultaneouslyUniform (F : C → V → V → ℝ) (ε : ℝ)
    (P : Finpartition (Finset.univ : Finset V)) (m : ℕ) : Prop :=
  ∀ c, ((badPairs (F c) ε (goodCells P m)).card : ℝ) ≤ ε*((goodCells P m).card : ℝ)^2

theorem exists_balanced_refinement [Nonempty V]
    (P : Finpartition (Finset.univ : Finset V)) {δ : ℝ} (hδ : 0 < δ)
    {A : ℕ} (hA : P.parts.card ≤ A) (hA0 : 0 < A)
    (hlarge : 2*(A : ℝ)/δ ≤ Fintype.card V) :
    ∃ (Q : Finpartition (Finset.univ : Finset V)) (m : ℕ), Q ≤ P ∧
      IsBalanced Q m δ ∧ Q.parts.card ≤ equalRefineBound δ A := by
  obtain ⟨Q,m,hQP,hm,hsize,hmass,hcard,hmhi⟩ :=
    exists_bounded_equal_refinement P hδ hA hA0 hlarge
  have hAr : (1 : ℝ) ≤ A := by exact_mod_cast hA0
  have hsmall : (m : ℝ) ≤ δ*Fintype.card V := by
    apply hmhi.trans
    exact div_le_self (by positivity) hAr
  exact ⟨Q,m,hQP,⟨hm,hsize,hmass,hsmall⟩,nat_le_equalRefineBound hcard⟩

theorem balanced_half_mass {P : Finpartition (Finset.univ : Finset V)} {m : ℕ} {δ : ℝ}
    (hP : IsBalanced P m δ) (hδ : δ ≤ 1/2) :
    (Fintype.card V : ℝ)/2 ≤ (goodCells P m).card*(m : ℝ) := by
  apply le_trans _ hP.2.2.1
  have hN : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  nlinarith

theorem regularity_iteration [Nonempty V]
    (F : C → V → V → ℝ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδhalf : δ ≤ 1/2)
    {T : ℕ} (hN : regularityOrderThreshold δ T ≤ Fintype.card V) :
    ∀ i ≤ T, ∃ (P : Finpartition (Finset.univ : Finset V)) (m : ℕ),
      IsBalanced P m δ ∧ P.parts.card ≤ regularitySizeBound δ i ∧
      (IsSimultaneouslyUniform F ε P m ∨
        (i : ℝ)*(ε^8/16)*(Fintype.card V : ℝ)^2 ≤ matrixEnergy P F) := by
  intro i
  induction i with
  | zero =>
    intro hi
    let P₀ : Finpartition (Finset.univ : Finset V) :=
      Finpartition.indiscrete Finset.univ_nonempty.ne_empty
    have hlarge : 2*(1 : ℝ)/δ ≤ Fintype.card V := by
      apply le_trans _ (regularityOrderThreshold_large hδ hi hN)
      have ha : 1 ≤ atomBound (regularitySizeBound δ 0) :=
        atomBound_pos (regularitySizeBound_pos δ 0)
      gcongr
      exact_mod_cast ha
    obtain ⟨P,m,hPP,hbal,hcard⟩ := exists_balanced_refinement P₀ hδ
      (A := 1) (by simp [P₀]) (by omega) (by simpa using hlarge)
    refine ⟨P,m,hbal,hcard.trans (le_max_right _ _),Or.inr ?_⟩
    simpa using matrixEnergy_nonneg P F
  | succ i ih =>
    intro hi
    obtain ⟨P,m,hbal,hcard,hor⟩ := ih (by omega)
    by_cases hreg : IsSimultaneouslyUniform F ε P m
    · exact ⟨P,m,hbal,hcard.trans (regularitySizeBound_mono δ (Nat.le_succ i)),Or.inl hreg⟩
    have henergy := hor.resolve_left hreg
    have hfail : ∃ c, ε*((goodCells P m).card : ℝ)^2 <
        ((badPairs (F c) ε (goodCells P m)).card : ℝ) := by
      simpa only [IsSimultaneouslyUniform, not_forall, not_le] using hreg
    obtain ⟨c,hbad⟩ := hfail
    obtain ⟨Q,hQP,hQcard,hgain⟩ := exists_matrix_energy_increment P F hε
      (goodCells P m) (goodCells_subset P m) (fun S hS => goodCells_card P m hS)
      (balanced_half_mass hbal hδhalf) c hbad.le
    have hA : Q.parts.card ≤ atomBound (regularitySizeBound δ i) :=
      hQcard.trans (atomBound_mono hcard)
    have hA0 : 0 < atomBound (regularitySizeBound δ i) :=
      atomBound_pos (regularitySizeBound_pos δ i)
    obtain ⟨R,m',hRQ,hRbal,hRcard⟩ := exists_balanced_refinement Q hδ hA hA0
      (regularityOrderThreshold_large hδ (by omega : i ≤ T) hN)
    refine ⟨R,m',hRbal,hRcard.trans (equalRefineBound_le_next δ i),Or.inr ?_⟩
    have hmono := matrixEnergy_mono hRQ F
    have heq : ((i+1 : ℕ) : ℝ)*(ε^8/16)*(Fintype.card V : ℝ)^2 =
        (i : ℝ)*(ε^8/16)*(Fintype.card V : ℝ)^2 + (ε^8/16)*(Fintype.card V : ℝ)^2 := by
      push_cast
      ring
    rw [heq]
    linarith

theorem exists_simultaneous_balanced_partition [Nonempty V]
    (F : C → V → V → ℝ) (hF0 : ∀ c x y, 0 ≤ F c x y) (hF1 : ∀ c x y, F c x y ≤ 1)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδhalf : δ ≤ 1/2)
    (hN : regularityOrderThreshold δ (energySteps ε (Fintype.card C)) ≤ Fintype.card V) :
    ∃ (P : Finpartition (Finset.univ : Finset V)) (m : ℕ), IsBalanced P m δ ∧
      P.parts.card ≤ regularitySizeBound δ (energySteps ε (Fintype.card C)) ∧
      IsSimultaneouslyUniform F ε P m := by
  obtain ⟨P,m,hbal,hcard,hor⟩ := regularity_iteration F hε hδ hδhalf hN
    (energySteps ε (Fintype.card C)) le_rfl
  refine ⟨P,m,hbal,hcard,?_⟩
  rcases hor with hreg | he
  · exact hreg
  · exfalso
    have hupper := matrixEnergy_le P hF0 hF1
    have hNpos : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
    have hbig := mul_lt_mul_of_pos_right (energySteps_gain hε (Fintype.card C))
      (sq_pos_of_pos hNpos)
    linarith

theorem balanced_good_card_lower [Nonempty V]
    {P : Finpartition (Finset.univ : Finset V)} {m l : ℕ} {δ : ℝ}
    (hP : IsBalanced P m δ) (hδ : 0 < δ) (hδsmall : δ*((l : ℝ)+1) ≤ 1/4) :
    l ≤ (goodCells P m).card := by
  have hN : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hl : (0 : ℝ) ≤ l := Nat.cast_nonneg _
  have hδquarter : δ ≤ 1/4 := by nlinarith
  have hδl : δ*(l : ℝ) ≤ 1/4 := by nlinarith
  by_contra h
  have hk : ((goodCells P m).card : ℝ) ≤ l := by exact_mod_cast (by omega : (goodCells P m).card ≤ l)
  have hprod : ((goodCells P m).card : ℝ)*(m : ℝ) ≤ (l : ℝ)*δ*Fintype.card V := by
    calc
      _ ≤ (l : ℝ)*(m : ℝ) := by gcongr
      _ ≤ (l : ℝ)*(δ*Fintype.card V) := by gcongr; exact hP.2.2.2
      _ = _ := by ring
  have hprod' := mul_le_mul_of_nonneg_right hδl hN.le
  have hmass := hP.2.2.1
  nlinarith

/-- Simultaneous Szemerédi regularity for finitely many arbitrary matrices.
The constants are independent of the finite vertex set. Good cells have
exactly equal size, cover at least `(1-ε)n` vertices, and have few bad pairs
in every matrix. -/
theorem simultaneous_matrix_regularity (C : Type*) [Fintype C] [DecidableEq C]
    {ε : ℝ} (hε : 0 < ε) (l : ℕ) :
    ∃ M N : ℕ, ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (F : C → W → W → ℝ),
      (∀ c x y, 0 ≤ F c x y) → (∀ c x y, F c x y ≤ 1) → N ≤ Fintype.card W →
      ∃ (P : Finpartition (Finset.univ : Finset W)) (m : ℕ), 0 < m ∧
        l ≤ (goodCells P m).card ∧ P.parts.card ≤ M ∧
        (1-ε)*(Fintype.card W : ℝ) ≤ (goodCells P m).card*(m : ℝ) ∧
        IsSimultaneouslyUniform F ε P m := by
  let δ : ℝ := min (ε/2) (1/(4*((l : ℝ)+1)))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδε : δ ≤ ε := (min_le_left _ _).trans (by linarith)
  have hδsmall : δ*((l : ℝ)+1) ≤ 1/4 := by
    have h := mul_le_mul_of_nonneg_right (min_le_right (ε/2) (1/(4*((l : ℝ)+1))))
      (by positivity : (0 : ℝ) ≤ (l : ℝ)+1)
    have heq : (1/(4*((l : ℝ)+1)))*((l : ℝ)+1) = 1/4 := by field_simp
    simpa only [heq] using h
  have hδhalf : δ ≤ 1/2 := by
    have hl : (0 : ℝ) ≤ l := Nat.cast_nonneg _
    nlinarith
  let T := energySteps ε (Fintype.card C)
  refine ⟨regularitySizeBound δ T,regularityOrderThreshold δ T,?_⟩
  intro W _ _ F hF0 hF1 hN
  have hcardpos : 0 < Fintype.card W := (regularityOrderThreshold_pos δ T).trans_le hN
  letI : Nonempty W := Fintype.card_pos_iff.mp hcardpos
  obtain ⟨P,m,hbal,hbound,hreg⟩ := exists_simultaneous_balanced_partition F hF0 hF1 hε hδ hδhalf hN
  refine ⟨P,m,hbal.1,balanced_good_card_lower hbal hδ hδsmall,hbound,?_,hreg⟩
  apply le_trans _ hbal.2.2.1
  gcongr

end DensityHS.MatrixRegularity
