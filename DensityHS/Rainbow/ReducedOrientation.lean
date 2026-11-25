module

public import DensityHS.Rainbow.PairStates
public import DensityHS.Rainbow.OrientationParameters

/-!
# Orienting a reduced graph from exclusive and double densities

The two densities are disjoint arc states.  After irregular pairs and low
densities are discarded, the remaining single directions are coupled by
one coin per pair.  The theorem constructs an actual digraph with a uniform
out-degree bound and certifies the exact regular state needed on every arc.

Formalization author and maintainer: Xizhi Liu.
-/

@[expose] public section

open Finset
open scoped BigOperators

universe u

namespace DensityHS.Rainbow

attribute [local instance] Classical.propDecidable

variable {I : Type*} [Fintype I] [LinearOrder I]

def eligibleSingle (M : I → I → Prop) (a : I → I → ℝ) (d : ℝ) (i j : I) : Prop :=
  M i j ∧ d ≤ a i j

def eligibleDouble (M : I → I → Prop) (b : I → I → ℝ) (d : ℝ) (i j : I) : Prop :=
  M i j ∧ d ≤ b i j

def densityProbability (a : I → I → ℝ) (ha0 : ∀ i j, 0 ≤ a i j)
    (ha1 : ∀ i j, a i j ≤ 1) (e : I × I) : unitInterval :=
  ⟨a e.1 e.2, ha0 _ _, ha1 _ _⟩

theorem densityState_means_lower (M : I → I → Prop) (hM : Symmetric M)
    (a b : I → I → ℝ) (ha0 : ∀ i j, 0 ≤ a i j) (ha1 : ∀ i j, a i j ≤ 1)
    (hb0 : ∀ i j, 0 ≤ b i j)
    (hpartition : ∀ i j, a i j + a j i + b i j ≤ 1)
    {d : ℝ} (hd : 0 ≤ d) {i j : I} (hij : i < j) :
    let A := eligibleSingle M a d
    let B := eligibleDouble M b d
    let p := densityProbability a ha0 ha1 (i, j)
    (a i j + b i j - 2 * d - (if M i j then 0 else 1) ≤ binaryMean p (forwardState A B (i, j))) ∧
    (a j i + b i j - 2 * d - (if M i j then 0 else 1) ≤ binaryMean p (backwardState A B (i, j))) := by
  dsimp only
  have hα := ha0 i j
  have hβ := ha0 j i
  have hγ := hb0 i j
  have htotal := hpartition i j
  by_cases hgood : M i j
  · have hgood' : M j i := hM hgood
    by_cases hdouble : d ≤ b i j <;> by_cases hforward : d ≤ a i j <;>
      by_cases hback : d ≤ a j i <;>
      simp only [eligibleSingle, eligibleDouble, forwardState, backwardState,
        densityProbability, binaryMean, selectionCoin, hij, hgood, hgood',
        hdouble, hforward, hback, ite_true, ite_false, and_true, true_and, and_false,
        Bool.not_true, Bool.not_false, Bool.false_eq_true, mul_one, mul_zero, add_zero,
        zero_add] <;> constructor <;> linarith
  · have hgood' : ¬M j i := fun h => hgood (hM h)
    simp only [eligibleSingle, eligibleDouble, forwardState, backwardState,
      densityProbability, binaryMean, selectionCoin, hij, hgood, hgood',
      ite_true, ite_false, false_and, mul_zero, add_zero]
    constructor <;> linarith

theorem densityState_row_lower (M : I → I → Prop) (hM : Symmetric M)
    (hMdiag : ∀ i, ¬M i i)
    (a b : I → I → ℝ) (ha0 : ∀ i j, 0 ≤ a i j) (ha1 : ∀ i j, a i j ≤ 1)
    (hb0 : ∀ i j, 0 ≤ b i j) (hbsymm : ∀ i j, b i j = b j i)
    (hpartition : ∀ i j, a i j + a j i + b i j ≤ 1)
    {d : ℝ} (hd : 0 ≤ d) (i : I) :
    let A := eligibleSingle M a d
    let B := eligibleDouble M b d
    let p := densityProbability a ha0 ha1
    (∑ j, (a i j + b i j)) - 2 * d * Fintype.card I -
      ((univ.filter fun j => ¬M i j).card : ℝ) ≤
      (∑ j, binaryMean (p (i, j)) (forwardState A B (i, j))) +
        ∑ j, binaryMean (p (j, i)) (backwardState A B (j, i)) := by
  dsimp only
  have hpair (j : I) : a i j + b i j - 2 * d - (if M i j then 0 else 1) ≤
      binaryMean (densityProbability a ha0 ha1 (i, j))
        (forwardState (eligibleSingle M a d) (eligibleDouble M b d) (i, j)) +
      binaryMean (densityProbability a ha0 ha1 (j, i))
        (backwardState (eligibleSingle M a d) (eligibleDouble M b d) (j, i)) := by
    rcases lt_trichotomy i j with hij | rfl | hji
    · have hh := (densityState_means_lower M hM a b ha0 ha1 hb0 hpartition hd hij).1
      have hz : ∀ z, backwardState (eligibleSingle M a d) (eligibleDouble M b d) (j, i) z = 0 := by
        intro z
        exact (pairStates_zero _ _ _ (not_lt.mpr hij.le) z).2
      simpa only [binaryMean, hz, mul_zero, add_zero] using hh
    · have hz := hMdiag i
      have ht := hpartition i i
      have hp := ha0 i i
      simp only [forwardState, backwardState, lt_self_iff_false, ite_false, binaryMean,
        mul_zero, add_zero, hz]
      linarith
    · have hh := (densityState_means_lower M hM a b ha0 ha1 hb0 hpartition hd hji).2
      have hMM : M j i ↔ M i j := ⟨fun h => hM h, fun h => hM h⟩
      have hz : ∀ z, forwardState (eligibleSingle M a d) (eligibleDouble M b d) (i, j) z = 0 := by
        intro z
        exact (pairStates_zero _ _ _ (not_lt.mpr hji.le) z).1
      simpa only [binaryMean, hz, mul_zero, zero_add, hbsymm j i, hMM] using hh
  have hsum := sum_le_sum (fun j (_ : j ∈ (univ : Finset I)) => hpair j)
  have hbad : (∑ j, if M i j then (0 : ℝ) else 1) =
      ((univ.filter fun j => ¬M i j).card : ℝ) := by
    simpa only [ite_not] using (sum_boole (s := univ) (p := fun j => ¬M i j) :
      (∑ j ∈ univ, if ¬M i j then (1 : ℝ) else 0) = _)
  rw [sum_add_distrib]
  simpa only [sum_sub_distrib, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul,
    hbad, mul_comm (Fintype.card I : ℝ)] using hsum

theorem exists_density_state_orientation {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ (I : Type u) [Fintype I] [LinearOrder I],
      N ≤ Fintype.card I → ∀ (M : I → I → Prop), Symmetric M → (∀ i, ¬M i i) →
      ∀ (a b : I → I → ℝ), (∀ i j, 0 ≤ a i j) → (∀ i j, a i j ≤ 1) →
      (∀ i j, 0 ≤ b i j) → (∀ i j, b i j = b j i) →
      (∀ i j, a i j + a j i + b i j ≤ 1) →
      ∀ {d q : ℝ}, 0 ≤ d →
      (∀ i, ((univ.filter fun j => ¬M i j).card : ℝ) ≤ q * Fintype.card I) →
      (∀ i : I, (ρ + δ + 2 * d + q) * Fintype.card I ≤ ∑ j : I, (a i j + b i j)) →
      ∃ D : Digraph I, (∀ i, ρ * Fintype.card I < (D.outDegree i : ℝ)) ∧
        ∀ i j, D.Arc i j → M i j ∧
          (D.Arc j i → d ≤ b i j) ∧ (¬D.Arc j i → d ≤ a i j) := by
  obtain ⟨N, hN⟩ := exists_pairOrientation_minDegree_threshold.{u} hρ hρ1 hδ
  refine ⟨N, ?_⟩
  intro I _ _ hn M hM hMdiag a b ha0 ha1 hb0 hbsymm hpartition d q hd hbad hrow
  let A := eligibleSingle M a d
  let B := eligibleDouble M b d
  let p := densityProbability a ha0 ha1
  have hmean (i : I) : (ρ + δ) * Fintype.card I ≤
      (∑ j, binaryMean (p (i, j)) (forwardState A B (i, j))) +
      ∑ j, binaryMean (p (j, i)) (backwardState A B (j, i)) := by
    have hh := densityState_row_lower M hM hMdiag a b ha0 ha1 hb0 hbsymm hpartition hd i
    have hr := hrow i
    have hb := hbad i
    dsimp only at hh
    dsimp only [A, B, p]
    nlinarith
  obtain ⟨ω, hω⟩ := hN I hn p (forwardState A B) (backwardState A B)
    (forwardState_binary A B) (backwardState_binary A B) (pairStates_zero A B) hmean
  have hBsymm : Symmetric B := by
    intro i j h
    exact ⟨hM h.1, (hbsymm i j) ▸ h.2⟩
  refine ⟨pairOrientation (forwardState A B) (backwardState A B) ω, hω, ?_⟩
  intro i j hij
  have hh := stateOrientation_arc_spec A B hBsymm ω hij
  refine ⟨hh.1.elim And.left And.left, ?_, ?_⟩
  · intro hji
    exact (hh.2.mp hji).2
  · intro hji
    have hnB : ¬B i j := fun h => hji (hh.2.mpr h)
    exact (hh.1.resolve_left hnB).2

end DensityHS.Rainbow
