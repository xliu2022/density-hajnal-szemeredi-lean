module

public import DensityHS.Rainbow.RandomOrientation
public import DensityHS.Rainbow.Digraph

/-!
# Simultaneous degree control for independent pair orientations

One Bernoulli coordinate controls each unordered pair, represented by its
increasing ordered pair.  The two endpoint scores use that same coordinate,
so opposite directions can be coupled or excluded exactly as prescribed.

Formalization author and maintainer: Xizhi Liu.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace DensityHS.Rainbow

variable {I : Type*} [Fintype I] [LinearOrder I]

def pairOrientation (L R : I × I → Bool → ℝ) (ω : I × I → Bool) : Digraph I where
  Arc i j := (i < j ∧ L (i, j) (ω (i, j)) = 1) ∨
    (j < i ∧ R (j, i) (ω (j, i)) = 1)
  loopless i := by simp

def pairScore (L R : I × I → Bool → ℝ) (i : I) (e : I × I) (b : Bool) : ℝ :=
  (if e.1 = i then L e b else 0) + (if e.2 = i then R e b else 0)

theorem pairScore_binary {L R : I × I → Bool → ℝ}
    (hL : ∀ e b, L e b = 0 ∨ L e b = 1)
    (hR : ∀ e b, R e b = 0 ∨ R e b = 1)
    (hzero : ∀ e, ¬e.1 < e.2 → ∀ b, L e b = 0 ∧ R e b = 0)
    (i : I) (e : I × I) (b : Bool) : pairScore L R i e b = 0 ∨ pairScore L R i e b = 1 := by
  by_cases h₁ : e.1 = i <;> by_cases h₂ : e.2 = i
  · have hz := hzero e (by simpa only [h₁, h₂] using (lt_irrefl i)) b
    simp only [pairScore, h₁, h₂, if_true, hz.1, hz.2, zero_add, true_or]
  · simpa only [pairScore, h₁, h₂, if_true, if_false, add_zero] using hL e b
  · simpa only [pairScore, h₁, h₂, if_true, if_false, zero_add] using hR e b
  · simp only [pairScore, h₁, h₂, if_false, zero_add, true_or]

theorem pairScore_sum (L R : I × I → Bool → ℝ) (ω : I × I → Bool) (i : I) :
    ∑ e, pairScore L R i e (ω e) =
      (∑ j, L (i, j) (ω (i, j))) + ∑ j, R (j, i) (ω (j, i)) := by
  simp only [pairScore, sum_add_distrib, Fintype.sum_prod_type]
  simp only [sum_ite_irrel, sum_ite_eq', mem_univ, if_true]
  congr 1
  rw [sum_comm]
  simp only [sum_ite_eq', mem_univ, if_true]

theorem pairOrientation_outDegree {L R : I × I → Bool → ℝ}
    (hL : ∀ e b, L e b = 0 ∨ L e b = 1)
    (hR : ∀ e b, R e b = 0 ∨ R e b = 1)
    (hzero : ∀ e, ¬e.1 < e.2 → ∀ b, L e b = 0 ∧ R e b = 0)
    (ω : I × I → Bool) (i : I) :
    ((pairOrientation L R ω).outDegree i : ℝ) = ∑ e, pairScore L R i e (ω e) := by
  rw [Digraph.outDegree_eq_sum, pairScore_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  rcases lt_trichotomy i j with hij | rfl | hji
  · have hnot : ¬ j < i := not_lt.mpr hij.le
    have hz := (hzero (j, i) hnot (ω (j, i))).2
    rcases hL (i, j) (ω (i, j)) with h | h <;>
      simp only [pairOrientation, hij, hnot, true_and, false_and, or_false, h, hz] <;> norm_num
  · have hz := hzero (i, i) (lt_irrefl i) (ω (i, i))
    simp only [pairOrientation, lt_self_iff_false, false_and, or_self, if_false, hz.1, hz.2, zero_add]
  · have hnot : ¬ i < j := not_lt.mpr hji.le
    have hz := (hzero (i, j) hnot (ω (i, j))).1
    rcases hR (j, i) (ω (j, i)) with h | h <;>
      simp only [pairOrientation, hji, hnot, true_and, false_and, false_or, h, hz] <;> norm_num

theorem pairScore_mean_sum (p : I × I → unitInterval) (L R : I × I → Bool → ℝ) (i : I) :
    ∑ e, binaryMean (p e) (pairScore L R i e) =
      (∑ j, binaryMean (p (i, j)) (L (i, j))) +
        ∑ j, binaryMean (p (j, i)) (R (j, i)) := by
  have hmean (e : I × I) : binaryMean (p e) (pairScore L R i e) =
      (if e.1 = i then binaryMean (p e) (L e) else 0) +
      (if e.2 = i then binaryMean (p e) (R e) else 0) := by
    by_cases h₁ : e.1 = i <;> by_cases h₂ : e.2 = i <;>
      simp only [binaryMean, pairScore, h₁, h₂, if_true, if_false] <;> ring
  simp_rw [hmean]
  simp only [sum_add_distrib, Fintype.sum_prod_type, sum_ite_irrel, sum_ite_eq', mem_univ, if_true]
  congr 1
  rw [sum_comm]
  simp only [sum_ite_eq', mem_univ, if_true]

theorem exists_pairOrientation_degrees
    (p : I × I → unitInterval) (L R : I × I → Bool → ℝ)
    (hL : ∀ e b, L e b = 0 ∨ L e b = 1)
    (hR : ∀ e b, R e b = 0 ∨ R e b = 1)
    (hzero : ∀ e, ¬e.1 < e.2 → ∀ b, L e b = 0 ∧ R e b = 0)
    (m a : I → ℝ) {t : ℝ} (ht : 0 < t)
    (hm : ∀ i, m i ≤ (∑ j, binaryMean (p (i, j)) (L (i, j))) +
      ∑ j, binaryMean (p (j, i)) (R (j, i)))
    (hpotential : ∑ i, Real.exp (t * a i - (1 - Real.exp (-t)) * m i) < 1) :
    ∃ ω : I × I → Bool, ∀ i, a i < ((pairOrientation L R ω).outDegree i : ℝ) := by
  obtain ⟨ω, hω⟩ := exists_simultaneous_binary_scores p (pairScore L R)
    (pairScore_binary hL hR hzero) m a ht
    (fun i => (pairScore_mean_sum p L R i).symm ▸ hm i) hpotential
  exact ⟨ω, fun i => (hω i).trans_eq (pairOrientation_outDegree hL hR hzero ω i).symm⟩

end DensityHS.Rainbow
