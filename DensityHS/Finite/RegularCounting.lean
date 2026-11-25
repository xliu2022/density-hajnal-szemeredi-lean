module

public import DensityHS.Finite.RegularEmbedding
public import Mathlib.Data.Finset.Sigma

/-!
# Quantitative counting of regular transversal cliques

This strengthens the greedy existence lemma to a count of actual vertex
maps.  Every step retains all good first vertices and counts every recursive
completion; the resulting maps are distinct by their first coordinate.

Formalization author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS.Regularity

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def transversalCliqueMaps (n : ℕ) (P : Fin n → Finset V) :
    Finset (Fin n → V) := by
  classical
  exact Finset.univ.filter fun f => (∀ i, f i ∈ P i) ∧
    ∀ i j, i ≠ j → G.Adj (f i) (f j)

theorem mem_transversalCliqueMaps {n : ℕ} {P : Fin n → Finset V} {f : Fin n → V} :
    f ∈ transversalCliqueMaps G n P ↔
      (∀ i, f i ∈ P i) ∧ ∀ i j, i ≠ j → G.Adj (f i) (f j) := by
  classical
  simp [transversalCliqueMaps]

theorem transversalCliqueMaps_injective {n : ℕ} {P : Fin n → Finset V} {f : Fin n → V}
    (hf : f ∈ transversalCliqueMaps G n P) : Function.Injective f := by
  intro i j heq
  by_contra hij
  exact ((mem_transversalCliqueMaps G).mp hf).2 i j hij |>.ne heq

/-- Integer product lower bound for the number of genuine transversal
clique maps.  The budgets may differ between clusters. -/
theorem regular_transversal_count (n : ℕ) {ε q η : ℝ}
    (hε : 0 < ε) (hq : 0 < q) (hq1 : q ≤ 1) (hη : 0 < η)
    (S P : Fin n → Finset V) (M : Fin n → ℕ)
    (hP : ∀ i, P i ⊆ S i)
    (hsize : ∀ i, η * (S i).card ≤ (P i).card)
    (hreg : ∀ i j, i ≠ j → G.IsUniform ε (S i) (S j))
    (hdensity : ∀ i j, i ≠ j → q + ε ≤ (G.edgeDensity (S i) (S j) : ℝ))
    (hsmall : 2 * ε * n < η * q ^ (n - 1))
    (hbudget : ∀ i, 2 * (M i : ℝ) ≤ η * q ^ (n - 1) * (S i).card) :
    (∏ i, M i) ≤ (transversalCliqueMaps G n P).card := by
  classical
  induction n generalizing η with
  | zero =>
    simp [transversalCliqueMaps]
  | succ n ih =>
    have hsmall' : 2 * ε * ((n : ℝ) + 1) < η * q ^ n := by
      simpa only [Nat.succ_sub_one, Nat.cast_succ] using hsmall
    have hpow : q ^ n ≤ 1 := pow_le_one₀ hq.le hq1
    have hbound : 2 * ε * ((n : ℝ) + 1) < η :=
      hsmall'.trans_le (by simpa using mul_le_mul_of_nonneg_left hpow hη.le)
    have hεη : ε < η := by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    let bad : Fin n → Finset V := fun j => lowDegreeVertices G q (S 0) (P j.succ)
    let B : Finset V := Finset.univ.biUnion bad
    let A : Finset V := P 0 \ B
    have hbadcard (j : Fin n) : ((bad j).card : ℝ) ≤ ε * (S 0).card := by
      apply card_lowDegree_le G hq.le (hreg 0 j.succ (Fin.succ_ne_zero j).symm)
        (hdensity 0 j.succ (Fin.succ_ne_zero j).symm) (hP j.succ)
      exact (mul_le_mul_of_nonneg_right hεη.le (Nat.cast_nonneg _)).trans (hsize _)
    have hBcard : (B.card : ℝ) ≤ (n : ℝ) * ε * (S 0).card := by
      calc
        (B.card : ℝ) ≤ ∑ j : Fin n, ((bad j).card : ℝ) := by
          exact_mod_cast (show B.card ≤ ∑ j : Fin n, (bad j).card from Finset.card_biUnion_le)
        _ ≤ ∑ _j : Fin n, ε * (S 0).card :=
          Finset.sum_le_sum fun j _ => hbadcard j
        _ = (n : ℝ) * ε * (S 0).card := by simp; ring
    have hgood : M 0 ≤ A.card := by
      have hPcard : ((P 0).card : ℝ) ≤ A.card + (B.card : ℝ) := by
        exact_mod_cast (show (P 0).card ≤ A.card + B.card from Finset.card_le_card_sdiff_add_card)
      have hnb : (n : ℝ) * ε ≤ η / 2 := by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have hbudget0 : 2 * (M 0 : ℝ) ≤ η * (S 0).card := by
        apply (hbudget 0).trans
        simp only [Nat.succ_sub_one]
        gcongr
        nlinarith
      have hscaled := mul_le_mul_of_nonneg_right hnb (Nat.cast_nonneg (S 0).card)
      have hM : (M 0 : ℝ) ≤ A.card := by nlinarith [hsize 0]
      exact_mod_cast hM
    let P' (x : V) : Fin n → Finset V := fun j => (P j.succ).filter (G.Adj x)
    have hdegree {x : V} (hx : x ∈ A) (j : Fin n) :
        q * (P j.succ).card ≤ (((P' x) j).card : ℝ) := by
      apply le_of_not_gt
      intro hj
      apply (Finset.mem_sdiff.mp hx).2
      refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, ?_⟩
      exact Finset.mem_filter.mpr ⟨hP 0 (Finset.mem_sdiff.mp hx).1, hj⟩
    have hsmallIH : 2 * ε * n < (η * q) * q ^ (n - 1) := by
      cases n with
      | zero => simpa using mul_pos hη hq
      | succ k =>
        simp only [Nat.succ_sub_one, Nat.cast_succ] at ⊢ hsmall'
        rw [pow_succ] at hsmall'
        nlinarith
    have hbudgetIH (j : Fin n) :
        2 * (M j.succ : ℝ) ≤ (η * q) * q ^ (n - 1) * (S j.succ).card := by
      have hn : 1 ≤ n := by
        have hj := j.isLt
        omega
      have hp : (η * q) * q ^ (n - 1) = η * q ^ n := by
        rw [mul_assoc, ← pow_succ', Nat.sub_add_cancel hn]
      rw [hp]
      simpa only [Nat.succ_sub_one] using hbudget j.succ
    have htail {x : V} (hx : x ∈ A) :
        (∏ j : Fin n, M j.succ) ≤ (transversalCliqueMaps G n (P' x)).card := by
      apply ih (mul_pos hη hq) (fun j => S j.succ) (P' x) (fun j => M j.succ)
        (fun j => (Finset.filter_subset _ _).trans (hP j.succ))
      · intro j
        calc
          (η * q) * (S j.succ).card = q * (η * (S j.succ).card) := by ring
          _ ≤ q * (P j.succ).card := mul_le_mul_of_nonneg_left (hsize _) hq.le
          _ ≤ _ := hdegree hx j
      · exact fun i j hij => hreg i.succ j.succ (by simpa using hij)
      · exact fun i j hij => hdensity i.succ j.succ (by simpa using hij)
      · exact hsmallIH
      · exact hbudgetIH
    let U : Finset (Σ _x : V, Fin n → V) :=
      A.sigma fun x => transversalCliqueMaps G n (P' x)
    let prepend : (Σ _x : V, Fin n → V) → (Fin (n + 1) → V) :=
      fun t => Fin.cons t.1 t.2
    have hprepend : Function.Injective prepend := by
      rintro ⟨x, f⟩ ⟨y, g⟩ h
      have hh : x = y := congrFun h 0
      have ht : f = g := funext fun j => congrFun h j.succ
      subst y
      subst g
      rfl
    have hsub : U.image prepend ⊆ transversalCliqueMaps G (n + 1) P := by
      intro f hf
      obtain ⟨⟨x, g⟩, hmem, rfl⟩ := Finset.mem_image.mp hf
      rcases Finset.mem_sigma.mp hmem with ⟨hx, hg⟩
      rcases (mem_transversalCliqueMaps G).mp hg with ⟨hgP, hgadj⟩
      apply (mem_transversalCliqueMaps G).mpr
      constructor
      · intro i
        cases i using Fin.cases with
        | zero => exact (Finset.mem_sdiff.mp hx).1
        | succ i => exact (Finset.mem_filter.mp (hgP i)).1
      · intro i j hij
        cases i using Fin.cases with
        | zero =>
          cases j using Fin.cases with
          | zero => exact False.elim (hij rfl)
          | succ j => exact (Finset.mem_filter.mp (hgP j)).2
        | succ i =>
          cases j using Fin.cases with
          | zero => exact (Finset.mem_filter.mp (hgP i)).2.symm
          | succ j => exact hgadj i j (fun h => hij (congrArg Fin.succ h))
    calc
      (∏ i, M i) = M 0 * ∏ j : Fin n, M j.succ := Fin.prod_univ_succ _
      _ ≤ A.card * ∏ j : Fin n, M j.succ := Nat.mul_le_mul_right _ hgood
      _ = ∑ _x ∈ A, ∏ j : Fin n, M j.succ := by simp only [Finset.sum_const_nat]
      _ ≤ ∑ x ∈ A, (transversalCliqueMaps G n (P' x)).card :=
        Finset.sum_le_sum fun _ hx => htail hx
      _ = U.card := (Finset.card_sigma _ _).symm
      _ = (U.image prepend).card := (Finset.card_image_of_injective _ hprepend).symm
      _ ≤ _ := Finset.card_le_card hsub

/-- A uniform positive proportion of the product of the cluster sizes.
The size assumption makes the rounding loss at most a factor of two. -/
theorem regular_transversal_count_lower (n : ℕ) {ε q η : ℝ}
    (hε : 0 < ε) (hq : 0 < q) (hq1 : q ≤ 1) (hη : 0 < η)
    (S P : Fin n → Finset V)
    (hP : ∀ i, P i ⊆ S i)
    (hsize : ∀ i, η * (S i).card ≤ (P i).card)
    (hreg : ∀ i j, i ≠ j → G.IsUniform ε (S i) (S j))
    (hdensity : ∀ i j, i ≠ j → q + ε ≤ (G.edgeDensity (S i) (S j) : ℝ))
    (hsmall : 2 * ε * n < η * q ^ (n - 1))
    (hlarge : ∀ i, 4 ≤ η * q ^ (n - 1) * (S i).card) :
    (η * q ^ (n - 1) / 4) ^ n * (∏ i, ((S i).card : ℝ)) ≤
      ((transversalCliqueMaps G n P).card : ℝ) := by
  classical
  let M : Fin n → ℕ := fun i => ⌊η * q ^ (n - 1) * (S i).card / 2⌋₊
  have hupper (i : Fin n) : (M i : ℝ) ≤ η * q ^ (n - 1) * (S i).card / 2 :=
    Nat.floor_le (by positivity)
  have hlower (i : Fin n) : (η * q ^ (n - 1) / 4) * (S i).card ≤ (M i : ℝ) := by
    have hround := Nat.lt_floor_add_one (η * q ^ (n - 1) * (S i).card / 2)
    change η * q ^ (n - 1) * (S i).card / 2 < (M i : ℝ) + 1 at hround
    nlinarith [hlarge i]
  have hcount := regular_transversal_count G n hε hq hq1 hη S P M hP hsize hreg
    hdensity hsmall (fun i => by linarith [hupper i])
  have hcast : (∏ i, (M i : ℝ)) ≤ ((transversalCliqueMaps G n P).card : ℝ) := by
    exact_mod_cast hcount
  calc
    _ = ∏ i, (η * q ^ (n - 1) / 4) * (S i).card := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ ∏ i, (M i : ℝ) := Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun i _ => hlower i)
    _ ≤ _ := hcast

/-- The same quantitative count using the usual pair-density parameter. -/
theorem regular_transversal_count_density (n : ℕ) {ε d α : ℝ}
    (hε : 0 < ε) (hd : ε < d) (hd1 : d - ε ≤ 1) (hα : 0 < α)
    (S P : Fin n → Finset V)
    (hP : ∀ i, P i ⊆ S i)
    (hsize : ∀ i, α * (S i).card ≤ (P i).card)
    (hreg : ∀ i j, i ≠ j → G.IsUniform ε (S i) (S j))
    (hdensity : ∀ i j, i ≠ j → d ≤ (G.edgeDensity (S i) (S j) : ℝ))
    (hsmall : 2 * ε * n < α * (d - ε) ^ (n - 1))
    (hlarge : ∀ i, 4 ≤ α * (d - ε) ^ (n - 1) * (S i).card) :
    (α * (d - ε) ^ (n - 1) / 4) ^ n * (∏ i, ((S i).card : ℝ)) ≤
      ((transversalCliqueMaps G n P).card : ℝ) := by
  exact regular_transversal_count_lower G n hε (sub_pos.mpr hd) hd1 hα S P hP hsize hreg
    (fun i j hij => by simpa only [sub_add_cancel] using hdensity i j hij) hsmall hlarge

end DensityHS.Regularity
