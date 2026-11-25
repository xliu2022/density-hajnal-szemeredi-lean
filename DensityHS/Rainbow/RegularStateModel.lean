module

public import DensityHS.Rainbow.RegularStateMask

/-!
# A concrete regular reduced digraph

Simultaneous matrix regularity, deletion of exceptional clusters, and the
coupled random orientation produce an equitable family covering almost all
vertices.  Every chosen reduced arc has an actual dense regular arc state.

Formalization author and maintainer: Xizhi Liu.
-/

@[expose] public section

set_option maxHeartbeats 1200000

open Finset
open scoped BigOperators

universe u

namespace DensityHS

def Digraph.comap {I J : Type*} (D : Digraph J) (f : I → J) : Digraph I where
  Arc i j := D.Arc (f i) (f j)
  loopless i := D.loopless (f i)

theorem Digraph.outDegree_comap_equiv {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (D : Digraph J) (e : I ≃ J) (i : I) :
    (D.comap e).outDegree i = D.outDegree (e i) := by
  classical
  have hh : ((D.comap e).outDegree i : ℝ) = (D.outDegree (e i) : ℝ) := by
    rw [Digraph.outDegree_eq_sum, Digraph.outDegree_eq_sum]
    exact e.sum_comp (fun j => if D.Arc (e i) j then (1 : ℝ) else 0)
  exact_mod_cast hh

namespace Rainbow

open MatrixRegularity

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

structure RegularStateModel (D : Digraph V) (ε d : ℝ) (k m : ℕ) where
  clusters : Fin k → Finset V
  disjoint : (Set.univ : Set (Fin k)).PairwiseDisjoint clusters
  cluster_card : ∀ i, (clusters i).card = m
  reduced : Digraph (Fin k)
  state : ∀ i j, reduced.Arc i j →
    IsUniform (exclusiveMatrix D) ε (clusters i) (clusters j) ∧
    IsUniform (doubleMatrix D) ε (clusters i) (clusters j) ∧
    (reduced.Arc j i → d ≤ pairAverage (doubleMatrix D) (clusters i) (clusters j)) ∧
    (¬reduced.Arc j i → d ≤ pairAverage (exclusiveMatrix D) (clusters i) (clusters j))

set_option linter.unusedSectionVars false in
theorem exists_regular_state_model {ρ τ θ ε d q ζ : ℝ}
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hτ : 0 < τ)
    (hε : 0 < ε) (hd : 0 ≤ d) (hq : 0 < q) (hqhalf : q ≤ 1 / 2)
    (hregsmall : 5 * ε ≤ q ^ 2) (hcoverloss : ε + q ≤ ζ)
    (hmargin : ρ + τ + 2 * d + 3 * q ≤ θ - ε) (l : ℕ) :
    ∃ M N : ℕ, ∀ (W : Type u) [Fintype W] [DecidableEq W] (D : Digraph W),
      N ≤ Fintype.card W → (∀ x, θ * Fintype.card W ≤ (D.outDegree x : ℝ)) →
      ∃ k m : ℕ, ∃ Q : RegularStateModel D ε d k m,
        0 < m ∧ l ≤ k ∧ k ≤ M ∧ (1 - ζ) * Fintype.card W ≤ (k : ℝ) * m ∧
        ∀ i, ρ * k < (Q.reduced.outDegree i : ℝ) := by
  classical
  obtain ⟨N₀, hN₀⟩ := exists_density_state_orientation.{u} hρ hρ1 hτ
  obtain ⟨L, hL⟩ := exists_nat_gt (1 / ε)
  let l₀ := max (2 * max N₀ l) L
  obtain ⟨M, N, hMN⟩ := simultaneous_matrix_regularity.{u} Bool hε l₀
  refine ⟨M, N, ?_⟩
  intro W _ _ D hn hdeg
  let F : Bool → W → W → ℝ := fun c => if c then exclusiveMatrix D else doubleMatrix D
  have hF0 : ∀ c x y, 0 ≤ F c x y := by
    intro c x y
    cases c
    · exact (doubleMatrix_bounds D x y).1
    · exact (exclusiveMatrix_bounds D x y).1
  have hF1 : ∀ c x y, F c x y ≤ 1 := by
    intro c x y
    cases c
    · exact (doubleMatrix_bounds D x y).2
    · exact (exclusiveMatrix_bounds D x y).2
  obtain ⟨P, m, hm, hcount, hM, hcovered, hreg⟩ := hMN W F hF0 hF1 hn
  let G := goodCells P m
  let S : G → Finset W := fun i => i.1
  letI : LinearOrder G := LinearOrder.lift' (Fintype.equivFin G) (Fintype.equivFin G).injective
  have hlarge : 1 ≤ ε * G.card := by
    have hLG : (L : ℝ) ≤ G.card := by exact_mod_cast (show L ≤ G.card by exact hcount.trans' (le_max_right _ _))
    have hh := (div_le_iff₀ hε).mp (hL.le.trans hLG)
    nlinarith
  have hmissing := regularStateMask_missing_bound F G hreg hlarge hregsmall
  let Mask := regularStateMask F ε S
  obtain ⟨J, hJsize, hJdelete, hJbad⟩ := exists_pruned_clusters Mask hq hmissing
  let S' : J → Finset W := fun i => S i.1
  let a : J → J → ℝ := fun i j => pairAverage (exclusiveMatrix D) (S' i) (S' j)
  let b : J → J → ℝ := fun i j => pairAverage (doubleMatrix D) (S' i) (S' j)
  have hScard : ∀ i : G, (S i).card = m := fun i => goodCells_card P m i.2
  have hSdis : (Set.univ : Set G).PairwiseDisjoint S := by
    intro i _ j _ hij
    exact P.disjoint (goodCells_subset P m i.2) (goodCells_subset P m j.2)
      (fun h => hij (Subtype.ext h))
  have hGupper : (G.card : ℝ) * m ≤ Fintype.card W := by
    have hh := card_le_card (subset_univ (univ.biUnion S))
    rw [clusterUnion_card S hSdis hScard, card_univ, Fintype.card_coe] at hh
    exact_mod_cast hh
  have hJcount : max N₀ l ≤ Fintype.card J := by
    have hk : (2 * max N₀ l : ℕ) ≤ G.card := (le_max_left _ _).trans hcount
    have hkR : (2 : ℝ) * max N₀ l ≤ G.card := by exact_mod_cast hk
    have hGnonneg : (0 : ℝ) ≤ G.card := Nat.cast_nonneg G.card
    have hh : (max N₀ l : ℕ) ≤ J.card := by
      have hhalf : ((max N₀ l : ℕ) : ℝ) ≤ J.card := by
        simp only [Fintype.card_coe] at hJsize
        nlinarith
      exact_mod_cast hhalf
    simpa only [Fintype.card_coe] using hh
  have hrow (i : J) : (ρ + τ + 2 * d + 2 * q) * Fintype.card J ≤
      ∑ j : J, (a i j + b i j) := by
    have hfull := directed_cluster_row_lower D S hSdis hm hScard
      (show ε ≤ θ by linarith) (by simpa only [Fintype.card_coe] using hcovered) hdeg i.1
    have hstrength : (ρ + τ + 2 * d + 2 * q + q) * Fintype.card G ≤
        ∑ j : G, (pairAverage (exclusiveMatrix D) (S i.1) (S j) +
          pairAverage (doubleMatrix D) (S i.1) (S j)) := by
      have hh := mul_le_mul_of_nonneg_right hmargin (show (0 : ℝ) ≤ Fintype.card G by positivity)
      nlinarith
    exact matrix_row_pruned_lower _ (fun j => by
      have ht := directed_pair_densities_partition D (S i.1) (S j)
      have hp := pairAverage_nonneg (fun x y => (exclusiveMatrix_bounds D x y).1) (S j) (S i.1)
      linarith) J (by positivity) hJdelete hstrength
  have hbad (i : J) : ((univ.filter fun j : J => ¬Mask i.1 j.1).card : ℝ) ≤
      (2 * q) * Fintype.card J :=
    pruned_missingPartners_le hq.le hqhalf hJsize hJbad i
  obtain ⟨R, hRdeg, hRstate⟩ := hN₀ J ((le_max_left _ _).trans hJcount)
    (fun i j : J => Mask i.1 j.1)
    (fun _ _ h => regularStateMask_symm F ε S h)
    (fun i => regularStateMask_irrefl F ε S i.1)
    a b (fun i j => pairAverage_nonneg (fun x y => (exclusiveMatrix_bounds D x y).1) _ _)
    (fun i j => pairAverage_le_one (fun x y => (exclusiveMatrix_bounds D x y).2) _ _)
    (fun i j => pairAverage_nonneg (fun x y => (doubleMatrix_bounds D x y).1) _ _)
    (fun i j => double_pair_density_symm D _ _)
    (fun i j => directed_pair_densities_partition D _ _) hd hbad hrow
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let Q : RegularStateModel D ε d (Fintype.card J) m :=
    { clusters := fun i => S' (e i)
      disjoint := by
        intro i _ j _ hij
        apply hSdis (Set.mem_univ _) (Set.mem_univ _)
        intro h
        exact hij (e.injective (Subtype.ext h))
      cluster_card := fun i => hScard (e i).1
      reduced := R.comap e
      state := by
        intro i j hij
        have hh := hRstate (e i) (e j) hij
        exact ⟨hh.1.2.2.2.1, hh.1.2.1, hh.2.1, hh.2.2⟩ }
  have hJupper : Fintype.card J ≤ M := by
    rw [Fintype.card_coe]
    have hJG : J.card ≤ G.card := by
      simpa only [card_univ, Fintype.card_coe] using card_le_card (subset_univ J)
    exact hJG.trans ((card_le_card (goodCells_subset P m)).trans hM)
  have hcoverage : (1 - ζ) * Fintype.card W ≤ (Fintype.card J : ℝ) * m := by
    have hJsize' := mul_le_mul_of_nonneg_right hJsize (show (0 : ℝ) ≤ m by positivity)
    have hsmall := mul_le_mul_of_nonneg_left hGupper hq.le
    have hcovered' : (1 - ε) * Fintype.card W ≤ (G.card : ℝ) * m := hcovered
    have hζ := mul_le_mul_of_nonneg_right hcoverloss (show (0 : ℝ) ≤ Fintype.card W by positivity)
    simp only [Fintype.card_coe] at hJsize' ⊢
    nlinarith
  refine ⟨Fintype.card J, m, Q, hm, (le_max_right _ _).trans hJcount, hJupper, hcoverage, ?_⟩
  intro i
  change ρ * Fintype.card J < ((R.comap e).outDegree i : ℝ)
  rw [Digraph.outDegree_comap_equiv]
  exact hRdeg (e i)

end Rainbow
end DensityHS
