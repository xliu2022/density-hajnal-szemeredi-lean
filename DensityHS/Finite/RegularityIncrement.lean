module

public import DensityHS.Finite.RegularityWitness

/-!
# A quantitative energy increment for simultaneous regularity

Author and maintainer: Xizhi Liu.

All irregular pairs of one matrix are tested at once. The signed witness
has square norm at most the number of ordered vertex pairs. Exact partition
refinement preserves every other matrix's contribution to the energy.
-/

@[expose] public section

namespace DensityHS.MatrixRegularity

open Finset Fintype
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

set_option maxHeartbeats 400000 in
theorem witnessScore_sum (P : Finpartition (Finset.univ : Finset V))
    (F : V → V → ℝ) (ε : ℝ) (G : Finset (Finset V)) (hG : G ⊆ P.parts) :
    (∑ x, ∑ y, (F x y - pairAverage F (P.part x) (P.part y)) * witnessScore P F ε G x y) =
      ∑ p ∈ badPairs F ε G,
        (((irregularWitness F ε p.1 p.2).1.card : ℝ) * (irregularWitness F ε p.1 p.2).2.card) *
          |witnessDifference F ε p.1 p.2| := by
  have hsub : badPairs F ε G ⊆ P.parts ×ˢ P.parts := by
    intro p hp
    have h := mem_badPairs.mp hp
    exact Finset.mem_product.mpr ⟨hG h.1,hG h.2.1⟩
  calc
    _ = ∑ S ∈ P.parts, ∑ T ∈ P.parts, ∑ x ∈ S, ∑ y ∈ T,
        (F x y - pairAverage F (P.part x) (P.part y)) * witnessScore P F ε G x y :=
      (sum_part_rectangles P _).symm
    _ = ∑ S ∈ P.parts, ∑ T ∈ P.parts,
        if (S,T) ∈ badPairs F ε G then
          (((irregularWitness F ε S T).1.card : ℝ) * (irregularWitness F ε S T).2.card) *
            |witnessDifference F ε S T| else 0 := by
      apply Finset.sum_congr rfl
      intro S hS
      apply Finset.sum_congr rfl
      intro T hT
      exact witnessScore_rectangle_sum P F ε G hS hT
    _ = ∑ p ∈ P.parts ×ˢ P.parts,
        if p ∈ badPairs F ε G then
          (((irregularWitness F ε p.1 p.2).1.card : ℝ) * (irregularWitness F ε p.1 p.2).2.card) *
            |witnessDifference F ε p.1 p.2| else 0 :=
      (Finset.sum_product P.parts P.parts (fun p : Finset V × Finset V =>
        if p ∈ badPairs F ε G then
          (((irregularWitness F ε p.1 p.2).1.card : ℝ) * (irregularWitness F ε p.1 p.2).2.card) *
            |witnessDifference F ε p.1 p.2| else 0)).symm
    _ = _ := by rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsub]

theorem irregular_witness_contribution {F : V → V → ℝ} {ε : ℝ} (hε : 0 < ε)
    {G : Finset (Finset V)} {m : ℕ} (hsize : ∀ S ∈ G, S.card = m)
    {S T : Finset V} (hST : (S,T) ∈ badPairs F ε G) :
    ε^3 * (m : ℝ)^2 ≤
      (((irregularWitness F ε S T).1.card : ℝ) * (irregularWitness F ε S T).2.card) *
        |witnessDifference F ε S T| := by
  obtain ⟨hS,hT,hne,hbad⟩ := mem_badPairs.mp hST
  obtain ⟨hs,ht,hsl,htl,hd⟩ := irregularWitness_spec F ε S T hbad
  rw [hsize S hS] at hsl
  rw [hsize T hT] at htl
  change ε ≤ |witnessDifference F ε S T| at hd
  calc
    _ = ((m : ℝ)*ε) * ((m : ℝ)*ε) * ε := by ring
    _ ≤ _ := by gcongr

theorem witnessScore_sum_lower (P : Finpartition (Finset.univ : Finset V))
    (F : V → V → ℝ) {ε : ℝ} (hε : 0 < ε) (G : Finset (Finset V))
    (hG : G ⊆ P.parts) {m : ℕ} (hsize : ∀ S ∈ G, S.card = m) :
    ε^3 * (m : ℝ)^2 * (badPairs F ε G).card ≤
      ∑ x, ∑ y, (F x y - pairAverage F (P.part x) (P.part y)) * witnessScore P F ε G x y := by
  rw [witnessScore_sum P F ε G hG]
  calc
    _ = ∑ _p ∈ badPairs F ε G, ε^3 * (m : ℝ)^2 := by simp [mul_comm]
    _ ≤ _ := Finset.sum_le_sum (fun p hp => irregular_witness_contribution hε hsize hp)

theorem witnessScore_sum_quarter_lower (P : Finpartition (Finset.univ : Finset V))
    (F : V → V → ℝ) {ε : ℝ} (hε : 0 < ε) (G : Finset (Finset V))
    (hG : G ⊆ P.parts) {m : ℕ} (hsize : ∀ S ∈ G, S.card = m)
    (hcover : (Fintype.card V : ℝ)/2 ≤ (G.card : ℝ)*m)
    (hbad : ε*(G.card : ℝ)^2 ≤ (badPairs F ε G).card) :
    ε^4 * (Fintype.card V : ℝ)^2 / 4 ≤
      ∑ x, ∑ y, (F x y - pairAverage F (P.part x) (P.part y)) * witnessScore P F ε G x y := by
  calc
    _ = ε^4 * ((Fintype.card V : ℝ)/2)^2 := by ring
    _ ≤ ε^4 * ((G.card : ℝ)*m)^2 := by gcongr
    _ = ε^3*(m : ℝ)^2*(ε*(G.card : ℝ)^2) := by ring
    _ ≤ ε^3*(m : ℝ)^2*(badPairs F ε G).card := by gcongr
    _ ≤ _ := witnessScore_sum_lower P F hε G hG hsize

/-- A nonregular matrix forces a bounded-size common refinement with a
fixed positive simultaneous energy increment. -/
theorem exists_matrix_energy_increment [Nonempty V]
    (P : Finpartition (Finset.univ : Finset V)) (F : C → V → V → ℝ)
    {ε : ℝ} (hε : 0 < ε) (G : Finset (Finset V)) (hG : G ⊆ P.parts)
    {m : ℕ} (hsize : ∀ S ∈ G, S.card = m)
    (hcover : (Fintype.card V : ℝ)/2 ≤ (G.card : ℝ)*m)
    (c : C) (hbad : ε*(G.card : ℝ)^2 ≤ (badPairs (F c) ε G).card) :
    ∃ Q : Finpartition (Finset.univ : Finset V), Q ≤ P ∧
      Q.parts.card ≤ P.parts.card * 2^(2*P.parts.card^2) ∧
      matrixEnergy P F + ε^8/16*(Fintype.card V : ℝ)^2 ≤ matrixEnergy Q F := by
  classical
  let Q := cutPartition P (witnessCuts (F c) ε G)
  have hQP : Q ≤ P := cutPartition_refines P _
  have hcard : Q.parts.card ≤ P.parts.card * 2^(2*P.parts.card^2) := by
    apply (cutPartition_card_le P _).trans
    gcongr
    apply (witnessCuts_card_le (F c) ε G).trans
    gcongr
  have hcorr := witnessScore_sum_quarter_lower P (F c) hε G hG hsize hcover hbad
  have hbound := matrix_correlation_energy_bound hQP F c (witnessScore P (F c) ε G)
    (witnessScore_constant_on_cuts P (F c) ε G) (witnessScore_sq_le P (F c) ε G)
  have hN : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hlow0 : 0 ≤ ε^4 * (Fintype.card V : ℝ)^2 / 4 := by positivity
  have hsquare : (ε^4 * (Fintype.card V : ℝ)^2 / 4)^2 ≤
      (∑ x, ∑ y, (F c x y - pairAverage (F c) (P.part x) (P.part y)) *
        witnessScore P (F c) ε G x y)^2 := by gcongr
  have hgain : ε^8/16*(Fintype.card V : ℝ)^2 ≤ matrixEnergy Q F - matrixEnergy P F := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hN)).mp
    calc
      _ = (ε^4 * (Fintype.card V : ℝ)^2 / 4)^2 := by ring
      _ ≤ (matrixEnergy Q F - matrixEnergy P F) * (Fintype.card V : ℝ)^2 := hsquare.trans hbound
      _ = _ := by ring
  exact ⟨Q,hQP,hcard,by linarith⟩

end DensityHS.MatrixRegularity
