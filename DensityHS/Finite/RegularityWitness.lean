module

public import DensityHS.Finite.PartitionEnergy

/-!
# Simultaneous witnesses of irregular matrix pairs

Author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS.MatrixRegularity

open Finset Fintype
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def irregularWitness (F : V → V → ℝ) (ε : ℝ) (S T : Finset V) :
    Finset V × Finset V :=
  if h : ¬IsUniform F ε S T then
    ((not_isUniform_iff F ε S T).mp h |>.choose,
      (not_isUniform_iff F ε S T).mp h |>.choose_spec.2.choose)
  else (S, T)

theorem irregularWitness_spec (F : V → V → ℝ) (ε : ℝ) (S T : Finset V)
    (h : ¬IsUniform F ε S T) :
    (irregularWitness F ε S T).1 ⊆ S ∧ (irregularWitness F ε S T).2 ⊆ T ∧
    (S.card : ℝ)*ε ≤ (irregularWitness F ε S T).1.card ∧
    (T.card : ℝ)*ε ≤ (irregularWitness F ε S T).2.card ∧
    ε ≤ |pairAverage F (irregularWitness F ε S T).1 (irregularWitness F ε S T).2 -
      pairAverage F S T| := by
  rw [irregularWitness, dif_pos h]
  have hw := (not_isUniform_iff F ε S T).mp h
  exact ⟨hw.choose_spec.1, hw.choose_spec.2.choose_spec.1,
    hw.choose_spec.2.choose_spec.2⟩

noncomputable def badPairs (F : V → V → ℝ) (ε : ℝ) (G : Finset (Finset V)) :
    Finset (Finset V × Finset V) :=
  G.offDiag.filter (fun p => ¬IsUniform F ε p.1 p.2)

theorem mem_badPairs {F : V → V → ℝ} {ε : ℝ} {G : Finset (Finset V)} {S T : Finset V} :
    (S,T) ∈ badPairs F ε G ↔ S ∈ G ∧ T ∈ G ∧ S ≠ T ∧ ¬IsUniform F ε S T := by
  simp only [badPairs, Finset.mem_filter, Finset.mem_offDiag, and_assoc]

noncomputable def witnessCuts (F : V → V → ℝ) (ε : ℝ) (G : Finset (Finset V)) :
    Finset (Finset V) :=
  (badPairs F ε G).biUnion (fun p =>
    {(irregularWitness F ε p.1 p.2).1, (irregularWitness F ε p.1 p.2).2})

theorem witnessCuts_card_le (F : V → V → ℝ) (ε : ℝ) (G : Finset (Finset V)) :
    (witnessCuts F ε G).card ≤ 2 * G.card^2 := by
  calc
    _ ≤ ∑ p ∈ badPairs F ε G,
        ({(irregularWitness F ε p.1 p.2).1, (irregularWitness F ε p.1 p.2).2} :
          Finset (Finset V)).card := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ badPairs F ε G, 2 := by
      apply Finset.sum_le_sum
      intro p _
      have h := Finset.card_pair_eq_one_or_two
        (a := (irregularWitness F ε p.1 p.2).1)
        (b := (irregularWitness F ε p.1 p.2).2)
      omega
    _ = 2 * (badPairs F ε G).card := by simp [mul_comm]
    _ ≤ 2 * G.card^2 := by
      gcongr
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans
        (by rw [Finset.offDiag_card, pow_two]; omega)

theorem left_witness_mem_cuts {F : V → V → ℝ} {ε : ℝ} {G : Finset (Finset V)}
    {S T : Finset V} (h : (S,T) ∈ badPairs F ε G) :
    (irregularWitness F ε S T).1 ∈ witnessCuts F ε G :=
  Finset.mem_biUnion.mpr ⟨(S,T), h, by simp⟩

theorem right_witness_mem_cuts {F : V → V → ℝ} {ε : ℝ} {G : Finset (Finset V)}
    {S T : Finset V} (h : (S,T) ∈ badPairs F ε G) :
    (irregularWitness F ε S T).2 ∈ witnessCuts F ε G :=
  Finset.mem_biUnion.mpr ⟨(S,T), h, by simp⟩

noncomputable def realSign (a : ℝ) : ℝ := if 0 ≤ a then 1 else -1

theorem realSign_sq (a : ℝ) : (realSign a)^2 = 1 := by
  unfold realSign
  split_ifs <;> norm_num

theorem mul_realSign (a : ℝ) : a * realSign a = |a| := by
  unfold realSign
  split_ifs with h
  · simp [abs_of_nonneg h]
  · simp [abs_of_neg (lt_of_not_ge h)]

noncomputable def witnessDifference (F : V → V → ℝ) (ε : ℝ) (S T : Finset V) : ℝ :=
  pairAverage F (irregularWitness F ε S T).1 (irregularWitness F ε S T).2 -
    pairAverage F S T

noncomputable def witnessScore (P : Finpartition (Finset.univ : Finset V))
    (F : V → V → ℝ) (ε : ℝ) (G : Finset (Finset V)) (x y : V) : ℝ :=
  if (P.part x, P.part y) ∈ badPairs F ε G then
    if x ∈ (irregularWitness F ε (P.part x) (P.part y)).1 ∧
       y ∈ (irregularWitness F ε (P.part x) (P.part y)).2 then
      realSign (witnessDifference F ε (P.part x) (P.part y))
    else 0
  else 0

theorem witnessScore_sq_le (P : Finpartition (Finset.univ : Finset V))
    (F : V → V → ℝ) (ε : ℝ) (G : Finset (Finset V)) (x y : V) :
    (witnessScore P F ε G x y)^2 ≤ 1 := by
  unfold witnessScore
  split_ifs <;> simp [realSign_sq]

theorem cut_mem_iff_of_partIndex_eq (P : Finpartition (Finset.univ : Finset V))
    (F : Finset (Finset V)) {x y : V}
    (hxy : partIndex (cutPartition P F) x = partIndex (cutPartition P F) y)
    {S : Finset V} (hS : S ∈ F) : x ∈ S ↔ y ∈ S := by
  let Q := cutPartition P F
  have hx := mem_partIndex Q x
  have hy : y ∈ (partIndex Q x).val := by rw [hxy]; exact mem_partIndex Q y
  exact cutPartition_mem_iff P F (partIndex Q x).property hS hx hy

theorem witnessScore_constant_on_cuts (P : Finpartition (Finset.univ : Finset V))
    (F : V → V → ℝ) (ε : ℝ) (G : Finset (Finset V)) :
    ∀ x y x' y', partIndex (cutPartition P (witnessCuts F ε G)) x =
      partIndex (cutPartition P (witnessCuts F ε G)) x' →
    partIndex (cutPartition P (witnessCuts F ε G)) y =
      partIndex (cutPartition P (witnessCuts F ε G)) y' →
    witnessScore P F ε G x y = witnessScore P F ε G x' y' := by
  intro x y x' y' hx hy
  have hparent := cutPartition_refines P (witnessCuts F ε G)
  have hpx : P.part x = P.part x' := by
    have h := congrArg (refinementParent hparent) hx
    simp only [refinementParent_partIndex] at h
    exact congrArg Subtype.val h
  have hpy : P.part y = P.part y' := by
    have h := congrArg (refinementParent hparent) hy
    simp only [refinementParent_partIndex] at h
    exact congrArg Subtype.val h
  unfold witnessScore
  rw [hpx,hpy]
  by_cases h : (P.part x',P.part y') ∈ badPairs F ε G
  · rw [if_pos h,if_pos h]
    have hs := cut_mem_iff_of_partIndex_eq P _ hx (left_witness_mem_cuts h)
    have ht := cut_mem_iff_of_partIndex_eq P _ hy (right_witness_mem_cuts h)
    simp only [hs,ht]
  · rw [if_neg h,if_neg h]

theorem rectangle_residual_sum (P : Finpartition (Finset.univ : Finset V))
    (F : V → V → ℝ) {S T S' T' : Finset V} (hS : S ∈ P.parts) (hT : T ∈ P.parts)
    (hS' : S' ⊆ S) (hT' : T' ⊆ T) :
    (∑ x ∈ S', ∑ y ∈ T', (F x y - pairAverage F (P.part x) (P.part y))) =
      ((S'.card : ℝ)*T'.card) * (pairAverage F S' T' - pairAverage F S T) := by
  have hpart : (∑ x ∈ S', ∑ y ∈ T', pairAverage F (P.part x) (P.part y)) =
      ((S'.card : ℝ)*T'.card) * pairAverage F S T := by
    calc
      _ = ∑ _x ∈ S', ∑ _y ∈ T', pairAverage F S T := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        rw [P.part_eq_of_mem hS (hS' hx), P.part_eq_of_mem hT (hT' hy)]
      _ = _ := by simp [mul_assoc]
  simp_rw [Finset.sum_sub_distrib]
  rw [hpart, mul_sub, card_mul_pairAverage]

/-- On a parent rectangle the signed test extracts exactly the absolute
irregularity discrepancy on its witness rectangle. -/
theorem witnessScore_rectangle_sum (P : Finpartition (Finset.univ : Finset V))
    (F : V → V → ℝ) (ε : ℝ) (G : Finset (Finset V))
    {S T : Finset V} (hS : S ∈ P.parts) (hT : T ∈ P.parts) :
    (∑ x ∈ S, ∑ y ∈ T,
      (F x y - pairAverage F (P.part x) (P.part y)) * witnessScore P F ε G x y) =
    if (S,T) ∈ badPairs F ε G then
      (((irregularWitness F ε S T).1.card : ℝ) * (irregularWitness F ε S T).2.card) *
        |witnessDifference F ε S T|
    else 0 := by
  classical
  have hrewrite : (∑ x ∈ S, ∑ y ∈ T,
      (F x y - pairAverage F (P.part x) (P.part y)) * witnessScore P F ε G x y) =
      ∑ x ∈ S, ∑ y ∈ T, (F x y - pairAverage F S T) *
      (if (S,T) ∈ badPairs F ε G then
        if x ∈ (irregularWitness F ε S T).1 ∧ y ∈ (irregularWitness F ε S T).2 then
          realSign (witnessDifference F ε S T) else 0 else 0) := by
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    simp only [witnessScore, P.part_eq_of_mem hS hx, P.part_eq_of_mem hT hy]
  rw [hrewrite]
  by_cases h : (S,T) ∈ badPairs F ε G
  · simp only [if_pos h]
    obtain ⟨hs,ht,hsl,htl,hd⟩ := irregularWitness_spec F ε S T ((mem_badPairs.mp h).2.2.2)
    let A := (irregularWitness F ε S T).1
    let B := (irregularWitness F ε S T).2
    have hfilter : (∑ x ∈ S, ∑ y ∈ T, (F x y - pairAverage F S T) *
        (if x ∈ A ∧ y ∈ B then realSign (witnessDifference F ε S T) else 0)) =
        (∑ x ∈ A, ∑ y ∈ B, (F x y - pairAverage F S T)) *
          realSign (witnessDifference F ε S T) := by
      calc
        _ = ∑ x ∈ A, ∑ y ∈ T, (F x y - pairAverage F S T) *
            (if x ∈ A ∧ y ∈ B then realSign (witnessDifference F ε S T) else 0) := by
          symm
          apply Finset.sum_subset hs
          intro x hx hxa
          change x ∉ A at hxa
          simp [hxa]
        _ = ∑ x ∈ A, ∑ y ∈ B, (F x y - pairAverage F S T) *
            realSign (witnessDifference F ε S T) := by
          apply Finset.sum_congr rfl
          intro x hx
          calc
            _ = ∑ y ∈ B, (F x y - pairAverage F S T) *
                (if x ∈ A ∧ y ∈ B then realSign (witnessDifference F ε S T) else 0) := by
              symm
              apply Finset.sum_subset ht
              intro y hy hyb
              change y ∉ B at hyb
              simp [hyb]
            _ = _ := by
              apply Finset.sum_congr rfl
              intro y hy
              simp [hx,hy]
        _ = _ := by simp only [Finset.sum_mul]
    rw [hfilter]
    have hres : (∑ x ∈ A, ∑ y ∈ B, (F x y - pairAverage F S T)) =
        ((A.card : ℝ)*B.card) * witnessDifference F ε S T := by
      change _ = ((A.card : ℝ)*B.card) * (pairAverage F A B - pairAverage F S T)
      rw [mul_sub, card_mul_pairAverage]
      simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_assoc]
    rw [hres, mul_assoc, mul_realSign]
  · simp [h]

end DensityHS.MatrixRegularity
