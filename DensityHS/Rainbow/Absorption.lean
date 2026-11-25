module

public import DensityHS.Rainbow.ColoredGraph
public import DensityHS.Rainbow.AbsorberSelection

/-!
# Absorbing a divisible leftover by actual rainbow packings

This module assembles disjoint local absorbers into a global absorbing set.
Both the unaugmented and augmented tilings are concrete finite clique packings.

Formalization author and maintainer: Xizhi Liu.
-/

@[expose] public section

open Finset

namespace DensityHS.Rainbow

attribute [local instance] Classical.propDecidable

variable {V K : Type*} [DecidableEq V] {G : SimpleGraph V}
    {r : ℕ} {C : G.EdgeLabeling K}

theorem HasPerfectRainbowPackingOn.empty (r : ℕ) (C : G.EdgeLabeling K) :
    HasPerfectRainbowPackingOn r C ∅ := by
  refine ⟨∅, ⟨⟨?_, ?_⟩, ?_⟩, by simp⟩ <;> simp

theorem HasPerfectRainbowPackingOn.union {A B : Finset V}
    (hA : HasPerfectRainbowPackingOn r C A)
    (hB : HasPerfectRainbowPackingOn r C B) (hdis : Disjoint A B) :
    HasPerfectRainbowPackingOn r C (A ∪ B) := by
  classical
  obtain ⟨P, hP, hPA⟩ := hA
  obtain ⟨Q, hQ, hQB⟩ := hB
  have hsubP {T : Finset V} (hT : T ∈ P) : T ⊆ A := by
    rw [← hPA]
    intro v hv
    exact mem_biUnion.mpr ⟨T, hT, hv⟩
  have hsubQ {T : Finset V} (hT : T ∈ Q) : T ⊆ B := by
    rw [← hQB]
    intro v hv
    exact mem_biUnion.mpr ⟨T, hT, hv⟩
  refine ⟨P ∪ Q, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro T hT
    rcases mem_union.mp hT with hT | hT
    · exact hP.1.1 T hT
    · exact hQ.1.1 T hT
  · intro T hT U hU hTU
    rcases mem_union.mp hT with hT | hT <;> rcases mem_union.mp hU with hU | hU
    · exact hP.1.2 hT hU hTU
    · exact hdis.mono (hsubP hT) (hsubQ hU)
    · exact hdis.symm.mono (hsubQ hT) (hsubP hU)
    · exact hQ.1.2 hT hU hTU
  · intro T hT
    rcases mem_union.mp hT with hT | hT
    · exact hP.2 T hT
    · exact hQ.2 T hT
  · simp only [union_biUnion, hPA, hQB]

theorem HasPerfectRainbowPackingOn.biUnion (F : Finset (Finset V))
    (hdis : (F : Set (Finset V)).PairwiseDisjoint id)
    (hF : ∀ A ∈ F, HasPerfectRainbowPackingOn r C A) :
    HasPerfectRainbowPackingOn r C (F.biUnion id) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using HasPerfectRainbowPackingOn.empty r C
  | @insert A F hAF ih =>
    have hdF : (F : Set (Finset V)).PairwiseDisjoint id :=
      hdis.subset (by intro T hT; exact mem_insert_of_mem hT)
    have hd : Disjoint A (F.biUnion id) := by
      apply (disjoint_biUnion_right A F id).mpr
      intro B hB
      exact hdis (mem_insert_self _ _) (mem_insert_of_mem hB)
        (by intro hab; subst B; exact hAF hB)
    simpa only [biUnion_insert, id_eq] using
      (hF A (mem_insert_self _ _)).union
        (ih hdF (fun B hB => hF B (mem_insert_of_mem hB))) hd

/-- A local absorber has its own perfect packing and can also pack the
specified target set together with itself. -/
def IsLocalAbsorber (r : ℕ) (C : G.EdgeLabeling K) (X A : Finset V) : Prop :=
  Disjoint A X ∧ HasPerfectRainbowPackingOn r C A ∧
    HasPerfectRainbowPackingOn r C (A ∪ X)

/-- Assign disjoint absorbers successively to arbitrary blocks of the
leftover.  At each step at most one candidate is lost for each later block. -/
theorem absorb_leftover_of_many_local (hr : 0 < r) (k : ℕ)
    (F : Finset (Finset V)) (U : Finset V)
    (hdis : (F : Set (Finset V)).PairwiseDisjoint id)
    (hF : ∀ A ∈ F, HasPerfectRainbowPackingOn r C A)
    (hFU : Disjoint (F.biUnion id) U) (hU : U.card = r * k)
    (hgood : ∀ X ⊆ U, X.card = r →
      k ≤ (F.filter fun A => IsLocalAbsorber r C X A).card) :
    HasPerfectRainbowPackingOn r C (F.biUnion id ∪ U) := by
  classical
  induction k generalizing F U with
  | zero =>
    have hU0 : U = ∅ := card_eq_zero.mp (by simpa using hU)
    simpa [hU0] using HasPerfectRainbowPackingOn.biUnion F hdis hF
  | succ k ih =>
    have hrU : r ≤ U.card := by rw [hU, Nat.mul_succ]; omega
    obtain ⟨X, hXU, hXcard⟩ := exists_subset_card_eq hrU
    have hsome : (F.filter fun A => IsLocalAbsorber r C X A).Nonempty := by
      apply card_pos.mp
      have hh := hgood X hXU hXcard
      omega
    obtain ⟨A, hA⟩ := hsome
    obtain ⟨hAF, hAX⟩ := mem_filter.mp hA
    have hF'U : Disjoint ((F.erase A).biUnion id) (U \ X) :=
      hFU.mono (biUnion_subset_biUnion_of_subset_left id (erase_subset A F)) sdiff_subset
    have hU' : (U \ X).card = r * k := by
      rw [card_sdiff_of_subset hXU, hU, hXcard, Nat.mul_succ]
      omega
    have hgood' : ∀ Y ⊆ U \ X, Y.card = r →
        k ≤ ((F.erase A).filter fun B => IsLocalAbsorber r C Y B).card := by
      intro Y hYU hYcard
      have hy := hgood Y (hYU.trans sdiff_subset) hYcard
      have hfilter : (F.erase A).filter (fun B => IsLocalAbsorber r C Y B) =
          (F.filter fun B => IsLocalAbsorber r C Y B).erase A := by
        ext B
        simp only [mem_filter, mem_erase]
        tauto
      rw [hfilter]
      by_cases ha : A ∈ F.filter fun B => IsLocalAbsorber r C Y B
      · rw [card_erase_of_mem ha]
        omega
      · rw [erase_eq_of_notMem ha]
        omega
    have hrest := ih (F.erase A) (U \ X)
      (hdis.subset (erase_subset A F))
      (fun B hB => hF B (mem_of_mem_erase hB)) hF'U hU' hgood'
    have hAXrest : Disjoint (A ∪ X) ((F.erase A).biUnion id ∪ (U \ X)) := by
      rw [disjoint_union_left, disjoint_union_right, disjoint_union_right]
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · apply (disjoint_biUnion_right A (F.erase A) id).mpr
        intro B hB
        exact hdis hAF (mem_of_mem_erase hB) (mem_erase.mp hB).1.symm
      · exact hFU.mono
          (by intro v hv; exact mem_biUnion.mpr ⟨A, hAF, hv⟩) sdiff_subset
      · exact hFU.symm.mono hXU
          (biUnion_subset_biUnion_of_subset_left id (erase_subset A F))
      · exact Finset.disjoint_left.mpr fun v hvX hv => (mem_sdiff.mp hv).2 hvX
    have hcover : (A ∪ X) ∪ ((F.erase A).biUnion id ∪ (U \ X)) =
        F.biUnion id ∪ U := by
      have hdecomp : F.biUnion id = A ∪ (F.erase A).biUnion id := by
        calc
          F.biUnion id = (Insert.insert A (F.erase A)).biUnion id :=
            congrArg (fun P : Finset (Finset V) => P.biUnion id) (insert_erase hAF).symm
          _ = _ := by simp only [biUnion_insert, id_eq]
      rw [hdecomp]
      ext v
      simp only [mem_union, mem_sdiff]
      have hx : v ∈ X → v ∈ U := fun hv => hXU hv
      tauto
    rw [← hcover]
    exact hAX.2.2.union hrest hAXrest

/-- A set absorbing every disjoint divisible leftover of at most `r * L`
vertices, while also admitting a perfect rainbow packing itself. -/
def IsAbsorbingSet (r : ℕ) (C : G.EdgeLabeling K) (L : ℕ) (W : Finset V) : Prop :=
  HasPerfectRainbowPackingOn r C W ∧
    ∀ U : Finset V, Disjoint W U → r ∣ U.card → U.card ≤ r * L →
      HasPerfectRainbowPackingOn r C (W ∪ U)

theorem absorbingSet_of_local_family (hr : 0 < r) (L : ℕ)
    (F : Finset (Finset V)) (hdis : (F : Set (Finset V)).PairwiseDisjoint id)
    (hF : ∀ A ∈ F, HasPerfectRainbowPackingOn r C A)
    (hgood : ∀ X : Finset V, X.card = r →
      L ≤ (F.filter fun A => IsLocalAbsorber r C X A).card) :
    IsAbsorbingSet r C L (F.biUnion id) := by
  refine ⟨HasPerfectRainbowPackingOn.biUnion F hdis hF, ?_⟩
  intro U hFU hdiv hsize
  obtain ⟨k, hk⟩ := hdiv
  have hkL : k ≤ L := by nlinarith
  exact absorb_leftover_of_many_local hr k F U hdis hF hFU hk
    (fun X _ hX => hkL.trans (hgood X hX))

noncomputable def candidateConflicts {I : Type*} [Fintype I]
    (A : I → Finset V) : Finset (I × I) := by
  classical
  exact univ.filter fun e => e.1 ≠ e.2 ∧ ¬Disjoint (A e.1) (A e.2)

/-- Produce a genuine small absorbing set from a concrete finite supply of
local absorbers and an explicit numerical selection inequality. -/
theorem exists_absorbingSet_of_candidates [Fintype V] {I : Type*} [Fintype I]
    (hr : 0 < r) (A : I → Finset V) (hne : ∀ i, (A i).Nonempty)
    (hA : ∀ i, HasPerfectRainbowPackingOn r C (A i))
    {a L : ℕ} (ha : 0 < a) (hsize : ∀ i, (A i).card ≤ a)
    (p : unitInterval) {m S T : ℝ} (hS : 0 < S) (hT : 0 < T)
    (hgood : ∀ X : Finset V, X.card = r →
      m ≤ ((univ.filter fun i => IsLocalAbsorber r C X (A i)).card : ℝ))
    (hL : (L : ℝ) ≤ (p : ℝ) * m / 2 - T)
    (hpotential : (p : ℝ) * Fintype.card I / S +
      (p : ℝ) ^ 2 * (candidateConflicts A).card / T +
      Fintype.card {X : Finset V // X.card = r} *
        Real.exp (-selectionDecay * (p : ℝ) * m) < 1) :
    ∃ W : Finset V, (W.card : ℝ) < a * S ∧ IsAbsorbingSet r C L W := by
  classical
  let Good : {X : Finset V // X.card = r} → Finset I := fun X =>
    univ.filter fun i => IsLocalAbsorber r C X.1 (A i)
  have hconf : ∀ e ∈ candidateConflicts A, e.1 ≠ e.2 := by
    intro e he
    exact (mem_filter.mp he).2.1
  obtain ⟨B, hBsize, hBfree, hBgood⟩ :=
    exists_conflict_free_selection p Good (candidateConflicts A) hconf
      (fun X => hgood X.1 X.2) hS hT hpotential
  let F := B.image A
  have hinjB : Set.InjOn A (B : Set I) := by
    intro i hi j hj hij
    by_contra hneij
    obtain ⟨v, hv⟩ := hne i
    have hnondis : ¬Disjoint (A i) (A j) := fun hd =>
      Finset.disjoint_left.mp hd hv (hij ▸ hv)
    exact hBfree (i, j) (mem_filter.mpr ⟨mem_univ _, hneij, hnondis⟩) ⟨hi, hj⟩
  have hFdis : (F : Set (Finset V)).PairwiseDisjoint id := by
    intro X hX Y hY hXY
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hX
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hY
    by_contra hdis
    have hij : i ≠ j := fun heq => hXY (congrArg A heq)
    exact hBfree (i, j) (mem_filter.mpr ⟨mem_univ _, hij, hdis⟩) ⟨hi, hj⟩
  have hFbase : ∀ X ∈ F, HasPerfectRainbowPackingOn r C X := by
    intro X hX
    obtain ⟨i, _, rfl⟩ := mem_image.mp hX
    exact hA i
  have hFgood : ∀ X : Finset V, X.card = r →
      L ≤ (F.filter fun Y => IsLocalAbsorber r C X Y).card := by
    intro X hX
    have hg := hBgood ⟨X, hX⟩
    have heq : Good ⟨X, hX⟩ ∩ B = B.filter fun i => IsLocalAbsorber r C X (A i) := by
      ext i
      simp only [Good, mem_inter, mem_filter, mem_univ, true_and]
      tauto
    rw [heq] at hg
    have hgt : (L : ℝ) < ((B.filter fun i => IsLocalAbsorber r C X (A i)).card : ℝ) :=
      lt_of_le_of_lt hL hg
    dsimp only [F]
    rw [filter_image, card_image_of_injOn
      (hinjB.mono (by intro i hi; exact (mem_filter.mp hi).1))]
    exact_mod_cast hgt.le
  have hFsize : (F.biUnion id).card ≤ a * B.card := by
    calc
      (F.biUnion id).card ≤ ∑ X ∈ F, X.card := card_biUnion_le
      _ ≤ ∑ _X ∈ F, a := by
        apply sum_le_sum
        intro X hX
        obtain ⟨i, _, rfl⟩ := mem_image.mp hX
        exact hsize i
      _ = a * F.card := by simp [mul_comm]
      _ ≤ a * B.card := Nat.mul_le_mul_left a card_image_le
  refine ⟨F.biUnion id, ?_, absorbingSet_of_local_family hr L F hFdis hFbase hFgood⟩
  calc
    ((F.biUnion id).card : ℝ) ≤ (a : ℝ) * B.card := by exact_mod_cast hFsize
    _ < (a : ℝ) * S := mul_lt_mul_of_pos_left hBsize (by exact_mod_cast ha)

end DensityHS.Rainbow
