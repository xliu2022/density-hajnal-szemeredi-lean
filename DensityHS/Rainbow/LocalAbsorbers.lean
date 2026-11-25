module

public import DensityHS.Rainbow.Absorption

/-!
# Local rainbow absorbers built from common connectors

A rainbow base clique and one disjoint common connector for each target/base
vertex pair form a concrete local absorber.  The two packings are assembled
explicitly by switching the distinguished vertex in each connector.

Formalization author and maintainer: Xizhi Liu.
-/

@[expose] public section

open Finset

namespace DensityHS.Rainbow

attribute [local instance] Classical.propDecidable

variable {V K : Type*} [DecidableEq V] {G : SimpleGraph V}
    {r : ℕ} {C : G.EdgeLabeling K}

theorem IsRainbowClique.perfectOn {S : Finset V} (hS : IsRainbowClique r C S) :
    HasPerfectRainbowPackingOn r C S := by
  classical
  refine ⟨{S}, ⟨⟨?_, ?_⟩, ?_⟩, by simp⟩
  · intro T hT
    simpa only [mem_singleton.mp hT] using hS.1
  · intro T hT U hU hTU
    exact False.elim (hTU ((mem_singleton.mp hT).trans (mem_singleton.mp hU).symm))
  · intro T hT
    simpa only [mem_singleton.mp hT] using hS.2

theorem HasPerfectRainbowPackingOn.indexed_union {I : Type*} (F : Finset I)
    (A : I → Finset V) (hdis : (F : Set I).PairwiseDisjoint A)
    (hA : ∀ i ∈ F, HasPerfectRainbowPackingOn r C (A i)) :
    HasPerfectRainbowPackingOn r C (F.biUnion A) := by
  classical
  have hd : (F.image A : Set (Finset V)).PairwiseDisjoint id := by
    intro X hX Y hY hXY
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hX
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hY
    exact hdis hi hj (fun hij => hXY (congrArg A hij))
  have hh := HasPerfectRainbowPackingOn.biUnion (F.image A) hd (by
    intro X hX
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hX
    exact hA i hi)
  simpa only [image_biUnion, id_eq] using hh

theorem pairwiseDisjoint_insert_roots {I : Type*} [Fintype I]
    (e : I ↪ V) (S : I → Finset V)
    (hdis : (Set.univ : Set I).PairwiseDisjoint S)
    (havoid : ∀ i j, e j ∉ S i) :
    (Set.univ : Set I).PairwiseDisjoint (fun i => Insert.insert (e i) (S i)) := by
  intro i _ j _ hij
  apply Finset.disjoint_left.mpr
  intro v hvi hvj
  rcases mem_insert.mp hvi with hvi | hvi <;> rcases mem_insert.mp hvj with hvj | hvj
  · exact hij (e.injective (hvi.symm.trans hvj))
  · exact havoid j i (hvi ▸ hvj)
  · exact havoid i j (hvj ▸ hvi)
  · exact Finset.disjoint_left.mp (hdis (Set.mem_univ i) (Set.mem_univ j) hij) hvi hvj

theorem biUnion_insert_roots {I : Type*} [Fintype I] (e : I → V) (S : I → Finset V) :
    univ.biUnion (fun i => Insert.insert (e i) (S i)) = univ.image e ∪ univ.biUnion S := by
  classical
  ext v
  simp only [mem_biUnion, mem_insert, mem_univ, true_and, mem_union, mem_image]
  aesop

/-- A common one-clique connector avoids both roots and extends either root
to an actual rainbow clique. -/
def IsCommonConnector (r : ℕ) (C : G.EdgeLabeling K) (x y : V) (S : Finset V) : Prop :=
  x ∉ S ∧ y ∉ S ∧ IsRainbowClique r C (Insert.insert x S) ∧
    IsRainbowClique r C (Insert.insert y S)

theorem localAbsorber_of_disjoint_connectors
    (x y : Fin r ↪ V) (S : Fin r → Finset V)
    (hbase : IsRainbowClique r C (univ.image y))
    (hXY : Disjoint (univ.image x) (univ.image y))
    (hdis : (Set.univ : Set (Fin r)).PairwiseDisjoint S)
    (havoid : ∀ i j, x j ∉ S i ∧ y j ∉ S i)
    (hconn : ∀ i, IsCommonConnector r C (x i) (y i) (S i)) :
    IsLocalAbsorber r C (univ.image x) (univ.image y ∪ univ.biUnion S) := by
  classical
  have hSX : Disjoint (univ.biUnion S) (univ.image x) := by
    apply (disjoint_biUnion_left univ S _).mpr
    intro i _
    apply Finset.disjoint_left.mpr
    intro v hv hvX
    obtain ⟨j, _, rfl⟩ := mem_image.mp hvX
    exact (havoid i j).1 hv
  have hSY : Disjoint (univ.biUnion S) (univ.image y) := by
    apply (disjoint_biUnion_left univ S _).mpr
    intro i _
    apply Finset.disjoint_left.mpr
    intro v hv hvY
    obtain ⟨j, _, rfl⟩ := mem_image.mp hvY
    exact (havoid i j).2 hv
  have hpackY : HasPerfectRainbowPackingOn r C (univ.image y ∪ univ.biUnion S) := by
    rw [← biUnion_insert_roots]
    exact HasPerfectRainbowPackingOn.indexed_union univ _
      (by simpa only [coe_univ] using
        pairwiseDisjoint_insert_roots y S hdis (fun i j => (havoid i j).2))
      (fun i _ => (hconn i).2.2.2.perfectOn)
  have hpackX : HasPerfectRainbowPackingOn r C (univ.image x ∪ univ.biUnion S) := by
    rw [← biUnion_insert_roots]
    exact HasPerfectRainbowPackingOn.indexed_union univ _
      (by simpa only [coe_univ] using
        pairwiseDisjoint_insert_roots x S hdis (fun i j => (havoid i j).1))
      (fun i _ => (hconn i).2.2.1.perfectOn)
  refine ⟨disjoint_union_left.mpr ⟨hXY.symm, hSX⟩, hpackY, ?_⟩
  have hp := hbase.perfectOn.union hpackX
    (disjoint_union_right.mpr ⟨hXY.symm, hSY.symm⟩)
  convert hp using 1 <;> ext v <;> simp only [mem_union] <;> tauto

end DensityHS.Rainbow
