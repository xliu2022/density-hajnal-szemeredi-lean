module

public import DensityHS.Constructions.FiniteBasic

/-!
# A common finite model for the extremal families

Author and maintainer: Xizhi Liu.

The first block is a clique, the second is independent and anticomplete to it,
and both are joined to an equipartite graph.  A final block of isolated vertices
absorbs integer rounding in the first two constructions.
-/

@[expose] public section

namespace DensityHS.Constructions

open Finset

abbrev ConstructionVertices (a b t q z : ℕ) :=
  ((Fin a ⊕ Fin b) ⊕ (Fin t × Fin q)) ⊕ Fin z

def constructionGraph (a b t q z : ℕ) : SimpleGraph (ConstructionVertices a b t q z) :=
  (joinGraph ((⊤ : SimpleGraph (Fin a)) ⊕g (⊥ : SimpleGraph (Fin b)))
    (SimpleGraph.completeEquipartiteGraph t q)) ⊕g (⊥ : SimpleGraph (Fin z))

theorem constructionVertices_card (a b t q z : ℕ) :
    Fintype.card (ConstructionVertices a b t q z) = a + b + t * q + z := by
  simp [ConstructionVertices]

theorem constructionGraph_mass (a b t q z : ℕ) :
    edgeMass (constructionGraph a b t q z) (fun _ => 1) =
      (a : ℝ) * ((a : ℝ) - 1) / 2 + ((a : ℝ) + b) * t * q +
        (t : ℝ) * ((t : ℝ) - 1) * (q : ℝ) ^ 2 / 2 := by
  rw [constructionGraph, edgeMass_sum_one, edgeMass_bot_one, add_zero,
    edgeMass_join_one, edgeMass_sum_one, edgeMass_top_one, edgeMass_bot_one,
    edgeMass_equipartite_one]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
    Nat.cast_add, Nat.cast_mul, add_zero]
  ring

def inCliqueBlock {a b t q z : ℕ} : ConstructionVertices a b t q z → Bool
  | .inl (.inl (.inl _)) => true
  | _ => false

def inActiveBlocks {a b t q z : ℕ} : ConstructionVertices a b t q z → Bool
  | .inl (.inl (.inl _)) => true
  | .inl (.inr _) => true
  | _ => false

def cliqueResource (a b t q z : ℕ) : Finset (ConstructionVertices a b t q z) :=
  Finset.univ.filter (fun v => inCliqueBlock v = true)

def activeResource (a b t q z : ℕ) : Finset (ConstructionVertices a b t q z) :=
  Finset.univ.filter (fun v => inActiveBlocks v = true)

@[simp] theorem mem_cliqueResource {a b t q z : ℕ} (v : ConstructionVertices a b t q z) :
    v ∈ cliqueResource a b t q z ↔ inCliqueBlock v = true := by
  simp [cliqueResource]

@[simp] theorem mem_activeResource {a b t q z : ℕ} (v : ConstructionVertices a b t q z) :
    v ∈ activeResource a b t q z ↔ inActiveBlocks v = true := by
  simp [activeResource]

@[simp] theorem cliqueResource_card (a b t q z : ℕ) :
    (cliqueResource a b t q z).card = a := by
  unfold cliqueResource
  rw [Finset.card_filter]
  simp only [Fintype.sum_sum_type]
  simp [inCliqueBlock]

@[simp] theorem activeResource_card (a b t q z : ℕ) :
    (activeResource a b t q z).card = a + t * q := by
  unfold activeResource
  rw [Finset.card_filter]
  simp only [Fintype.sum_sum_type]
  simp [inActiveBlocks]

/-- The first independent block receives color zero and the other parts
receive the positive colors. -/
def constructionColor {a b t q z : ℕ} : ConstructionVertices a b t q z → Fin (t + 1)
  | .inl (.inr v) => v.1.succ
  | _ => 0

theorem constructionColor_property (a b t q z : ℕ) :
    ∀ u v, (constructionGraph a b t q z).Adj u v →
      constructionColor u ≠ constructionColor v ∨
        (u ∈ cliqueResource a b t q z ∧ v ∈ cliqueResource a b t q z) := by
  rintro (((u | u) | u) | u) (((v | v) | v) | v) h
  all_goals
    simp_all [constructionGraph, joinGraph, constructionColor, inCliqueBlock,
      SimpleGraph.completeEquipartiteGraph_adj]
  all_goals exact (Fin.succ_ne_zero _).symm

theorem construction_clique_uses_two {a b t q z : ℕ}
    {K : Finset (ConstructionVertices a b t q z)}
    (hK : (constructionGraph a b t q z).IsNClique (t + 2) K) :
    2 ≤ (K ∩ cliqueResource a b t q z).card :=
  clique_resource_card_two (constructionGraph a b t q z) (cliqueResource a b t q z)
    constructionColor (constructionColor_property a b t q z) (by simp) hK

theorem constructionA_packing (k b t q z : ℕ) :
    HasPackingNumberAtMost (t + 2) (constructionGraph (2 * k) b t q z) k := by
  apply packing_bound_of_resource (by norm_num : 0 < 2)
    (constructionGraph (2 * k) b t q z) (cliqueResource (2 * k) b t q z)
  · simp
  · intro K hK
    exact construction_clique_uses_two hK

/-- Every large enough clique in the model avoids the independent block
anticomplete to the clique block, as well as all isolated vertices. -/
theorem construction_clique_subset_active {a b t q z : ℕ}
    {K : Finset (ConstructionVertices a b t q z)}
    (hK : (constructionGraph a b t q z).IsNClique (t + 2) K) :
    K ⊆ activeResource a b t q z := by
  have hpos : 0 < (K ∩ cliqueResource a b t q z).card :=
    lt_of_lt_of_le (by norm_num) (construction_clique_uses_two hK)
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  rcases Finset.mem_inter.mp hx with ⟨hxK, hxX⟩
  rcases x with (((x | x) | x) | x)
  all_goals simp only [mem_cliqueResource, inCliqueBlock, Bool.false_eq_true] at hxX
  all_goals try contradiction
  intro v hv
  rcases v with (((v | v) | v) | v)
  · simp [inActiveBlocks]
  · have h := hK.isClique hxK hv (by simp)
    simpa [constructionGraph, joinGraph] using h
  · simp [inActiveBlocks]
  · have h := hK.isClique hxK hv (by simp)
    simpa [constructionGraph, joinGraph] using h

theorem constructionR_packing {a b t q z k : ℕ}
    (hcapacity : a + t * q ≤ (t + 2) * k) :
    HasPackingNumberAtMost (t + 2) (constructionGraph a b t q z) k := by
  apply packing_bound_of_resource (by omega : 0 < t + 2)
    (constructionGraph a b t q z) (activeResource a b t q z)
  · simpa using hcapacity
  · intro K hK
    rw [Finset.inter_eq_left.mpr (construction_clique_subset_active hK), hK.card_eq]

/-- When the anticomplete independent block is empty, the non-resource
vertices have a proper coloring by just the equipartite part labels. -/
def constructionBColor {a t q z : ℕ} (ht : 0 < t) :
    ConstructionVertices a 0 t q z → Fin t
  | .inl (.inl (.inr v)) => Fin.elim0 v
  | .inl (.inr v) => v.1
  | _ => ⟨0, ht⟩

theorem constructionBColor_property {a t q z : ℕ} (ht : 0 < t) :
    ∀ u v, (constructionGraph a 0 t q z).Adj u v →
      u ∉ cliqueResource a 0 t q z → v ∉ cliqueResource a 0 t q z →
        constructionBColor ht u ≠ constructionBColor ht v := by
  rintro (((u | u) | u) | u) (((v | v) | v) | v) h hu hv
  all_goals first
  | exact Fin.elim0 u
  | exact Fin.elim0 v
  | simp_all [constructionGraph, joinGraph, constructionBColor, inCliqueBlock,
      SimpleGraph.completeEquipartiteGraph_adj]

theorem constructionB_packing {i t k q z : ℕ} (hi : 0 < i) (ht : 0 < t) :
    HasPackingNumberAtMost (i + t) (constructionGraph (i * k) 0 t q z) k := by
  apply packing_bound_of_resource hi (constructionGraph (i * k) 0 t q z)
    (cliqueResource (i * k) 0 t q z)
  · simp
  · intro K hK
    have houtside := clique_sdiff_card_le_colors
      (constructionGraph (i * k) 0 t q z) (cliqueResource (i * k) 0 t q z)
      (constructionBColor ht) (constructionBColor_property ht) hK.isClique
    simp only [Fintype.card_fin] at houtside
    have hcard := Finset.card_sdiff_add_card_inter K (cliqueResource (i * k) 0 t q z)
    rw [hK.card_eq] at hcard
    omega

end DensityHS.Constructions
