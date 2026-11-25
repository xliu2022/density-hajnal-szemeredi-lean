module

public import DensityHS.Basic.UniformHypergraph
public import DensityHS.Weighted.UniversalPeeling

/-!
# Finite loopless digraphs and the double-edge neighborhood reduction

Opposite arcs are allowed. A tile has a complete base graph and internal
out-degree at least `r-2` at every one of its `r` vertices.

Author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS

open Finset

attribute [local instance] Classical.propDecidable

/-- A directed graph without loops; digons are allowed. -/
structure Digraph (V : Type*) where
  Arc : V → V → Prop
  loopless : ∀ v, ¬ Arc v v

namespace Digraph

variable {V : Type*}

/-- The graph of pairs carrying at least one arc. -/
def baseGraph (D : Digraph V) : SimpleGraph V where
  Adj u v := D.Arc u v ∨ D.Arc v u
  symm := ⟨by intro u v h; exact h.symm⟩
  loopless := ⟨by intro v h; exact h.elim (D.loopless v) (D.loopless v)⟩

/-- The graph of pairs carrying both opposite arcs. -/
def doubleGraph (D : Digraph V) : SimpleGraph V where
  Adj u v := D.Arc u v ∧ D.Arc v u
  symm := ⟨by intro u v h; exact h.symm⟩
  loopless := ⟨by intro v h; exact D.loopless v h.1⟩

@[simp] theorem baseGraph_adj (D : Digraph V) (u v : V) :
    D.baseGraph.Adj u v ↔ D.Arc u v ∨ D.Arc v u := Iff.rfl

@[simp] theorem doubleGraph_adj (D : Digraph V) (u v : V) :
    D.doubleGraph.Adj u v ↔ D.Arc u v ∧ D.Arc v u := Iff.rfl

/-- Restriction to a specified finite vertex set. -/
def induce (D : Digraph V) (S : Finset V) : Digraph S where
  Arc u v := D.Arc u v
  loopless v := D.loopless v

variable [Fintype V] [DecidableEq V]

noncomputable def outNeighbors (D : Digraph V) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter (D.Arc v)

noncomputable def outDegree (D : Digraph V) (v : V) : ℕ := (D.outNeighbors v).card

@[simp] theorem mem_outNeighbors (D : Digraph V) (v w : V) :
    w ∈ D.outNeighbors v ↔ D.Arc v w := by
  classical
  simp [outNeighbors]

@[simp] theorem not_mem_outNeighbors_self (D : Digraph V) (v : V) :
    v ∉ D.outNeighbors v := by simpa using D.loopless v

noncomputable def arcCount (D : Digraph V) : ℝ := by
  classical
  exact ∑ u, ∑ v, if D.Arc u v then 1 else 0

theorem outDegree_eq_sum (D : Digraph V) (v : V) :
    (D.outDegree v : ℝ) = ∑ w, if D.Arc v w then 1 else 0 := by
  classical
  simp [outDegree, outNeighbors, Finset.sum_boole]

theorem arcCount_eq_sum_outDegree (D : Digraph V) :
    D.arcCount = ∑ v, (D.outDegree v : ℝ) := by
  classical
  simp only [arcCount, outDegree_eq_sum]

theorem induce_outDegree_eq_sum (D : Digraph V) (S : Finset V) (v : S) :
    ((D.induce S).outDegree v : ℝ) = ∑ w ∈ S, if D.Arc v w then 1 else 0 := by
  classical
  rw [outDegree_eq_sum]
  exact Finset.sum_coe_sort S (fun w => if D.Arc v w then (1 : ℝ) else 0)

/-- Restriction discards at most the number of outside vertices. -/
theorem outDegree_le_induce_add_complement (D : Digraph V) (S : Finset V) (v : S) :
    (D.outDegree v : ℝ) ≤ ((D.induce S).outDegree v : ℝ) +
      ((Fintype.card V : ℝ) - S.card) := by
  classical
  rw [outDegree_eq_sum, induce_outDegree_eq_sum, ← S.sum_add_sum_compl]
  have hout : (∑ w ∈ Sᶜ, if D.Arc v w then (1 : ℝ) else 0) ≤ ∑ _w ∈ Sᶜ, (1 : ℝ) := by
    apply Finset.sum_le_sum
    intro w _
    split_ifs <;> norm_num
  have hcard : S.card ≤ Fintype.card V := Finset.card_le_univ S
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_compl,
    Nat.cast_sub hcard] at hout
  linarith

/-- Pairwise arc counting: the first arc uses an unordered pair and only a
double edge can contribute an additional arc. -/
theorem arcCount_le_pairs_add_doubleEdges (D : Digraph V) :
    2 * D.arcCount ≤ (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) +
      2 * edgeMass D.doubleGraph (fun _ => 1) := by
  classical
  have hpair (u v : V) :
      (if D.Arc u v then (1 : ℝ) else 0) + (if D.Arc v u then 1 else 0) ≤
        1 - (if u = v then 1 else 0) + (if D.doubleGraph.Adj u v then 1 else 0) := by
    by_cases huv : u = v
    · subst v
      simp [D.loopless]
    · simp only [huv, if_false, sub_zero, doubleGraph_adj]
      by_cases h₁ : D.Arc u v <;> by_cases h₂ : D.Arc v u <;> simp [h₁, h₂]
  have h := Finset.sum_le_sum (fun u (_hu : u ∈ Finset.univ) =>
    Finset.sum_le_sum (fun v (_hv : v ∈ Finset.univ) => hpair u v))
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at h
  have hrev : (∑ u : V, ∑ v : V, if D.Arc v u then (1 : ℝ) else 0) = D.arcCount := by
    rw [Finset.sum_comm]
    rfl
  have hdiag : (∑ u : V, ∑ v : V, if u = v then (1 : ℝ) else 0) = Fintype.card V := by simp
  have hconst : (∑ _u : V, ∑ _v : V, (1 : ℝ)) = (Fintype.card V : ℝ) ^ 2 := by simp; ring
  rw [hrev, hdiag, hconst] at h
  change D.arcCount + D.arcCount ≤ (Fintype.card V : ℝ) ^ 2 - Fintype.card V +
    (∑ u, ∑ v, if D.doubleGraph.Adj u v then 1 else 0) at h
  have he : 2 * edgeMass D.doubleGraph (fun _ => 1) =
      ∑ u, ∑ v, if D.doubleGraph.Adj u v then (1 : ℝ) else 0 := by
    unfold edgeMass
    simp only [one_mul]
    ring
  rw [← he] at h
  nlinarith

/-- The family used in a fractional `(r,r-2)`-tiling. -/
def IsTile (r : ℕ) (D : Digraph V) (K : Finset V) : Prop :=
  K.card = r ∧ D.baseGraph.IsClique K ∧
    ∀ v ∈ K, r - 2 ≤ (K.filter (D.Arc v)).card

noncomputable def tileFamily (r : ℕ) (D : Digraph V) : Finset (Finset V) := by
  classical
  exact Finset.univ.filter (D.IsTile r)

@[simp] theorem mem_tileFamily (r : ℕ) (D : Digraph V) (K : Finset V) :
    K ∈ D.tileFamily r ↔ D.IsTile r K := by
  classical
  simp [tileFamily]

/-- A perfect fractional `(r,r-2)`-tiling, indexed by its actual vertex sets. -/
def HasPerfectFractionalTiling (r : ℕ) (D : Digraph V) : Prop :=
  ∃ t : D.tileFamily r → ℝ, IsPerfectFamilyTiling (D.tileFamily r) t

/-- A double-edge clique in an out-neighborhood extends to an allowed tile. -/
theorem insert_isTile {r : ℕ} (hr : 2 ≤ r) (D : Digraph V)
    {v₀ : V} {K : Finset V} (hK : D.doubleGraph.IsNClique (r - 1) K)
    (hN : ∀ w ∈ K, D.Arc v₀ w) : D.IsTile r (insert v₀ K) := by
  classical
  have hvK : v₀ ∉ K := fun h => D.loopless v₀ (hN v₀ h)
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem hvK, hK.card_eq]
    omega
  · intro u hu v hv huv
    rcases Finset.mem_insert.mp hu with hu | hu <;> rcases Finset.mem_insert.mp hv with hv | hv
    · exact False.elim (huv (hu.trans hv.symm))
    · subst u
      exact Or.inl (hN v hv)
    · subst v
      exact Or.inr (hN u hu)
    · exact Or.inl (hK.isClique hu hv huv).1
  · intro v hv
    rcases Finset.mem_insert.mp hv with hv | hv
    · subst v
      have hsub : K ⊆ (insert v₀ K).filter (D.Arc v₀) := by
        intro w hw
        exact Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem hw, hN w hw⟩
      have hcard := Finset.card_le_card hsub
      rw [hK.card_eq] at hcard
      omega
    · have hsub : K.erase v ⊆ (insert v₀ K).filter (D.Arc v) := by
        intro w hw
        have hwK := Finset.mem_of_mem_erase hw
        exact Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem hwK,
          (hK.isClique hv hwK (Ne.symm (Finset.mem_erase.mp hw).1)).1⟩
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hv, hK.card_eq] at hcard
      omega

end Digraph

/-- Uniform probability weights on any nonempty finite vertex type. -/
theorem probabilityWeight_uniform {V : Type*} [Fintype V] [Nonempty V] :
    IsProbabilityWeight (fun _ : V => 1 / (Fintype.card V : ℝ)) := by
  have hN : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt Fintype.card_pos)
  refine ⟨fun _ => by positivity, ?_⟩
  simp [hN]

/-- Uniform edge mass is the raw edge count divided by the square of the order. -/
theorem edgeMass_uniform_rescale {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) :
    edgeMass G (fun _ => 1) = (Fintype.card V : ℝ) ^ 2 *
      edgeMass G (fun _ => 1 / (Fintype.card V : ℝ)) := by
  have hN : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt Fintype.card_pos)
  have h := edgeMass_scale (G := G) (p := fun _ => 1) (1 / (Fintype.card V : ℝ))
  simp only [mul_one] at h
  rw [h]
  field_simp

end DensityHS
