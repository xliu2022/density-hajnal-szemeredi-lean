module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Regularity.Uniform
public import Mathlib.Tactic

/-!
# Transversal clique embedding in regular pairs

Author and maintainer: Xizhi Liu.

The proof keeps all regularity hypotheses on the original clusters.  At each
step only the candidate pools shrink, so no slicing lemma is required.
-/

@[expose] public section

namespace DensityHS.Regularity

open Finset

variable {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Vertices with fewer than the prescribed proportion of neighbors in a pool. -/
noncomputable def lowDegreeVertices (q : ℝ) (s u : Finset V) : Finset V := by
  classical
  exact s.filter (fun x => (#{y ∈ u | G.Adj x y} : ℝ) < q * u.card)

theorem card_interedges_lowDegree_le (q : ℝ) (s u : Finset V) :
    (Rel.interedges G.Adj (lowDegreeVertices G q s u) u).card ≤
      (lowDegreeVertices G q s u).card * (u.card : ℝ) * q := by
  classical
  refine (Nat.cast_le.2 <|
    (card_le_card <| subset_of_eq (Rel.interedges_eq_biUnion _)).trans
      card_biUnion_le).trans ?_
  simp_rw [Nat.cast_sum, card_map, ← nsmul_eq_mul, smul_mul_assoc, mul_comm (u.card : ℝ)]
  exact sum_le_card_nsmul _ _ _ fun x hx => (mem_filter.mp hx).2.le

theorem edgeDensity_lowDegree_le {q : ℝ} (hq : 0 ≤ q) (s u : Finset V) :
    (G.edgeDensity (lowDegreeVertices G q s u) u : ℝ) ≤ q := by
  rw [SimpleGraph.edgeDensity_def]
  push_cast
  refine div_le_of_le_mul₀ (by positivity) hq ?_
  rw [mul_comm]
  exact card_interedges_lowDegree_le G q s u

/-- For a regular pair, all but an `ε`-fraction of the first cluster have the
expected minimum degree into every sufficiently large pool in the second. -/
theorem card_lowDegree_le {ε q : ℝ} {s t u : Finset V}
    (hq : 0 ≤ q) (hreg : G.IsUniform ε s t)
    (hdensity : q + ε ≤ (G.edgeDensity s t : ℝ))
    (hu : u ⊆ t) (hucard : ε * t.card ≤ (u.card : ℝ)) :
    ((lowDegreeVertices G q s u).card : ℝ) ≤ ε * s.card := by
  classical
  by_contra! hlarge
  have h := hreg (s' := lowDegreeVertices G q s u) (t' := u)
    (filter_subset _ _) hu (by linarith) (by linarith)
  rw [abs_sub_lt_iff] at h
  have hd := edgeDensity_lowDegree_le G hq s u
  linarith

/-- Greedy embedding in candidate pools, using regularity only on the original
clusters.  The selected vertices are pairwise adjacent. -/
theorem exists_transversal_clique_pools (n : ℕ) {ε q η : ℝ}
    (hε : 0 < ε) (hq : 0 < q) (hq1 : q ≤ 1) (hη : 0 < η)
    (S P : Fin n → Finset V)
    (hS : ∀ i, (S i).Nonempty) (hP : ∀ i, P i ⊆ S i)
    (hsize : ∀ i, η * (S i).card ≤ (P i).card)
    (hreg : ∀ i j, i ≠ j → G.IsUniform ε (S i) (S j))
    (hdensity : ∀ i j, i ≠ j → q + ε ≤ (G.edgeDensity (S i) (S j) : ℝ))
    (hsmall : ε * n < η * q ^ (n - 1)) :
    ∃ f : Fin n → V, (∀ i, f i ∈ P i) ∧
      ∀ i j, i ≠ j → G.Adj (f i) (f j) := by
  classical
  induction n generalizing η with
  | zero =>
      exact ⟨Fin.elim0, (fun i => Fin.elim0 i), (fun i => Fin.elim0 i)⟩
  | succ n ih =>
      have hsmall' : ε * ((n : ℝ) + 1) < η * q ^ n := by
        simpa only [Nat.succ_sub_one, Nat.cast_succ] using hsmall
      have hpow : q ^ n ≤ 1 := pow_le_one₀ hq.le hq1
      have hbound : ε * ((n : ℝ) + 1) < η :=
        hsmall'.trans_le (by simpa using mul_le_mul_of_nonneg_left hpow hη.le)
      have hεη : ε < η := by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      let bad : Fin n → Finset V := fun j =>
        lowDegreeVertices G q (S 0) (P j.succ)
      let B : Finset V := Finset.univ.biUnion bad
      have hbadcard (j : Fin n) : ((bad j).card : ℝ) ≤ ε * (S 0).card := by
        apply card_lowDegree_le G hq.le (hreg 0 j.succ (Fin.succ_ne_zero j).symm)
          (hdensity 0 j.succ (Fin.succ_ne_zero j).symm) (hP j.succ)
        exact (mul_le_mul_of_nonneg_right hεη.le (Nat.cast_nonneg _)).trans (hsize _)
      have hBcard : (B.card : ℝ) ≤ (n : ℝ) * ε * (S 0).card := by
        calc
          (B.card : ℝ) ≤ ∑ j : Fin n, ((bad j).card : ℝ) := by
            have hnat : B.card ≤ ∑ j : Fin n, (bad j).card := Finset.card_biUnion_le
            exact_mod_cast hnat
          _ ≤ ∑ _j : Fin n, ε * (S 0).card :=
            Finset.sum_le_sum (fun j _ => hbadcard j)
          _ = (n : ℝ) * ε * (S 0).card := by simp; ring
      have h0pos : (0 : ℝ) < (S 0).card := by exact_mod_cast (hS 0).card_pos
      have hless : (n : ℝ) * ε < η := by nlinarith
      have hBlt : B.card < (P 0).card := by
        exact_mod_cast hBcard.trans_lt
          ((mul_lt_mul_of_pos_right hless h0pos).trans_le (hsize 0))
      obtain ⟨x, hxP, hxB⟩ := Finset.exists_mem_notMem_of_card_lt_card hBlt
      have hxS : x ∈ S 0 := hP 0 hxP
      let P' : Fin n → Finset V := fun j => (P j.succ).filter (G.Adj x)
      have hdegree (j : Fin n) : q * (P j.succ).card ≤ ((P' j).card : ℝ) := by
        apply le_of_not_gt
        intro hj
        apply hxB
        exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _,
          by exact Finset.mem_filter.mpr ⟨hxS, hj⟩⟩
      have hsize' (j : Fin n) : (η * q) * (S j.succ).card ≤ ((P' j).card : ℝ) := by
        calc
          (η * q) * (S j.succ).card = q * (η * (S j.succ).card) := by ring
          _ ≤ q * (P j.succ).card := mul_le_mul_of_nonneg_left (hsize _) hq.le
          _ ≤ _ := hdegree j
      have hsmallIH : ε * n < (η * q) * q ^ (n - 1) := by
        cases n with
        | zero => simpa using mul_pos hη hq
        | succ k =>
            simp only [Nat.succ_sub_one, Nat.cast_succ] at ⊢ hsmall'
            rw [pow_succ] at hsmall'
            nlinarith
      obtain ⟨f, hf, hfadj⟩ := ih (mul_pos hη hq) (fun j => S j.succ) P'
        (fun j => hS j.succ) (fun j => (Finset.filter_subset _ _).trans (hP j.succ))
        hsize' (fun i j hij => hreg i.succ j.succ (by simpa using hij))
        (fun i j hij => hdensity i.succ j.succ (by simpa using hij)) hsmallIH
      refine ⟨Fin.cons x f, ?_, ?_⟩
      · intro i
        cases i using Fin.cases with
        | zero => exact hxP
        | succ i => exact (Finset.mem_filter.mp (hf i)).1
      · intro i j hij
        cases i using Fin.cases with
        | zero =>
            cases j using Fin.cases with
            | zero => exact (hij rfl).elim
            | succ j => exact (Finset.mem_filter.mp (hf j)).2
        | succ i =>
            cases j using Fin.cases with
            | zero => exact (Finset.mem_filter.mp (hf i)).2.symm
            | succ j => exact hfadj i j (fun h => hij (congrArg Fin.succ h))

/-- A pairwise adjacent choice is an injective transversal and its image is an
actual finite clique. -/
theorem transversal_image_isNClique {n : ℕ} (f : Fin n → V)
    (hadj : ∀ i j, i ≠ j → G.Adj (f i) (f j)) :
    ∃ e : Fin n ↪ V, (∀ i, e i = f i) ∧ G.IsNClique n (Finset.univ.map e) := by
  classical
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    exact (hadj i j hne).ne hij
  let e : Fin n ↪ V := ⟨f, hinj⟩
  refine ⟨e, fun _ => rfl, ?_, ?_⟩
  · intro x hx y hy hxy
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hy
    exact hadj i j (fun hij => hxy (congrArg e hij))
  · simp

/-- Transversal clique embedding with the usual minimum-density parameter
`d`.  Every pool may be any sufficiently large subset of its original cluster. -/
theorem exists_regular_transversal (n : ℕ) {ε d α : ℝ}
    (hε : 0 < ε) (hd : ε < d) (hd1 : d - ε ≤ 1) (hα : 0 < α)
    (S P : Fin n → Finset V)
    (hS : ∀ i, (S i).Nonempty) (hP : ∀ i, P i ⊆ S i)
    (hsize : ∀ i, α * (S i).card ≤ (P i).card)
    (hreg : ∀ i j, i ≠ j → G.IsUniform ε (S i) (S j))
    (hdensity : ∀ i j, i ≠ j → d ≤ (G.edgeDensity (S i) (S j) : ℝ))
    (hsmall : ε * n < α * (d - ε) ^ (n - 1)) :
    ∃ e : Fin n ↪ V, (∀ i, e i ∈ P i) ∧
      G.IsNClique n (Finset.univ.map e) := by
  obtain ⟨f, hf, hadj⟩ := exists_transversal_clique_pools G n hε
    (sub_pos.mpr hd) hd1 hα S P hS hP hsize hreg
    (fun i j hij => by simpa only [sub_add_cancel] using hdensity i j hij) hsmall
  obtain ⟨e, he, hclique⟩ := transversal_image_isNClique G f hadj
  exact ⟨e, fun i => he i ▸ hf i, hclique⟩

end DensityHS.Regularity
