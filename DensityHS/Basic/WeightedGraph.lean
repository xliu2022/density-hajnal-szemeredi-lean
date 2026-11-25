module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic

/-!
# Finite weighted graphs and fractional clique covers

Author and maintainer: Xizhi Liu.
The definitions follow Section 2.1 of the density Hajnal–Szemerédi manuscript.
In particular `edgeMass` counts each undirected edge once.
-/

@[expose] public section

namespace DensityHS

open Finset

variable {V : Type*} [Fintype V]

/-- A probability vector. Zero coordinates are permitted for compactness arguments. -/
def IsProbabilityWeight (p : V → ℝ) : Prop :=
  (∀ v, 0 ≤ p v) ∧ ∑ v, p v = 1

/-- A nonnegative fractional cover of all unordered `r`-cliques. -/
def IsCliqueCover (r : ℕ) (G : SimpleGraph V) (c : V → ℝ) : Prop :=
  (∀ v, 0 ≤ c v) ∧ ∀ K : Finset V, G.IsNClique r K → 1 ≤ ∑ v ∈ K, c v

/-- The cost of a fractional cover against a vertex weight vector. -/
def coverCost (p c : V → ℝ) : ℝ := ∑ v, p v * c v

/-- Undirected weighted edge mass: one half of the ordered adjacency sum. -/
noncomputable def edgeMass (G : SimpleGraph V) (p : V → ℝ) : ℝ := by
  classical
  exact (∑ u, ∑ v, if G.Adj u v then p u * p v else 0) / 2

/-- Covers can be restricted to the compact unit cube. -/
def coverCube (r : ℕ) (G : SimpleGraph V) : Set (V → ℝ) :=
  {c | IsCliqueCover r G c ∧ ∀ v, c v ≤ 1}

/-- Optimality is expressed directly against every nonnegative fractional cover. -/
def IsOptimalCover (r : ℕ) (G : SimpleGraph V) (p c : V → ℝ) : Prop :=
  IsCliqueCover r G c ∧ ∀ d, IsCliqueCover r G d → coverCost p c ≤ coverCost p d

theorem coverCost_nonneg {p c : V → ℝ}
    (hp : ∀ v, 0 ≤ p v) (hc : ∀ v, 0 ≤ c v) :
    0 ≤ coverCost p c :=
  Finset.sum_nonneg fun v _ => mul_nonneg (hp v) (hc v)

theorem coverCost_mono {p c d : V → ℝ}
    (hp : ∀ v, 0 ≤ p v) (hcd : ∀ v, c v ≤ d v) :
    coverCost p c ≤ coverCost p d :=
  Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (hcd v) (hp v)

theorem coverCost_const (p : V → ℝ) (a : ℝ) :
    coverCost p (fun _ => a) = (∑ v, p v) * a := by
  simp [coverCost, Finset.sum_mul]

theorem constant_clique_cover (r : ℕ) (G : SimpleGraph V) (hr : 0 < r) :
    IsCliqueCover r G (fun _ => 1 / (r : ℝ)) := by
  constructor
  · intro v
    positivity
  · intro K hK
    have hpos : (0 : ℝ) < r := by exact_mod_cast hr
    simp only [Finset.sum_const, nsmul_eq_mul, hK.card_eq]
    exact le_of_eq (mul_one_div_cancel (ne_of_gt hpos)).symm

theorem IsCliqueCover.truncate {r : ℕ} {G : SimpleGraph V} {c : V → ℝ}
    (hc : IsCliqueCover r G c) :
    IsCliqueCover r G (fun v => min (c v) 1) := by
  classical
  constructor
  · intro v
    exact le_min (hc.1 v) (by norm_num)
  · intro K hK
    by_cases hlarge : ∃ v ∈ K, 1 ≤ c v
    · obtain ⟨v, hv, hcv⟩ := hlarge
      have hsingle : min (c v) 1 ≤ ∑ w ∈ K, min (c w) 1 :=
        Finset.single_le_sum (fun w _ => le_min (hc.1 w) (by norm_num)) hv
      simpa [min_eq_right hcv] using hsingle
    · have hsmall : ∀ v ∈ K, min (c v) 1 = c v := by
        intro v hv
        exact min_eq_left (le_of_lt (lt_of_not_ge (fun hv' => hlarge ⟨v, hv, hv'⟩)))
      simpa only [Finset.sum_congr rfl hsmall] using hc.2 K hK

theorem truncated_cover_mem_cube {r : ℕ} {G : SimpleGraph V} {c : V → ℝ}
    (hc : IsCliqueCover r G c) :
    (fun v => min (c v) 1) ∈ coverCube r G :=
  ⟨hc.truncate, fun _ => min_le_right _ _⟩

theorem coverCost_truncate_le {p c : V → ℝ} (hp : ∀ v, 0 ≤ p v) :
    coverCost p (fun v => min (c v) 1) ≤ coverCost p c :=
  coverCost_mono hp (fun _ => min_le_left _ _)

theorem continuous_coverCost (p : V → ℝ) : Continuous (coverCost p) := by
  unfold coverCost
  fun_prop

theorem isCompact_coverCube (r : ℕ) (G : SimpleGraph V) :
    IsCompact (coverCube r G) := by
  classical
  have hclosed : IsClosed {c : V → ℝ | ∀ K : Finset V,
      G.IsNClique r K → 1 ≤ ∑ v ∈ K, c v} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro K
    apply isClosed_iInter
    intro _
    exact isClosed_le continuous_const (by fun_prop)
  have hEq : coverCube r G =
      Set.Icc (fun _ : V => (0 : ℝ)) (fun _ => 1) ∩
        {c : V → ℝ | ∀ K : Finset V, G.IsNClique r K → 1 ≤ ∑ v ∈ K, c v} := by
    ext c
    simp only [coverCube, IsCliqueCover, Set.mem_ofPred_eq, Set.mem_inter_iff,
      Set.mem_Icc, Pi.le_def]
    tauto
  rw [hEq]
  exact isCompact_Icc.inter_right hclosed

theorem coverCube_nonempty (r : ℕ) (G : SimpleGraph V) (hr : 0 < r) :
    (coverCube r G).Nonempty := by
  refine ⟨fun _ => 1 / (r : ℝ), constant_clique_cover r G hr, ?_⟩
  intro v
  have h : (1 : ℝ) ≤ r := by exact_mod_cast hr
  exact (div_le_one (by positivity)).2 h

theorem exists_optimal_cover (r : ℕ) (G : SimpleGraph V) (hr : 0 < r)
    (p : V → ℝ) (hp : ∀ v, 0 ≤ p v) :
    ∃ c, IsOptimalCover r G p c ∧ ∀ v, c v ≤ 1 := by
  obtain ⟨c, hc, hmin⟩ := (isCompact_coverCube r G).exists_isMinOn
    (coverCube_nonempty r G hr) (continuous_coverCost p).continuousOn
  refine ⟨c, ⟨hc.1, ?_⟩, hc.2⟩
  intro d hd
  exact le_trans (hmin (truncated_cover_mem_cube hd)) (coverCost_truncate_le hp)

theorem optimal_cover_cost_le {r : ℕ} {G : SimpleGraph V} {p c : V → ℝ}
    (hr : 0 < r) (hp : IsProbabilityWeight p) (hc : IsOptimalCover r G p c) :
    coverCost p c ≤ 1 / (r : ℝ) := by
  have h := hc.2 (fun _ => 1 / (r : ℝ)) (constant_clique_cover r G hr)
  simpa [coverCost_const, hp.2] using h

end DensityHS
