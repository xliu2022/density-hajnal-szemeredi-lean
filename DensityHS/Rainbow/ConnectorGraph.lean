module

public import DensityHS.Rainbow.ColorDigraph
public import DensityHS.Finite.Supersaturation

/-!
# Dense auxiliary graphs for common rainbow connectors

Intersect the two outgoing neighbourhoods, whose root palettes are injective.
At each vertex discard the at most two outgoing arcs carrying a root colour.
The double-edge graph of the resulting digraph is properly coloured and has
density above the required Turán threshold.

Formalization author and maintainer: Xizhi Liu.
-/

@[expose] public section

open Finset

namespace DensityHS.Rainbow

attribute [local instance] Classical.propDecidable

variable {V K : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {C : G.EdgeLabeling K} {D : Digraph V}

def rootCompatibleDigraph (D : Digraph V) (C : G.EdgeLabeling K) (x y : V) : Digraph V where
  Arc u v := D.Arc u v ∧ edgeColor C u v ≠ edgeColor C u x ∧
    edgeColor C u v ≠ edgeColor C u y
  loopless u h := D.loopless u h.1

noncomputable def commonOutSet (D : Digraph V) (x y : V) : Finset V :=
  D.outNeighbors x ∩ D.outNeighbors y

theorem commonOutSet_card_lower (D : Digraph V) (x y : V) :
    (D.outDegree x : ℝ) + (D.outDegree y : ℝ) - Fintype.card V ≤
      ((commonOutSet D x y).card : ℝ) := by
  have hh := card_union_add_card_inter (D.outNeighbors x) (D.outNeighbors y)
  have hb := card_le_univ (D.outNeighbors x ∪ D.outNeighbors y)
  have hhR : ((D.outNeighbors x ∪ D.outNeighbors y).card : ℝ) +
      ((commonOutSet D x y).card : ℝ) = (D.outDegree x : ℝ) + D.outDegree y := by
    exact_mod_cast hh
  have hbR : ((D.outNeighbors x ∪ D.outNeighbors y).card : ℝ) ≤ Fintype.card V := by
    exact_mod_cast hb
  linarith

theorem roots_not_mem_commonOutSet (D : Digraph V) (x y : V) :
    x ∉ commonOutSet D x y ∧ y ∉ commonOutSet D x y := by
  constructor
  · intro hx
    exact D.loopless x ((D.mem_outNeighbors _ _).mp (mem_inter.mp hx).1)
  · intro hy
    exact D.loopless y ((D.mem_outNeighbors _ _).mp (mem_inter.mp hy).2)

theorem outgoing_color_fiber_card_le_one (hout : OutgoingColorsDistinct D C)
    (u : V) (c : Option K) :
    ((D.outNeighbors u).filter fun v => edgeColor C u v = c).card ≤ 1 := by
  apply card_le_one.mpr
  intro v hv w hw
  obtain ⟨hvD, hvc⟩ := mem_filter.mp hv
  obtain ⟨hwD, hwc⟩ := mem_filter.mp hw
  exact hout ((D.mem_outNeighbors _ _).mp hvD) ((D.mem_outNeighbors _ _).mp hwD)
    (hvc.trans hwc.symm)

theorem rootCompatible_outDegree_loss (hout : OutgoingColorsDistinct D C)
    (x y u : V) :
    (D.outDegree u : ℝ) ≤ (rootCompatibleDigraph D C x y).outDegree u + 2 := by
  classical
  let Bx := (D.outNeighbors u).filter fun v => edgeColor C u v = edgeColor C u x
  let By := (D.outNeighbors u).filter fun v => edgeColor C u v = edgeColor C u y
  have hsub : D.outNeighbors u ⊆ (rootCompatibleDigraph D C x y).outNeighbors u ∪ (Bx ∪ By) := by
    intro v hv
    by_cases hx : edgeColor C u v = edgeColor C u x
    · exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hv, hx⟩))
    by_cases hy : edgeColor C u v = edgeColor C u y
    · exact mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hv, hy⟩))
    exact mem_union_left _ (((rootCompatibleDigraph D C x y).mem_outNeighbors _ _).mpr
      ⟨(D.mem_outNeighbors _ _).mp hv, hx, hy⟩)
  have hBx : Bx.card ≤ 1 := outgoing_color_fiber_card_le_one hout _ _
  have hBy : By.card ≤ 1 := outgoing_color_fiber_card_le_one hout _ _
  have hcard := (card_le_card hsub).trans (card_union_le _ _)
  have hbad := card_union_le Bx By
  have hh : D.outDegree u ≤ (rootCompatibleDigraph D C x y).outDegree u + 2 := by
    change (D.outNeighbors u).card ≤ ((rootCompatibleDigraph D C x y).outNeighbors u).card + 2
    omega
  exact_mod_cast hh

theorem connector_double_edge_bound (hout : OutgoingColorsDistinct D C)
    (x y : V) (Z : Finset V) (hZ : Z.Nonempty) {ρ : ℝ}
    (hdeg : ∀ v, ρ * Fintype.card V ≤ (D.outDegree v : ℝ)) :
    (Z.card : ℝ) * (ρ * Fintype.card V - Fintype.card V + Z.card - 2) ≤
      (Z.card : ℝ) * (Z.card - 1) / 2 + (Z.card : ℝ) ^ 2 *
        edgeMass ((rootCompatibleDigraph D C x y).induce Z).doubleGraph
          (fun _ => 1 / (Z.card : ℝ)) := by
  classical
  letI : Nonempty Z := ⟨⟨hZ.choose, hZ.choose_spec⟩⟩
  let H := (rootCompatibleDigraph D C x y).induce Z
  have hdegH (v : Z) : ρ * Fintype.card V - Fintype.card V + Z.card - 2 ≤
      (H.outDegree v : ℝ) := by
    have h₁ := hdeg v
    have h₂ := rootCompatible_outDegree_loss hout x y v
    have h₃ := (rootCompatibleDigraph D C x y).outDegree_le_induce_add_complement Z v
    dsimp only [H]
    linarith
  have harcs : (Z.card : ℝ) * (ρ * Fintype.card V - Fintype.card V + Z.card - 2) ≤
      H.arcCount := by
    rw [Digraph.arcCount_eq_sum_outDegree]
    calc
      _ = ∑ _v : Z, (ρ * Fintype.card V - Fintype.card V + Z.card - 2) := by simp; ring
      _ ≤ _ := sum_le_sum fun v _ => hdegH v
  have hedge := H.arcCount_le_pairs_add_doubleEdges
  rw [edgeMass_uniform_rescale] at hedge
  simp only [Fintype.card_coe] at hedge
  dsimp only [H] at harcs hedge
  linarith

theorem connector_density_algebra {t N m ε e : ℝ}
    (ht : 2 ≤ t) (hN : 0 < N) (hm : 0 < m) (hmN : m ≤ N)
    (hcard : (t - 1) * N ≤ t * m) (hε : 0 < ε) (hlarge : 4 ≤ ε * N)
    (hraw : m * ((1 - 1 / (2 * t) + ε) * N - N + m - 2) ≤
      m * (m - 1) / 2 + m ^ 2 * e) :
    (t - 2) / (2 * (t - 1)) + ε / 2 ≤ e := by
  have ht0 : 0 < t := by linarith
  have ht1 : 0 < t - 1 := by linarith
  have hfrac : N / (2 * t) ≤ m / (2 * (t - 1)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  have hraw' : m / 2 - N / (2 * t) + ε * N - 3 / 2 ≤ m * e := by
    have hh : m * (m / 2 - N / (2 * t) + ε * N - 3 / 2) ≤ m * (m * e) := by
      calc
        _ = m * ((1 - 1 / (2 * t) + ε) * N - N + m - 2) - m * (m - 1) / 2 := by ring
        _ ≤ m ^ 2 * e := by linarith
        _ = _ := by ring
    exact (mul_le_mul_iff_right₀ hm).mp hh
  have hident : m / 2 - m / (2 * (t - 1)) = (t - 2) / (2 * (t - 1)) * m := by
    field_simp
    ring
  have hεm := mul_le_mul_of_nonneg_left hmN hε.le
  have hh : ((t - 2) / (2 * (t - 1)) + ε / 2) * m ≤ e * m := by
    nlinarith
  exact (mul_le_mul_iff_left₀ hm).mp hh

/-- Above the colour-degree absorption threshold, the concrete auxiliary
double graph has a uniform positive margin above the Turán density. -/
theorem commonConnector_density {t : ℕ} (ht : 2 ≤ t)
    (hout : OutgoingColorsDistinct D C) (x y : V) {ε : ℝ}
    (hε : 0 < ε) (hlarge : 4 ≤ ε * Fintype.card V)
    (hdeg : ∀ v, (1 - 1 / (2 * (t : ℝ)) + ε) * Fintype.card V ≤
      (D.outDegree v : ℝ)) :
    (commonOutSet D x y).Nonempty ∧
      Phi t 0 + ε / 2 ≤
        edgeMass ((rootCompatibleDigraph D C x y).induce (commonOutSet D x y)).doubleGraph
          (fun _ => 1 / ((commonOutSet D x y).card : ℝ)) := by
  have hN : (0 : ℝ) < Fintype.card V := by
    have hn0 : (0 : ℝ) ≤ Fintype.card V := by positivity
    nlinarith
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0 : ℝ) < t := by linarith
  have hcard0 := commonOutSet_card_lower D x y
  have hx := hdeg x
  have hy := hdeg y
  have hcard : ((t : ℝ) - 1) * Fintype.card V ≤
      (t : ℝ) * (commonOutSet D x y).card := by
    have hcalc : (t : ℝ) *
        (2 * (1 - 1 / (2 * (t : ℝ)) + ε) * Fintype.card V - Fintype.card V) =
        ((t : ℝ) - 1) * Fintype.card V + 2 * t * ε * Fintype.card V := by
      field_simp
      ring
    have hh : 2 * (1 - 1 / (2 * (t : ℝ)) + ε) * Fintype.card V - Fintype.card V ≤
        ((commonOutSet D x y).card : ℝ) := by linarith
    have hh' := mul_le_mul_of_nonneg_left hh ht0.le
    have hpos : 0 ≤ 2 * (t : ℝ) * ε * Fintype.card V := by positivity
    linarith
  have hm : (0 : ℝ) < (commonOutSet D x y).card := by
    nlinarith
  have hZ : (commonOutSet D x y).Nonempty := card_pos.mp (by exact_mod_cast hm)
  refine ⟨hZ, ?_⟩
  rw [Phi_zero ht]
  exact connector_density_algebra htR hN hm
    (by exact_mod_cast card_le_univ (commonOutSet D x y)) hcard hε hlarge
    (connector_double_edge_bound hout x y _ hZ hdeg)

end DensityHS.Rainbow
