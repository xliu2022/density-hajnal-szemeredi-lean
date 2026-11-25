module

public import DensityHS.Weighted.Induction
public import DensityHS.Weighted.Terminal
public import DensityHS.Weighted.RigidGraphBound
public import DensityHS.Weighted.SupportRigidity

/-!
# The finite weighted clique-cover density theorem

The proof combines compact extremal selection, the support classification,
terminal and rigid cases, and induction through a universal zero-cover vertex.
No optimizer certificate or structural classification is an assumption of the
final theorem.

Author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS

open Weighted.Support

universe u

/-- The extremal case at clique size `s+1` follows from the full theorem at
clique size `s`. -/
theorem extremal_bound_of_smaller_clique_bound {s : ℕ} (hs : 2 ≤ s)
    (hIH : ∀ {W : Type u} [Fintype W] {H : SimpleGraph W} {q d : W → ℝ},
      IsProbabilityWeight q → IsCliqueCover s H d →
      coverCost q d ≤ 1 / (s : ℝ) → edgeMass H q ≤ Phi s (coverCost q d))
    {V : Type u} [Fintype V] {x : ℝ} {G : SimpleGraph V} {p c : V → ℝ}
    (he : ExtremalTriple (s + 1) x G p c) (hx : x ≤ 1 / ((s + 1 : ℕ) : ℝ)) :
    edgeMass G p ≤ Phi (s + 1) (coverCost p c) := by
  classical
  have hr : 3 ≤ s + 1 := by omega
  have hcost := he.budget.trans hx
  obtain hcomplete | ⟨P, _hBne, hcard⟩ := complete_or_three_nonempty_cliques hr G c
    he.optimal.1 (he.saturated (by omega)) he.negative
  · subst G
    exact weighted_complete_cover_bound_nonneg (by omega) he.probability he.optimal.1 hcost
  by_cases hzero : ∃ b ∈ P.middle, c b = 0
  · obtain ⟨b, hb, hcb⟩ := hzero
    apply universal_zero_peeling hs he.probability he.optimal.1 hcb
    · intro v hv
      have hU : IsUniversal G b := by
        apply (mem_universalVertices G b).mp
        rwa [← P.middle_eq_universal]
      exact hU v (Ne.symm hv)
    · simpa only [Nat.cast_add, Nat.cast_one] using hcost
    · intro p' c' hp' hc' hx'
      exact hIH hp' hc' hx'
  have hBpos : ∀ b ∈ P.middle, 0 < c b := by
    intro b hb
    have hn : c b ≠ 0 := fun h => hzero ⟨b, hb, h⟩
    exact lt_of_le_of_ne (he.optimal.1.1 b) (Ne.symm hn)
  by_cases hterminal : ∀ K : Finset V, G.IsNClique (s + 1) K → ∀ z ∈ K, c z ≠ 0
  · exact terminal_cliquePath_bound hr he.probability he.optimal P hcard
      (fun b hb => ne_of_gt (hBpos b hb)) hterminal
  have hnonterminal : ∃ K : Finset V, G.IsNClique (s + 1) K ∧ ∃ z ∈ K, c z = 0 := by
    push_neg at hterminal
    exact hterminal
  obtain ⟨P', z, L, T, j, hC, hcz, hLT, hdisj, hA, hL, hT,
      hj, hcardL, hcardA, hcardT⟩ :=
    P.rigid_cover_classification hr he.extreme (he.saturated (by omega))
      he.negative hcard hBpos hnonterminal
  obtain ⟨lam, μ, _hμ, hstat⟩ := he.stationary
  exact rigid_high_class_bound hr hj he.probability he.positive P' hC hcz hLT hdisj
    hA hL hT hcardL hcardA hcardT hstat hcost

/-- The weighted density theorem for every finite graph, every nonnegative
probability vector, and every feasible fractional clique cover. -/
theorem weighted_clique_cover_bound {r : ℕ} (hr : 2 ≤ r)
    {V : Type u} [Fintype V] {G : SimpleGraph V} {p c : V → ℝ}
    (hp : IsProbabilityWeight p) (hc : IsCliqueCover r G c)
    (hx : coverCost p c ≤ 1 / (r : ℝ)) :
    edgeMass G p ≤ Phi r (coverCost p c) := by
  have hall : ∀ n : ℕ, 2 ≤ n → ∀ {W : Type u} [Fintype W]
      {H : SimpleGraph W} {q d : W → ℝ}, IsProbabilityWeight q →
      IsCliqueCover n H d → coverCost q d ≤ 1 / (n : ℝ) →
      edgeMass H q ≤ Phi n (coverCost q d) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn W instW H q d hq hd hcost
      by_cases hn2 : n = 2
      · subst n
        exact weighted_matching_cover_bound_nonneg hq hd (by norm_num at hcost ⊢; exact hcost)
      have hn3 : 3 ≤ n := by omega
      apply weighted_bound_of_extremal_bound hn3 ?_ hq hd hcost
      intro U instU x J a b he hxb
      have hn_succ : n - 1 + 1 = n := by omega
      have hsmall : ∀ {Z : Type u} [Fintype Z] {K : SimpleGraph Z} {w f : Z → ℝ},
          IsProbabilityWeight w → IsCliqueCover (n - 1) K f →
          coverCost w f ≤ 1 / ((n - 1 : ℕ) : ℝ) →
          edgeMass K w ≤ Phi (n - 1) (coverCost w f) := by
        intro Z instZ K w f hw hf hx'
        exact ih (n - 1) (by omega) (by omega) hw hf hx'
      have he' : ExtremalTriple (n - 1 + 1) x J a b := by rwa [hn_succ]
      have hxb' : x ≤ 1 / ((n - 1 + 1 : ℕ) : ℝ) := by rwa [hn_succ]
      have hbound := extremal_bound_of_smaller_clique_bound (by omega : 2 ≤ n - 1)
        hsmall he' hxb'
      simpa only [hn_succ] using hbound
  exact hall r hr hp hc hx

end DensityHS
