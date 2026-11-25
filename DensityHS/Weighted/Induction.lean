module

public import DensityHS.Weighted.Reduction
public import DensityHS.Weighted.Nonnegative

/-!
# Induction on the number of support atoms

Author and maintainer: Xizhi Liu.

This reduction principle proves an arbitrary weighted-cover bound from the
remaining bound on the concrete extremal triples constructed in Reduction.
It is an induction lemma, not a claim that the final extremal case is already
proved.
-/

@[expose] public section

namespace DensityHS

universe u

/-- Once the selected extreme positive-support cases are bounded, all finite
nonnegative weighted graphs are bounded. The zero-coordinate boundary is
handled by a separate induction on the number of vertices. -/
theorem weighted_bound_of_extremal_bound {r : ℕ} (hr : 3 ≤ r)
    (hextremal : ∀ {W : Type u} [Fintype W] {x : ℝ}
      {H : SimpleGraph W} {q d : W → ℝ},
      ExtremalTriple r x H q d → x ≤ 1 / (r : ℝ) →
      edgeMass H q ≤ Phi r (coverCost q d))
    {V : Type u} [Fintype V] {G : SimpleGraph V} {p c : V → ℝ}
    (hp : IsProbabilityWeight p) (hc : IsCliqueCover r G c)
    (hcost : coverCost p c ≤ 1 / (r : ℝ)) :
    edgeMass G p ≤ Phi r (coverCost p c) := by
  classical
  have hgeneral : ∀ n : ℕ, ∀ {W : Type u} [Fintype W], Fintype.card W = n →
      ∀ {H : SimpleGraph W} {q d : W → ℝ},
      IsProbabilityWeight q → IsCliqueCover r H d → coverCost q d ≤ 1 / (r : ℝ) →
      edgeMass H q ≤ Phi r (coverCost q d) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W instW hcard H q d hq hd hqd
      by_contra hfail
      have hstrict : Phi r (coverCost q d) < edgeMass H q := lt_of_not_ge hfail
      have hx0 : 0 ≤ coverCost q d := coverCost_nonneg hq.1 hd.1
      have hboundary : ∀ (J : SimpleGraph W) (a b : W → ℝ),
          IsProbabilityWeight a → IsCliqueCover r J b → coverCost a b ≤ coverCost q d →
          (∃ v, a v = 0) → edgeMass J a ≤ Phi r (coverCost q d) := by
        intro J a b ha hb hab hz
        have hcardlt : Fintype.card (PositiveSupport a) < n := by
          rw [← hcard]
          exact positiveSupport_card_lt hz
        have hca : coverCost (fun v : PositiveSupport a => a v)
            (fun v : PositiveSupport a => b v) ≤ 1 / (r : ℝ) := by
          rw [coverCost_positiveSupport ha.1]
          exact hab.trans hqd
        have hba : IsCliqueCover r (J.induce {v | 0 < a v})
            (fun v : PositiveSupport a => b v) := hb.restrict {v | 0 < a v}
        have hsmall := ih (Fintype.card (PositiveSupport a)) hcardlt rfl
          (probabilityWeight_positiveSupport ha) hba hca
        rw [edgeMass_positiveSupport ha.1, coverCost_positiveSupport ha.1] at hsmall
        exact hsmall.trans (Phi_monotoneOn hr
          ⟨coverCost_nonneg ha.1 hb.1, hab.trans hqd⟩ ⟨hx0, hqd⟩ hab)
      obtain ⟨J, a, b, he, hedge, hstrict'⟩ := exists_extremalTriple (by omega : 0 < r)
        hq hd (le_refl (coverCost q d)) hstrict hboundary
      have hj := hextremal he hqd
      have hmono := Phi_monotoneOn hr
        ⟨coverCost_nonneg he.probability.1 he.optimal.1.1, he.budget.trans hqd⟩
        ⟨hx0, hqd⟩ he.budget
      exact not_lt_of_ge (hj.trans hmono) hstrict'
  exact hgeneral (Fintype.card V) rfl hp hc hcost

end DensityHS
