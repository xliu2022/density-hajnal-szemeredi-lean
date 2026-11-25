module

public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic.Linarith

/-!
# Compactness and uniform stability with a varying parameter

Author and maintainer: Xizhi Liu.

This file proves the topological implication used in the stability part of the
density Hajnal--Szemerédi argument.  It is an abstract intermediate theorem:
the compact graphon space, the density bound, the equality classification and
the local approximation by near-active constructions still have to be supplied.
None of those graph-theoretic inputs is assumed as an axiom here.

The parameter is part of the compact feasible space.  Consequently the positive
gap obtained below is uniform in that parameter, including transition points.
-/

public section

open Set

namespace DensityHS.Stability

/-- A continuous nonnegative deficit has a positive uniform gap outside any
open neighborhood of its zero set, on a compact feasible set. -/
theorem exists_pos_gap_of_compact
    {Z : Type*} [TopologicalSpace Z]
    {K good : Set Z} (hK : IsCompact K) (hgood : IsOpen good)
    {deficit : Z → ℝ} (hcontinuous : ContinuousOn deficit K)
    (hnonneg : ∀ z ∈ K, 0 ≤ deficit z)
    (hzero : ∀ z ∈ K, deficit z = 0 → z ∈ good) :
    ∃ δ > 0, ∀ z ∈ K, deficit z ≤ δ → z ∈ good := by
  have hbad : IsCompact (K \ good) := hK.diff hgood
  have hpos : ∀ z ∈ K \ good, 0 < deficit z := by
    intro z hz
    apply lt_of_le_of_ne (hnonneg z hz.1)
    intro heq
    exact hz.2 (hzero z hz.1 heq.symm)
  obtain ⟨a, ha, hmin⟩ := hbad.exists_forall_le'
    (hcontinuous.mono fun _ hz => hz.1) hpos
  refine ⟨a / 2, by linarith, ?_⟩
  intro z hz hdef
  by_contra hnot
  have := hmin z ⟨hz, hnot⟩
  linarith

/-- Lower semicontinuity of the constrained quantity makes the feasible pairs
closed, even when the upper bound varies continuously with the parameter. -/
theorem isClosed_feasible_of_lowerSemicontinuous
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    {constraint : X → ℝ} (hconstraint : LowerSemicontinuous constraint)
    {bound : P → ℝ} (hbound : Continuous bound) :
    IsClosed {z : P × X | constraint z.2 ≤ bound z.1} := by
  exact hconstraint.isClosed_epigraph.preimage
    (continuous_snd.prodMk (hbound.comp continuous_fst))

/-- A sharp continuous objective on a compact closed feasible relation has a
uniform stability gap.  The local hypothesis says that each exact extremizer
has an open neighborhood of acceptable pairs; it is where continuity of the
near-active construction family is used in the graphon application. -/
theorem uniform_stability_of_closed_feasible
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    [CompactSpace P] [CompactSpace X]
    (feasible accepted : P → X → Prop)
    (hfeasible : IsClosed {z : P × X | feasible z.1 z.2})
    (target : P → ℝ) (objective : X → ℝ)
    (htarget : Continuous target) (hobjective : Continuous objective)
    (hsharp : ∀ p w, feasible p w → objective w ≤ target p)
    (hlocal : ∀ p w, feasible p w → objective w = target p →
      (p, w) ∈ interior {z : P × X | accepted z.1 z.2}) :
    ∃ δ > 0, ∀ p w, feasible p w → target p - δ ≤ objective w →
      accepted p w := by
  let K : Set (P × X) := {z | feasible z.1 z.2}
  let good : Set (P × X) := interior {z | accepted z.1 z.2}
  let deficit : P × X → ℝ := fun z => target z.1 - objective z.2
  have hcontinuous : Continuous deficit :=
    (htarget.comp continuous_fst).sub (hobjective.comp continuous_snd)
  have hnonneg : ∀ z ∈ K, 0 ≤ deficit z := by
    intro z hz
    exact sub_nonneg.mpr (hsharp z.1 z.2 hz)
  have hzero : ∀ z ∈ K, deficit z = 0 → z ∈ good := by
    intro z hz heq
    apply hlocal z.1 z.2 hz
    exact (sub_eq_zero.mp heq).symm
  obtain ⟨δ, hδ, hgap⟩ := exists_pos_gap_of_compact
    hfeasible.isCompact isOpen_interior hcontinuous.continuousOn hnonneg hzero
  refine ⟨δ, hδ, ?_⟩
  intro p w hfw hnear
  have hd : deficit (p, w) ≤ δ := by
    change target p - objective w ≤ δ
    linarith
  exact interior_subset (s := {z : P × X | accepted z.1 z.2})
    (hgap (p, w) hfw hd)

/-- The preceding stability principle for a lower-semicontinuous constraint.
For graphons, `constraint` will be the fractional clique-tiling number. -/
theorem uniform_stability_of_lowerSemicontinuous_constraint
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    [CompactSpace P] [CompactSpace X]
    (constraint : X → ℝ) (hconstraint : LowerSemicontinuous constraint)
    (bound target : P → ℝ) (objective : X → ℝ)
    (hbound : Continuous bound) (htarget : Continuous target)
    (hobjective : Continuous objective) (accepted : P → X → Prop)
    (hsharp : ∀ p w, constraint w ≤ bound p → objective w ≤ target p)
    (hlocal : ∀ p w, constraint w ≤ bound p → objective w = target p →
      (p, w) ∈ interior {z : P × X | accepted z.1 z.2}) :
    ∃ δ > 0, ∀ p w, constraint w ≤ bound p → target p - δ ≤ objective w →
      accepted p w := by
  exact uniform_stability_of_closed_feasible
    (fun p w => constraint w ≤ bound p) accepted
    (isClosed_feasible_of_lowerSemicontinuous hconstraint hbound)
    target objective htarget hobjective hsharp hlocal

end DensityHS.Stability
