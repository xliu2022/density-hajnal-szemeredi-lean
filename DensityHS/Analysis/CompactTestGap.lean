module

public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic.Linarith

/-!
# A uniform negative test on a compact set

Author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS.Analysis

open Set

/-- If each point in a compact set fails some continuous scalar test, the
failure has a positive uniform margin. The test may depend on the point. -/
theorem compact_uniform_negative_test {X I : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) (F : I → X → ℝ)
    (hF : ∀ i, Continuous (F i)) (hbad : ∀ x ∈ K, ∃ i, F i x<0) :
    ∃ ε>0, ∀ x∈K, ∃ i, F i x< -ε := by
  let U : Ioi (0:ℝ) → Set X := fun ε => {x | ∃ i, F i x< -ε.1}
  have hopen (ε : Ioi (0:ℝ)) : IsOpen (U ε) := by
    change IsOpen {x | ∃ i, F i x< -ε.1}
    simpa only [setOf_exists] using isOpen_iUnion (fun i => isOpen_lt (hF i) continuous_const)
  have hcover : K ⊆ ⋃ ε, U ε := by
    intro x hx
    obtain ⟨i,hi⟩ := hbad x hx
    refine mem_iUnion.mpr ⟨⟨-F i x/2,by change 0< -F i x/2; linarith⟩,i,?_⟩
    dsimp
    linarith
  have hdir : Directed (· ⊆ ·) U := by
    intro a b
    refine ⟨⟨min a.1 b.1,lt_min a.2 b.2⟩,?_,?_⟩
    · rintro x ⟨i,hi⟩
      exact ⟨i,hi.trans_le (neg_le_neg (min_le_left _ _))⟩
    · rintro x ⟨i,hi⟩
      exact ⟨i,hi.trans_le (neg_le_neg (min_le_right _ _))⟩
  letI : Nonempty (Ioi (0:ℝ)) := ⟨⟨1,by norm_num⟩⟩
  obtain ⟨ε,hε⟩ := hK.elim_directed_cover U hopen hcover hdir
  exact ⟨ε.1,ε.2,fun x hx => hε hx⟩

end DensityHS.Analysis
