module

public import DensityHS.Rainbow.PairOrientation

/-!
# Exact single and double states in a reduced digraph

Dense double pairs are kept in both directions.  Otherwise only eligible
single directions are used, and two eligible directions share one coin.

Formalization author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS.Rainbow

attribute [local instance] Classical.propDecidable

variable {I : Type*} [Fintype I] [LinearOrder I]

noncomputable def forwardState (A B : I → I → Prop) (e : I × I) (b : Bool) : ℝ :=
  if e.1 < e.2 then
    if B e.1 e.2 then 1 else
      if A e.1 e.2 then (if A e.2 e.1 then selectionCoin b else 1) else 0
  else 0

noncomputable def backwardState (A B : I → I → Prop) (e : I × I) (b : Bool) : ℝ :=
  if e.1 < e.2 then
    if B e.1 e.2 then 1 else
      if A e.2 e.1 then (if A e.1 e.2 then selectionCoin (!b) else 1) else 0
  else 0

theorem forwardState_binary (A B : I → I → Prop) (e : I × I) (b : Bool) :
    forwardState A B e b = 0 ∨ forwardState A B e b = 1 := by
  unfold forwardState
  split_ifs <;> cases b <;> norm_num [selectionCoin]

theorem backwardState_binary (A B : I → I → Prop) (e : I × I) (b : Bool) :
    backwardState A B e b = 0 ∨ backwardState A B e b = 1 := by
  unfold backwardState
  split_ifs <;> cases b <;> norm_num [selectionCoin]

theorem pairStates_zero (A B : I → I → Prop) (e : I × I) (he : ¬e.1 < e.2) (b : Bool) :
    forwardState A B e b = 0 ∧ backwardState A B e b = 0 := by
  simp only [forwardState, backwardState, he, ite_false, and_self]

theorem forwardState_spec (A B : I → I → Prop) {i j : I} (hij : i < j) (b : Bool)
    (h : forwardState A B (i, j) b = 1) :
    (B i j ∨ A i j) ∧ (backwardState A B (i, j) b = 1 ↔ B i j) := by
  by_cases hB : B i j <;> by_cases hA : A i j <;> by_cases hA' : A j i <;>
    cases b <;> simp_all [forwardState, backwardState, selectionCoin]

theorem backwardState_spec (A B : I → I → Prop) {i j : I} (hij : i < j) (b : Bool)
    (h : backwardState A B (i, j) b = 1) :
    (B i j ∨ A j i) ∧ (forwardState A B (i, j) b = 1 ↔ B i j) := by
  by_cases hB : B i j <;> by_cases hA : A i j <;> by_cases hA' : A j i <;>
    cases b <;> simp_all [forwardState, backwardState, selectionCoin]

theorem stateOrientation_arc_spec (A B : I → I → Prop)
    (hB : Symmetric B) (ω : I × I → Bool) {i j : I}
    (h : (pairOrientation (forwardState A B) (backwardState A B) ω).Arc i j) :
    (B i j ∨ A i j) ∧
      ((pairOrientation (forwardState A B) (backwardState A B) ω).Arc j i ↔ B i j) := by
  rcases h with ⟨hij, hf⟩ | ⟨hji, hb⟩
  · have hh := forwardState_spec A B hij (ω (i, j)) hf
    refine ⟨hh.1, ?_⟩
    simpa only [pairOrientation, not_lt.mpr hij.le, hij, false_and, true_and, false_or] using hh.2
  · have hh := backwardState_spec A B hji (ω (j, i)) hb
    have hBB : B j i ↔ B i j := ⟨fun h => hB h, fun h => hB h⟩
    refine ⟨hh.1.imp (fun h => hB h) id, ?_⟩
    simpa only [pairOrientation, not_lt.mpr hji.le, hji, false_and, true_and, or_false] using hh.2.trans hBB

end DensityHS.Rainbow
