module

public import DensityHS.Finite.RegularStep
public import DensityHS.Stability.RandomRounding
public import DensityHS.Stability.PartSizes

/-!
# Actual edge edits and finite template blow-ups

Author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS.Stability

open Finset Fintype Regularity
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {V I : Type*} [Fintype V] [DecidableEq V]

/-- Number of unordered edges whose status changes. -/
noncomputable def editDistance (G H : SimpleGraph V) : ℕ := by
  classical
  exact ((G.edgeFinset \ H.edgeFinset) ∪ (H.edgeFinset \ G.edgeFinset)).card

theorem two_editDistance_eq (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj] :
    2*(editDistance G H : ℝ) = ∑ u, ∑ v, |indicatorMatrix G u v-indicatorMatrix H u v| := by
  let D := (G \ H) ⊔ (H \ G)
  letI : Fintype D.edgeSet := D.fintypeEdgeSet
  have hD : D.edgeFinset.card = editDistance G H := by
    simp only [D,SimpleGraph.edgeFinset_sup,SimpleGraph.edgeFinset_sdiff,editDistance]
    congr 1
    ext e
    simp
  calc
    2*(editDistance G H : ℝ) = 2*(D.edgeFinset.card : ℝ) := by rw [hD]
    _ = ∑ u, ∑ v, indicatorMatrix D u v := (sum_indicatorMatrix D).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro v _
      by_cases hG : G.Adj u v <;> by_cases hH : H.Adj u v <;>
        simp [indicatorMatrix,D,SimpleGraph.sup_adj,SimpleGraph.sdiff_adj,hG,hH]

theorem editDistance_triangle (G H K : SimpleGraph V) :
    editDistance G K ≤ editDistance G H+editDistance H K := by
  classical
  have h : 2*(editDistance G K : ℝ) ≤ 2*(editDistance G H : ℝ)+2*(editDistance H K : ℝ) := by
    rw [two_editDistance_eq,two_editDistance_eq,two_editDistance_eq,
      ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro u _
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun v _ => abs_sub_le _ _ _)
  exact_mod_cast (show (editDistance G K : ℝ) ≤ (editDistance G H : ℝ)+(editDistance H K : ℝ) by linarith)

/-- If the graphs agree away from a vertex set, every changed edge touches
that set; the resulting edit bound is on actual unordered edges. -/
theorem editDistance_le_of_agree_off (G H : SimpleGraph V) (B : Finset V)
    (hag : ∀ u ∉ B, ∀ v ∉ B, G.Adj u v ↔ H.Adj u v) :
    editDistance G H ≤ Fintype.card V*B.card := by
  classical
  have hp (u v : V) : |indicatorMatrix G u v-indicatorMatrix H u v| ≤
      (if u ∈ B then (1 : ℝ) else 0)+(if v ∈ B then (1 : ℝ) else 0) := by
    have hb : |indicatorMatrix G u v-indicatorMatrix H u v| ≤ 1 := by
      apply abs_le.mpr
      constructor <;> linarith [indicatorMatrix_nonneg G u v,indicatorMatrix_le_one G u v,
        indicatorMatrix_nonneg H u v,indicatorMatrix_le_one H u v]
    by_cases hu : u ∈ B <;> by_cases hv : v ∈ B
    · simp only [hu,hv,ite_true]; linarith
    · simpa only [hu,hv,ite_true,ite_false,add_zero] using hb
    · simpa only [hu,hv,ite_true,ite_false,zero_add] using hb
    · simp only [hu,hv,ite_false,add_zero,indicatorMatrix,hag u hu v hv,sub_self,abs_zero,le_refl]
  have h : 2*(editDistance G H : ℝ) ≤ 2*(Fintype.card V : ℝ)*B.card := by
    rw [two_editDistance_eq]
    calc
      _ ≤ ∑ u : V, ∑ v : V,
          ((if u ∈ B then (1 : ℝ) else 0)+(if v ∈ B then (1 : ℝ) else 0)) :=
        Finset.sum_le_sum (fun u _ => Finset.sum_le_sum (fun v _ => hp u v))
      _ = _ := by simp [Finset.sum_add_distrib,Finset.sum_mul]; ring
  exact_mod_cast (show (editDistance G H : ℝ) ≤ (Fintype.card V : ℝ)*B.card by linarith)

/-- A binary template may have diagonal ones, which become clique parts.
The resulting finite graph itself remains loopless. -/
def templateGraph (A : I → I → ℝ) (hsymm : ∀ i j, A i j=A j i) (f : V → I) : SimpleGraph V where
  Adj u v := u≠v ∧ A (f u) (f v)=1
  symm := ⟨fun u v h => ⟨h.1.symm,by rw [hsymm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem indicatorMatrix_templateGraph (A : I → I → ℝ) (hsymm : ∀ i j, A i j=A j i)
    (hA : ∀ i j, A i j=0 ∨ A i j=1) (f : V → I) (u v : V) :
    indicatorMatrix (templateGraph A hsymm f) u v = if u=v then 0 else A (f u) (f v) := by
  classical
  by_cases huv : u=v
  · subst v
    simp [indicatorMatrix,templateGraph]
  · rcases hA (f u) (f v) with h | h <;> simp [indicatorMatrix,templateGraph,huv,h]

theorem assignmentCost_eq_two_edits (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : I → I → ℝ) (hsymm : ∀ i j, A i j=A j i)
    (hA : ∀ i j, A i j=0 ∨ A i j=1) (f : V → I) :
    assignmentCost (fun u v i j => |indicatorMatrix G u v-A i j|) f =
      2*(editDistance G (templateGraph A hsymm f) : ℝ) := by
  classical
  rw [two_editDistance_eq]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  rw [indicatorMatrix_templateGraph A hsymm hA]
  by_cases huv : u=v
  · subst v
    simp [indicatorMatrix]
  · simp [huv]

theorem templateGraph_edits_le_changed (A : I → I → ℝ) (hsymm : ∀ i j, A i j=A j i)
    (f g : V → I) [DecidableEq I] :
    editDistance (templateGraph A hsymm f) (templateGraph A hsymm g) ≤
      Fintype.card V*(Finset.univ.filter (fun v => f v≠g v)).card := by
  apply editDistance_le_of_agree_off
  intro u hu v hv
  have hu' : f u=g u := by simpa using hu
  have hv' : f v=g v := by simpa using hv
  change (u≠v ∧ A (f u) (f v)=1) ↔ (u≠v ∧ A (g u) (g v)=1)
  rw [hu',hv']

end DensityHS.Stability
