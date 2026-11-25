module

public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic

/-!
# Adjusting finite labelled parts to prescribed integer sizes

Author and maintainer: Xizhi Liu.

Keep as many vertices as possible in every current part, match these
vertices to the corresponding target parts, and extend the finite partial
matching to a permutation. The number moved is controlled by the total
size discrepancy.
-/

@[expose] public section

namespace DensityHS.Stability

open Finset Fintype
open scoped BigOperators

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

def fiberCount (f : V → I) (i : I) : ℕ := (Finset.univ.filter (fun v => f v=i)).card

theorem sum_fiberCount (f : V → I) : (∑ i, fiberCount f i) = Fintype.card V := by
  simp only [fiberCount,Finset.card_filter]
  rw [Finset.sum_comm]
  simp

theorem fiberCount_comp_equiv (f : V → I) (σ : V ≃ V) (i : I) :
    fiberCount (f ∘ σ) i = fiberCount f i := by
  simp only [fiberCount,Finset.card_filter,Function.comp_apply]
  exact σ.sum_comp (fun v => if f v=i then 1 else 0)

/-- Every integer vector of total size `|V|` is realized by a vertex labelling. -/
theorem exists_map_with_fiberCount (q : I → ℕ) (hq : ∑ i, q i = Fintype.card V) :
    ∃ f : V → I, ∀ i, fiberCount f i = q i := by
  classical
  let e : V ≃ (Σ i, Fin (q i)) := Fintype.equivOfCardEq (by
    rw [Fintype.card_sigma]
    simpa only [Fintype.card_fin] using hq.symm)
  refine ⟨fun v => (e v).1,?_⟩
  intro i
  unfold fiberCount
  rw [Finset.card_filter,e.sum_comp (fun z : Σ i, Fin (q i) => if z.1=i then 1 else 0)]
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

/-- Adjust all part sizes exactly, moving at most the total absolute size
discrepancy. The resulting assignment is on the original vertex set. -/
theorem exists_adjustment_to_sizes (f : V → I) (q : I → ℕ)
    (hq : ∑ i, q i = Fintype.card V) :
    ∃ g : V → I, (∀ i, fiberCount g i = q i) ∧
      ((Finset.univ.filter (fun v => f v ≠ g v)).card : ℝ) ≤
        ∑ i, |(fiberCount f i : ℝ)-(q i : ℝ)| := by
  classical
  obtain ⟨h0,hh0⟩ := exists_map_with_fiberCount (V := V) q hq
  have hR : ∀ i, ∃ R : Finset V,
      R ⊆ Finset.univ.filter (fun v => f v=i) ∧ R.card = min (fiberCount f i) (q i) := by
    intro i
    exact Finset.exists_subset_card_eq (min_le_left _ _)
  have hS : ∀ i, ∃ S : Finset V,
      S ⊆ Finset.univ.filter (fun v => h0 v=i) ∧ S.card = min (fiberCount f i) (q i) := by
    intro i
    apply Finset.exists_subset_card_eq
    change min (fiberCount f i) (q i) ≤ fiberCount h0 i
    rw [hh0]
    exact min_le_right _ _
  choose R hRsub hRcard using hR
  choose S hSsub hScard using hS
  let e (i : I) : R i ≃ S i := Fintype.equivOfCardEq (by
    simp only [Fintype.card_coe,hRcard,hScard])
  let J := Σ i, R i
  let a : J → V := fun z => z.2.val
  let b : J → V := fun z => (e z.1 z.2).val
  have ha (z : J) : f (a z) = z.1 :=
    (Finset.mem_filter.mp (hRsub z.1 z.2.property)).2
  have hb (z : J) : h0 (b z) = z.1 :=
    (Finset.mem_filter.mp (hSsub z.1 (e z.1 z.2).property)).2
  have hai : Function.Injective a := by
    rintro ⟨i,x⟩ ⟨j,y⟩ h
    have hij : i=j := (ha ⟨i,x⟩).symm.trans ((congrArg f h).trans (ha ⟨j,y⟩))
    subst j
    have hxy : x=y := Subtype.ext h
    cases hxy
    rfl
  have hbi : Function.Injective b := by
    rintro ⟨i,x⟩ ⟨j,y⟩ h
    have hij : i=j := (hb ⟨i,x⟩).symm.trans ((congrArg h0 h).trans (hb ⟨j,y⟩))
    subst j
    have heq : e i x=e i y := Subtype.ext h
    have hxy := (e i).injective heq
    cases hxy
    rfl
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair a b hai hbi
  let g : V → I := h0 ∘ σ
  have hg : ∀ i, fiberCount g i=q i := fun i => (fiberCount_comp_equiv h0 σ i).trans (hh0 i)
  let B := Finset.univ.image a
  let C := Finset.univ.filter (fun v => f v≠g v)
  have hB : B.card = ∑ i, min (fiberCount f i) (q i) := by
    rw [Finset.card_image_of_injective _ hai,Finset.card_univ]
    change Fintype.card (Σ i, R i) = _
    simp only [Fintype.card_sigma,Fintype.card_coe,hRcard]
  have hagree (v : V) (hv : v ∈ B) : g v=f v := by
    obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hv
    change h0 (σ (a z)) = f (a z)
    rw [hσ,hb,ha]
  have hdisj : Disjoint C B := by
    apply Finset.disjoint_left.mpr
    intro v hv hvB
    exact (Finset.mem_filter.mp hv).2 (hagree v hvB).symm
  have htotal : C.card+B.card ≤ Fintype.card V := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_univ _
  have htotalR : (C.card : ℝ)+(∑ i, min (fiberCount f i) (q i) : ℕ) ≤ Fintype.card V := by
    rw [← hB]
    exact_mod_cast htotal
  have hpoint (i : I) : (fiberCount f i : ℝ) ≤
      (min (fiberCount f i) (q i) : ℕ)+|(fiberCount f i : ℝ)-(q i : ℝ)| := by
    by_cases hi : fiberCount f i ≤ q i
    · rw [Nat.min_eq_left hi]
      exact le_add_of_nonneg_right (abs_nonneg _)
    · rw [Nat.min_eq_right (le_of_not_ge hi)]
      have hir : (q i : ℝ) ≤ fiberCount f i := by exact_mod_cast le_of_not_ge hi
      rw [abs_of_nonneg (sub_nonneg.mpr hir)]
      linarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)
  have hsumcount : (∑ i, (fiberCount f i : ℝ)) = Fintype.card V := by
    exact_mod_cast sum_fiberCount f
  rw [hsumcount,Finset.sum_add_distrib,← Nat.cast_sum] at hsum
  exact ⟨g,hg,by change (C.card : ℝ) ≤ _; linarith⟩

end DensityHS.Stability
