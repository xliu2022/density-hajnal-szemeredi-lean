module

public import DensityHS.Constructions.IntegerFamilies
public import DensityHS.Constructions.TemplateCovers

/-!
# Packing feasibility of the exact integer construction families

Author and maintainer: Xizhi Liu.

The explicit template covers also cover actual finite cliques, including
cliques using several vertices of a diagonal clique cell. Their exact
integer costs bound all disjoint clique packings by k.
-/

@[expose] public section

namespace DensityHS.Constructions

open Finset Stability

attribute [local instance] Classical.propDecidable

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I] [Nonempty I]

theorem IsTemplateCover.finite_cover {r : ℕ} {A : FiniteTemplate I} {c : I → ℝ}
    (hc : IsTemplateCover r A c) (f : V → I) :
    IsCliqueCover r (templateGraph A.entry A.symmetric f) (fun v => c (f v)) := by
  refine ⟨fun v => (hc.1 _).1, ?_⟩
  intro T hT
  let e : Fin r ≃ T := (Fintype.equivFinOfCardEq
    (show Fintype.card T=r by simpa using hT.card_eq)).symm
  have hedge (i j : Fin r) (hij : i ≠ j) : 0 < A.entry (f (e i)) (f (e j)) := by
    have hne : (e i).val ≠ (e j).val := fun h => hij (e.injective (Subtype.ext h))
    have h := hT.isClique (e i).property (e j).property hne
    change (e i).val ≠ (e j).val ∧ A.entry (f (e i)) (f (e j))=1 at h
    rw [h.2]
    norm_num
  have hcov := hc.2 (fun i => f (e i)) hedge
  have hsum : (∑ i : Fin r, c (f (e i))) = ∑ v ∈ T, c (f v) := by
    rw [← Finset.sum_coe_sort T (fun v => c (f v))]
    exact e.sum_comp (fun v : T => c (f v))
  rwa [hsum] at hcov

theorem sum_label_cost (f : V → I) (c : I → ℝ) :
    (∑ v, c (f v)) = ∑ i, (fiberCount f i : ℝ)*c i := by
  calc
    (∑ v, c (f v)) = ∑ v, ∑ i, if f v=i then c i else 0 := by simp
    _ = ∑ i, ∑ v, if f v=i then c i else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, fiberCount]

theorem packing_bound_of_cover_sum {r k : ℕ} (G : SimpleGraph V) {c : V → ℝ}
    (hc : IsCliqueCover r G c) (hcost : (∑ v, c v) ≤ k) :
    HasPackingNumberAtMost r G k := by
  intro P hP
  have h : (P.card : ℝ) ≤ (k : ℝ) := by
    calc
      (P.card : ℝ) = ∑ _T ∈ P, (1 : ℝ) := by simp
      _ ≤ ∑ T ∈ P, ∑ v ∈ T, c v :=
        Finset.sum_le_sum (fun T hT => hc.2 T (hP.1 T hT))
      _ = ∑ v ∈ P.biUnion id, c v := (Finset.sum_biUnion hP.2).symm
      _ ≤ ∑ v, c v := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun v _ _ => hc.1 v)
      _ ≤ k := hcost
  exact_mod_cast h

theorem ordinary_finite_feasible {r i k : ℕ} (hi : 1 ≤ i) (hir : i < r)
    (f : V → Option (Fin (r-i))) (hsize : IsOrdinarySize r i k (fiberCount f)) :
    HasPackingNumberAtMost r
      (templateGraph (ordinaryTemplate (r-i)).entry (ordinaryTemplate (r-i)).symmetric f) k := by
  apply packing_bound_of_cover_sum _ ((ordinary_template_cover hi hir).finite_cover f)
  rw [sum_label_cost, Fintype.sum_option]
  simp only [ordinaryCover, mul_zero, Finset.sum_const_zero, add_zero, hsize.1,
    Nat.cast_mul]
  have hi0 : (i : ℝ) ≠ 0 := by exact_mod_cast (by omega : i ≠ 0)
  field_simp
  exact le_rfl

theorem exceptional_finite_feasible {r k : ℕ} (hr : 2 ≤ r)
    (f : V → Option (Option (Fin (r-2)))) (hsize : IsExceptionalSize r k (fiberCount f)) :
    HasPackingNumberAtMost r
      (templateGraph (exceptionalTemplate (r-2)).entry (exceptionalTemplate (r-2)).symmetric f) k := by
  apply packing_bound_of_cover_sum _ ((exceptional_template_cover hr).finite_cover f)
  rw [sum_label_cost, Fintype.sum_option]
  simp only [exceptionalCover, mul_zero, Finset.sum_const_zero, add_zero, hsize.1,
    Nat.cast_mul, Nat.cast_ofNat]
  nlinarith

theorem final_finite_feasible {r k : ℕ} (hr : 2 ≤ r) (hk : r*k ≤ Fintype.card V)
    (f : V → Option (Fin (r-1) × Bool))
    (hsize : IsFinalSize r (Fintype.card V) k (fiberCount f)) :
    HasPackingNumberAtMost r
      (templateGraph (finalTemplate (r-1)).entry (finalTemplate (r-1)).symmetric f) k := by
  apply packing_bound_of_cover_sum _ ((final_template_cover hr).finite_cover f)
  let q := fiberCount f
  have htotal : (q none : ℝ)+(∑ j, (q (some (j,false)) : ℝ))+
      (∑ j, (q (some (j,true)) : ℝ)) = Fintype.card V := by
    have h := sum_fiberCount f
    change (∑ j, q j)=Fintype.card V at h
    have hR : (∑ j, (q j : ℝ))=Fintype.card V := by exact_mod_cast h
    simp only [Fintype.sum_option, Fintype.sum_prod_type, Fintype.sum_bool,
      Finset.sum_add_distrib] at hR
    linarith
  have hzero : (∑ j, (q (some (j,true)) : ℝ)) =
      (Fintype.card V : ℝ)-(r : ℝ)*k := by
    have h := hsize.2.2
    change (∑ j, q (some (j,true)))=Fintype.card V-r*k at h
    have hR := congrArg (fun m : ℕ => (m : ℝ)) h
    simpa only [Nat.cast_sum, Nat.cast_sub hk, Nat.cast_mul] using hR
  have hactive : (q none : ℝ)+(∑ j, (q (some (j,false)) : ℝ)) = (r : ℝ)*k := by
    linarith
  rw [sum_label_cost, Fintype.sum_option]
  change (q none : ℝ)*finalCover r none+
    (∑ j : Fin (r-1) × Bool, (q (some j) : ℝ)*finalCover r (some j)) ≤ k
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, finalCover, Bool.false_eq_true,
    ↓reduceIte, mul_zero, zero_add, ← Finset.sum_mul, ← add_mul]
  rw [hactive]
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  field_simp
  exact le_rfl

/-- Every member of the exact admissible finite family satisfies the
integral packing restriction used by the density theorem. -/
theorem finiteConstructionFamily_feasible {r k : ℕ} (hr : 3 ≤ r)
    (hk : r*k ≤ Fintype.card V) (t : ConstructionKind r) {H : SimpleGraph V}
    (hH : H ∈ finiteConstructionFamily r k t) : HasPackingNumberAtMost r H k := by
  obtain ⟨f, hf, rfl⟩ := hH
  cases t with
  | ordinary i => exact ordinary_finite_feasible (by omega) (by have := i.isLt; omega) f hf.2
  | exceptional => exact exceptional_finite_feasible (by omega) f hf.2
  | final => exact final_finite_feasible (by omega) hk f hf.2

end DensityHS.Constructions
