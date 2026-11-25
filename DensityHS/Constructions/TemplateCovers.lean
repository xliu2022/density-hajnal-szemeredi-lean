module

public import DensityHS.Constructions.FamilyDistance
public import DensityHS.Constructions.FiniteBasic
public import DensityHS.Basic.EnvelopeStrict

/-!
# Explicit fractional covers of the extremal graphons

Author and maintainer: Xizhi Liu.

The finite template constraints are imposed on ordered tuples and permit
repeated clique-cell labels. Their pullbacks are therefore genuine kernel
covers, not covers of the loopless graph obtained by deleting diagonal cells.
-/

@[expose] public section

namespace DensityHS.Constructions

open MeasureTheory Set Filter Finset

variable {I : Type*} [Fintype I] [Nonempty I]

def IsTemplateCover (r : ℕ) (A : FiniteTemplate I) (c : I → ℝ) : Prop :=
  (∀ i, 0 ≤ c i ∧ c i ≤ 1) ∧
    ∀ f : Fin r → I, (∀ i j, i ≠ j → 0 < A.entry (f i) (f j)) → 1 ≤ ∑ i, c (f i)

theorem IsTemplateCover.kernel_cover {r : ℕ} {A : FiniteTemplate I} {c : I → ℝ}
    (hc : IsTemplateCover r A c) (p : I → ℝ) :
    Graphon.IsKernelCover r (A.kernel p) unitMeasure (fun x => c (intervalLabel p x)) := by
  letI : MeasurableSpace I := ⊤
  refine ⟨(measurable_of_finite c).comp (measurable_intervalLabel p),
    fun x => hc.1 _, Eventually.of_forall ?_⟩
  intro f hf
  exact hc.2 (fun i => intervalLabel p (f i)) hf

theorem IsTemplateCover.tiling_le_cost {r : ℕ} (hr : 0 < r)
    {A : FiniteTemplate I} {c : I → ℝ} (hc : IsTemplateCover r A c)
    {p : I → ℝ} (hp : IsProbabilityWeight p) :
    Graphon.tilingNumber r (A.kernel p) unitMeasure ≤ ∑ i, p i * c i := by
  exact (Graphon.tilingNumber_le_coverNumber r _ _ hr).trans
    ((Graphon.coverNumber_le_cost (hc.kernel_cover p)).trans_eq (integral_intervalLabel hp c))

noncomputable def ordinaryCover {s : ℕ} (i : ℕ) : Option (Fin s) → ℝ
  | none => 1 / (i : ℝ)
  | some _ => 0

/-- Every ordinary template clique uses at least i clique-cell coordinates. -/
theorem ordinary_template_cover {r i : ℕ} (hi : 1 ≤ i) (hir : i < r) :
    IsTemplateCover r (ordinaryTemplate (r - i)) (ordinaryCover i) := by
  classical
  have hip : (0 : ℝ) < i := by exact_mod_cast (by omega : 0 < i)
  have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hs : 0 < r - i := by omega
  letI : NeZero (r - i) := ⟨Nat.ne_of_gt hs⟩
  refine ⟨?_, ?_⟩
  · intro u
    cases u with
    | none => exact ⟨(one_div_pos.mpr hip).le, (div_le_one hip).mpr hi1⟩
    | some j => norm_num [ordinaryCover]
  · intro f hf
    let X : Finset (Fin r) := univ.filter fun a => f a = none
    let color : Fin r → Fin (r - i) := fun a => (f a).getD 0
    have hcolor : ∀ a b, (⊤ : SimpleGraph (Fin r)).Adj a b →
        a ∉ X → b ∉ X → color a ≠ color b := by
      intro a b hab ha hb he
      have ha' : f a ≠ none := by simpa [X] using ha
      have hb' : f b ≠ none := by simpa [X] using hb
      cases hfa : f a with
      | none => exact ha' hfa
      | some u => cases hfb : f b with
        | none => exact hb' hfb
        | some v =>
          have huv : u = v := by simpa [color, hfa, hfb] using he
          have h := hf a b hab
          simp [hfa, hfb, huv, ordinaryTemplate] at h
    have hK : (⊤ : SimpleGraph (Fin r)).IsNClique r univ := ⟨by simp, by simp⟩
    have hout := clique_sdiff_card_le_colors (⊤ : SimpleGraph (Fin r)) X color hcolor hK.isClique
    have hcard := Finset.card_sdiff_add_card_inter (univ : Finset (Fin r)) X
    simp only [Finset.univ_inter, Finset.card_univ, Fintype.card_fin] at hcard hout
    have hX : i ≤ X.card := by omega
    have hsum : (∑ a, ordinaryCover i (f a)) = (X.card : ℝ) / i := by
      calc
        _ = ∑ a, if f a = none then 1 / (i : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro a _
          cases hfa : f a <;> simp [ordinaryCover]
        _ = _ := by rw [← Finset.sum_filter]; simp [X, div_eq_mul_inv]
    rw [hsum]
    apply (le_div_iff₀ hip).mpr
    simpa using (show (i : ℝ) ≤ X.card by exact_mod_cast hX)

noncomputable def exceptionalCover {t : ℕ} : Option (Option (Fin t)) → ℝ
  | none => 1 / 2
  | some _ => 0

def exceptionalColor {t : ℕ} : Option (Option (Fin t)) → Option (Fin t)
  | none => none
  | some i => i

theorem exceptional_color_property {t : ℕ} (u v : Option (Option (Fin t)))
    (h : 0 < (exceptionalTemplate t).entry u v) :
    exceptionalColor u ≠ exceptionalColor v ∨ (u = none ∧ v = none) := by
  classical
  rcases u with _ | (_ | i) <;> rcases v with _ | (_ | j) <;>
    simp_all [exceptionalTemplate, exceptionalDefect, exceptionalColor]
  split_ifs at h <;> simp_all

theorem exceptional_template_cover {r : ℕ} (hr : 2 ≤ r) :
    IsTemplateCover r (exceptionalTemplate (r - 2)) exceptionalCover := by
  classical
  refine ⟨?_, ?_⟩
  · intro u
    cases u <;> norm_num [exceptionalCover]
  · intro f hf
    let X : Finset (Fin r) := univ.filter fun a => f a = none
    have hcolor : ∀ a b, (⊤ : SimpleGraph (Fin r)).Adj a b →
        exceptionalColor (f a) ≠ exceptionalColor (f b) ∨ (a ∈ X ∧ b ∈ X) := by
      intro a b hab
      simpa only [X, Finset.mem_filter, Finset.mem_univ, true_and] using
        exceptional_color_property (f a) (f b) (hf a b hab)
    have hK : (⊤ : SimpleGraph (Fin r)).IsNClique r univ := ⟨by simp, by simp⟩
    have hX := clique_resource_card_two (⊤ : SimpleGraph (Fin r)) X
      (fun a => exceptionalColor (f a)) hcolor (by simp; omega) hK
    simp only [Finset.univ_inter] at hX
    have hsum : (∑ a, exceptionalCover (f a)) = (X.card : ℝ) / 2 := by
      calc
        _ = ∑ a, if f a = none then (1 / 2 : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro a _
          cases hfa : f a <;> simp [exceptionalCover]
        _ = _ := by rw [← Finset.sum_filter]; simp [X, div_eq_mul_inv]
    rw [hsum]
    have h : (2 : ℝ) ≤ X.card := by exact_mod_cast hX
    linarith

noncomputable def finalCover {s : ℕ} (r : ℕ) : Option (Fin s × Bool) → ℝ
  | none => 1 / (r : ℝ)
  | some (_, b) => if b then 0 else 1 / (r : ℝ)

/-- An r-clique in the final template cannot contain any Z coordinate. -/
theorem final_clique_avoids_zero {r : ℕ} (hr : 2 ≤ r)
    (f : Fin r → Option (Fin (r - 1) × Bool))
    (hf : ∀ i j, i ≠ j → 0 < (finalTemplate (r - 1)).entry (f i) (f j)) :
    ∀ a j, f a ≠ some (j, true) := by
  classical
  intro a j hfa
  have hs : 0 < r - 1 := by omega
  letI : NeZero (r - 1) := ⟨Nat.ne_of_gt hs⟩
  have hsome (b : Fin r) : f b ≠ none := by
    intro hfb
    by_cases hba : b = a
    · subst b
      rw [hfb] at hfa
      contradiction
    · have h := hf a b (Ne.symm hba)
      simp [hfa, hfb, finalTemplate, finalDefect] at h
  let color : Fin r → Fin (r - 1) := fun b => ((f b).getD (0, false)).1
  have hinj : Function.Injective color := by
    intro b c hbc
    by_contra hne
    cases hfb : f b with
    | none => exact hsome b hfb
    | some u => cases hfc : f c with
      | none => exact hsome c hfc
      | some v =>
        rcases u with ⟨u, bu⟩
        rcases v with ⟨v, bv⟩
        have huv : u = v := by simpa [color, hfb, hfc] using hbc
        have h := hf b c hne
        simp [hfb, hfc, huv, finalTemplate, finalDefect] at h
  have hcard := Fintype.card_le_of_injective color hinj
  simp only [Fintype.card_fin] at hcard
  omega

theorem final_template_cover {r : ℕ} (hr : 2 ≤ r) :
    IsTemplateCover r (finalTemplate (r - 1)) (finalCover r) := by
  classical
  have hrp : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (by omega : 1 ≤ r)
  have hb : 0 ≤ 1 / (r : ℝ) ∧ 1 / (r : ℝ) ≤ 1 :=
    ⟨(one_div_pos.mpr hrp).le, (div_le_one hrp).mpr hr1⟩
  refine ⟨?_, ?_⟩
  · intro u
    rcases u with _ | ⟨j, b⟩
    · exact hb
    · cases b
      · exact hb
      · norm_num [finalCover]
  · intro f hf
    have hzero := final_clique_avoids_zero hr f hf
    have he (a : Fin r) : finalCover r (f a) = 1 / (r : ℝ) := by
      cases hfa : f a with
      | none => rfl
      | some u =>
        rcases u with ⟨j, b⟩
        cases b
        · rfl
        · exact (hzero a j hfa).elim
    simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [mul_one_div_cancel hrp.ne']

theorem ordinaryKernel_tiling_le {r i : ℕ} (hi : 1 ≤ i) (hir : i < r) {x : ℝ}
    (hx : x ∈ Icc 0 (1 / (r : ℝ))) :
    Graphon.tilingNumber r (ordinaryKernel r i x) unitMeasure ≤ x := by
  have h := (ordinary_template_cover hi hir).tiling_le_cost (by omega)
    (ordinaryWeight_admissible hir hx)
  have hip : (i : ℝ) ≠ 0 := by exact_mod_cast (by omega : i ≠ 0)
  change Graphon.tilingNumber r (ordinaryKernel r i x) unitMeasure ≤ _ at h
  have he : (∑ u, ordinaryWeight (r - i) ((i : ℝ) * x) u * ordinaryCover i u) = x := by
    simp [Fintype.sum_option, ordinaryWeight, ordinaryCover, hip]
    field_simp
  exact h.trans_eq he

theorem exceptionalKernel_tiling_le {r : ℕ} (hr : 2 ≤ r) {x : ℝ}
    (hx : ADomain r x) :
    Graphon.tilingNumber r (exceptionalKernel r x) unitMeasure ≤ x := by
  have h := (exceptional_template_cover hr).tiling_le_cost (by omega)
    (exceptionalWeight_admissible hr hx)
  have he : (∑ u, exceptionalWeight (r - 2) x u * exceptionalCover u) = x := by
    simp [Fintype.sum_option, exceptionalWeight, exceptionalCover]
    ring
  exact h.trans_eq he

theorem finalKernel_tiling_le {r : ℕ} (hr : 2 ≤ r) {x : ℝ}
    (hx : RDomain r x) {z : Fin (r - 1) → ℝ} (hz : IsProbabilityWeight z) :
    Graphon.tilingNumber r (finalKernel r x z) unitMeasure ≤ x := by
  have h := (final_template_cover hr).tiling_le_cost (by omega)
    (finalWeight_admissible hr hx hz)
  have hrp : (r : ℝ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  have he : (∑ u, finalWeight (r - 1) (1 - (r : ℝ) * x) z u * finalCover r u) = x := by
    simp only [Fintype.sum_option, Fintype.sum_prod_type, Fintype.sum_bool,
      finalWeight, finalCover, Bool.false_eq_true, ↓reduceIte, mul_zero, zero_add]
    simp_rw [sub_mul, Finset.sum_sub_distrib, ← Finset.sum_mul, hz.2, one_mul]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
    field_simp [hrp]
    ring
  exact h.trans_eq he

theorem constructionKernel_tiling_le {r : ℕ} (hr : 3 ≤ r) (t : ConstructionKind r)
    {p : ℝ × (Fin (r - 1) → ℝ)} (hx : p.1 ∈ Icc 0 (1 / (r : ℝ)))
    (hz : IsProbabilityWeight p.2) (hd : constructionDomain r t p.1) :
    Graphon.tilingNumber r (constructionKernel r t p) unitMeasure ≤ p.1 := by
  cases t with
  | ordinary i => exact ordinaryKernel_tiling_le (by omega) (by have := i.isLt; omega) hx
  | exceptional => exact exceptionalKernel_tiling_le (by omega) hd
  | final => exact finalKernel_tiling_le (by omega) hd hz

/-- Every active concrete construction attains its prescribed fractional
tiling value, by its explicit cover and the strict density envelope. -/
theorem active_construction_tiling_eq {r : ℕ} (hr : 3 ≤ r) (t : ConstructionKind r)
    {p : ℝ × (Fin (r - 1) → ℝ)} (hx : p.1 ∈ Icc 0 (1 / (r : ℝ)))
    (hz : IsProbabilityWeight p.2) (hd : constructionDomain r t p.1)
    (hactive : constructionDensity r t p.1 = Phi r p.1) :
    Graphon.tilingNumber r (constructionKernel r t p) unitMeasure = p.1 := by
  have hle := constructionKernel_tiling_le hr t hx hz hd
  apply le_antisymm hle
  by_contra h
  have hlt : Graphon.tilingNumber r (constructionKernel r t p) unitMeasure < p.1 :=
    lt_of_not_ge h
  have hn := Graphon.tilingNumber_nonneg r (constructionKernel r t p) unitMeasure (by omega)
  have hPhi := Phi_strictMonoOn (by omega : 2 ≤ r) ⟨hn, hle.trans hx.2⟩ hx hlt
  have hbound := Graphon.kernel_tilingNumber_density_bound (by omega : 2 ≤ r)
    unitMeasure (constructionKernel r t p)
  rw [density_constructionKernel hr t hx hz hd, hactive] at hbound
  exact hPhi.not_ge hbound

end DensityHS.Constructions

