module

public import DensityHS.Rainbow.Absorption
public import DensityHS.Rainbow.BadEmbeddings
public import Mathlib.Data.Nat.Choose.Bounds

/-!
# Elementary map counts for absorption

Fixing one coordinate removes one power of the vertex count.  The same
observation bounds maps meeting a forbidden set and intersecting pairs of
labelled absorber candidates.

Formalization author and maintainer: Xizhi Liu.
-/

@[expose] public section

open Finset

namespace DensityHS.Rainbow

attribute [local instance] Classical.propDecidable

variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

noncomputable def fixedCoordinateMaps (i : I) (v : V) : Finset (I → V) :=
  mapFamily fun f => f i = v

theorem fixedCoordinateMaps_card_le (i : I) (v : V) :
    (fixedCoordinateMaps i v).card ≤ Fintype.card V ^ (Fintype.card I - 1) := by
  apply mapFamily_card_le_of_coordinate_determined _ i
  intro f g hf hg _
  exact hf.trans hg.symm

noncomputable def mapsMeeting (U : Finset V) : Finset (I → V) :=
  mapFamily fun f => ∃ i, f i ∈ U

theorem mapsMeeting_card_le (U : Finset V) :
    (mapsMeeting (I := I) U).card ≤
      Fintype.card I * U.card * Fintype.card V ^ (Fintype.card I - 1) := by
  classical
  let F := (univ ×ˢ U).biUnion fun iv : I × V => fixedCoordinateMaps iv.1 iv.2
  have hsub : mapsMeeting (I := I) U ⊆ F := by
    intro f hf
    obtain ⟨i, hi⟩ := mem_mapFamily.mp hf
    exact mem_biUnion.mpr ⟨(i, f i), mem_product.mpr ⟨mem_univ i, hi⟩,
      mem_mapFamily.mpr rfl⟩
  calc
    _ ≤ F.card := card_le_card hsub
    _ ≤ ∑ iv ∈ univ ×ˢ U, (fixedCoordinateMaps iv.1 iv.2).card := card_biUnion_le
    _ ≤ ∑ _iv ∈ (univ : Finset I) ×ˢ U,
        Fintype.card V ^ (Fintype.card I - 1) :=
      sum_le_sum fun iv _ => fixedCoordinateMaps_card_le iv.1 iv.2
    _ = _ := by simp only [sum_const, card_product, card_univ, nsmul_eq_mul, Nat.cast_id]

theorem card_maps_le_avoiding_add (F : Finset (I → V)) (U : Finset V) :
    F.card ≤ (F.filter fun f => ∀ i, f i ∉ U).card +
      Fintype.card I * U.card * Fintype.card V ^ (Fintype.card I - 1) := by
  classical
  have hsub : F ⊆ (F.filter fun f => ∀ i, f i ∉ U) ∪ mapsMeeting U := by
    intro f hf
    by_cases h : ∀ i, f i ∉ U
    · exact mem_union_left _ (mem_filter.mpr ⟨hf, h⟩)
    · push Not at h
      exact mem_union_right _ (mem_mapFamily.mpr h)
  exact (card_le_card hsub).trans
    ((card_union_le _ _).trans (Nat.add_le_add_left (mapsMeeting_card_le U) _))

theorem maps_avoiding_abundant {q b : ℕ} (hq : 0 < q) {β : ℝ}
    (F : Finset (Fin q → V)) (hF : β * (Fintype.card V : ℝ) ^ q ≤ (F.card : ℝ))
    (hlarge : ((2 * q * b : ℕ) : ℝ) ≤ β * Fintype.card V)
    (U : Finset V) (hU : U.card ≤ b) :
    (β / 2) * (Fintype.card V : ℝ) ^ q ≤
      ((F.filter fun f => ∀ i, f i ∉ U).card : ℝ) := by
  classical
  have hcount := card_maps_le_avoiding_add F U
  simp only [Fintype.card_fin] at hcount
  have hcountR : (F.card : ℝ) ≤ ((F.filter fun f => ∀ i, f i ∉ U).card : ℝ) +
      (q : ℝ) * U.card * (Fintype.card V : ℝ) ^ (q - 1) := by
    norm_cast
    convert hcount using 1
    congr 2
    ext f
    simp only [mem_filter]
  have hUR : (U.card : ℝ) ≤ b := by exact_mod_cast hU
  have hqb := mul_le_mul_of_nonneg_left hUR (show (0 : ℝ) ≤ q by positivity)
  have hsmall : (q : ℝ) * U.card ≤ β * Fintype.card V / 2 := by
    push_cast at hlarge
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hsmall
    (show 0 ≤ (Fintype.card V : ℝ) ^ (q - 1) by positivity)
  have hpow : (Fintype.card V : ℝ) * (Fintype.card V : ℝ) ^ (q - 1) =
      (Fintype.card V : ℝ) ^ q := by
    rw [← pow_succ', Nat.sub_add_cancel hq]
  have heq : (β * Fintype.card V / 2) * (Fintype.card V : ℝ) ^ (q - 1) =
      β / 2 * (Fintype.card V : ℝ) ^ q := by
    calc
      _ = β / 2 * ((Fintype.card V : ℝ) * (Fintype.card V : ℝ) ^ (q - 1)) := by ring
      _ = _ := by rw [hpow]
  rw [heq] at hmul
  linarith

theorem card_rsets_le_pow (r : ℕ) :
    Fintype.card {X : Finset V // X.card = r} ≤ Fintype.card V ^ r := by
  classical
  let e : {X : Finset V // X.card = r} ≃ ↥((univ : Finset V).powersetCard r) :=
    { toFun := fun X => ⟨X.1, mem_powersetCard.mpr ⟨subset_univ _, X.2⟩⟩
      invFun := fun X => ⟨X.1, (mem_powersetCard.mp X.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_coe, card_powersetCard, card_univ]
  exact Nat.choose_le_pow _ _

noncomputable def crossingCoordinateMaps (i j : I) : Finset (I ⊕ I → V) :=
  mapFamily fun f => f (Sum.inl i) = f (Sum.inr j)

theorem crossingCoordinateMaps_card_le (i j : I) :
    (crossingCoordinateMaps (V := V) i j).card ≤
      Fintype.card V ^ (2 * Fintype.card I - 1) := by
  have hh := mapFamily_card_le_of_coordinate_determined
    (fun f : I ⊕ I → V => f (Sum.inl i) = f (Sum.inr j)) (Sum.inr j) (by
      intro f g hf hg heq
      exact hf.symm.trans ((heq (Sum.inl i) (by simp)).trans hg))
  simpa only [crossingCoordinateMaps, Fintype.card_sum, two_mul] using hh

theorem candidate_maps_card_le (P : (I → V) → Prop) :
    Fintype.card {f : I → V // P f} ≤ Fintype.card V ^ Fintype.card I := by
  simpa only [Fintype.card_fun] using (Fintype.card_subtype_le (p := P))

theorem candidate_maps_conflicts_card_le (P : (I → V) → Prop) :
    (candidateConflicts (fun f : {f : I → V // P f} => univ.image f.1)).card ≤
      Fintype.card I ^ 2 * Fintype.card V ^ (2 * Fintype.card I - 1) := by
  classical
  let A := fun f : {f : I → V // P f} => univ.image f.1
  let E := candidateConflicts A
  let join : ({f : I → V // P f} × {f : I → V // P f}) → (I ⊕ I → V) :=
    fun e => Sum.elim e.1.1 e.2.1
  have hj : Function.Injective join := by
    intro f g hfg
    apply Prod.ext
    · apply Subtype.ext
      funext i
      exact congrFun hfg (Sum.inl i)
    · apply Subtype.ext
      funext i
      exact congrFun hfg (Sum.inr i)
  let B := univ.biUnion fun ij : I × I => crossingCoordinateMaps (V := V) ij.1 ij.2
  have hsub : E.image join ⊆ B := by
    intro f hf
    obtain ⟨e, he, rfl⟩ := mem_image.mp hf
    have he' : e.1 ≠ e.2 ∧ ¬Disjoint (A e.1) (A e.2) := by
      simpa only [E, candidateConflicts, mem_filter, mem_univ, true_and] using he
    have hdis := he'.2
    rw [Finset.disjoint_left] at hdis
    push Not at hdis
    obtain ⟨v, hv₁, hv₂⟩ := hdis
    obtain ⟨i, _, hi⟩ := mem_image.mp hv₁
    obtain ⟨j, _, hj⟩ := mem_image.mp hv₂
    exact mem_biUnion.mpr ⟨(i, j), mem_univ _, mem_mapFamily.mpr (hi.trans hj.symm)⟩
  calc
    E.card = (E.image join).card := (card_image_of_injective _ hj).symm
    _ ≤ B.card := card_le_card hsub
    _ ≤ ∑ ij : I × I, (crossingCoordinateMaps (V := V) ij.1 ij.2).card := card_biUnion_le
    _ ≤ ∑ _ij : I × I, Fintype.card V ^ (2 * Fintype.card I - 1) :=
      sum_le_sum fun ij _ => crossingCoordinateMaps_card_le ij.1 ij.2
    _ = _ := by
      simp only [sum_const, card_univ, Fintype.card_prod, nsmul_eq_mul, Nat.cast_id]
      ring

end DensityHS.Rainbow
