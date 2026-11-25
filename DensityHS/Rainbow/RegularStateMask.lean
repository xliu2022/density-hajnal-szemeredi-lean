module

public import DensityHS.Rainbow.DirectedMatrices

/-!
# Counting unusable pairs in a simultaneous regular partition

Both directions of both arc-state matrices are required.  Reversing an
ordered pair is a bijection, so this costs at most four irregular-pair
counts and one diagonal.

Formalization author and maintainer: Xizhi Liu.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace DensityHS.Rainbow

open MatrixRegularity

attribute [local instance] Classical.propDecidable

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

def regularStateMask (F : Bool → V → V → ℝ) (ε : ℝ) (S : I → Finset V) (i j : I) : Prop :=
  i ≠ j ∧ IsUniform (F false) ε (S i) (S j) ∧ IsUniform (F false) ε (S j) (S i) ∧
    IsUniform (F true) ε (S i) (S j) ∧ IsUniform (F true) ε (S j) (S i)

theorem regularStateMask_symm (F : Bool → V → V → ℝ) (ε : ℝ) (S : I → Finset V) :
    Symmetric (regularStateMask F ε S) := by
  intro i j h
  exact ⟨h.1.symm, h.2.2.1, h.2.1, h.2.2.2.2, h.2.2.2.1⟩

theorem regularStateMask_irrefl (F : Bool → V → V → ℝ) (ε : ℝ) (S : I → Finset V) (i : I) :
    ¬regularStateMask F ε S i i := fun h => h.1 rfl

noncomputable def indexedBadPairs (F : V → V → ℝ) (ε : ℝ) (S : I → Finset V) : Finset (I × I) :=
  univ.filter fun e => e.1 ≠ e.2 ∧ ¬IsUniform F ε (S e.1) (S e.2)

theorem regularStateMask_missing_card (F : Bool → V → V → ℝ) (ε : ℝ) (S : I → Finset V) :
    (missingPairs (regularStateMask F ε S)).card ≤ Fintype.card I +
      2 * ((indexedBadPairs (F false) ε S).card + (indexedBadPairs (F true) ε S).card) := by
  classical
  let Diag : Finset (I × I) := univ.filter fun e => e.1 = e.2
  let B₀ := indexedBadPairs (F false) ε S
  let B₁ := indexedBadPairs (F true) ε S
  let U := Diag ∪ (B₀ ∪ (B₀.image Prod.swap ∪ (B₁ ∪ B₁.image Prod.swap)))
  have hsub : missingPairs (regularStateMask F ε S) ⊆ U := by
    intro e he
    have hn := (mem_filter.mp he).2
    by_cases hd : e.1 = e.2
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hd⟩)
    have hb (c : Bool) (h : ¬IsUniform (F c) ε (S e.1) (S e.2)) :
        e ∈ indexedBadPairs (F c) ε S := mem_filter.mpr ⟨mem_univ _, hd, h⟩
    have hr (c : Bool) (h : ¬IsUniform (F c) ε (S e.2) (S e.1)) :
        e ∈ (indexedBadPairs (F c) ε S).image Prod.swap :=
      mem_image.mpr ⟨e.swap, mem_filter.mpr ⟨mem_univ _, (fun heq => hd heq.symm), h⟩, Prod.swap_swap e⟩
    by_cases h₀ : IsUniform (F false) ε (S e.1) (S e.2)
    · by_cases h₀' : IsUniform (F false) ε (S e.2) (S e.1)
      · by_cases h₁ : IsUniform (F true) ε (S e.1) (S e.2)
        · have h₁' : ¬IsUniform (F true) ε (S e.2) (S e.1) :=
            fun h => hn ⟨hd, h₀, h₀', h₁, h⟩
          exact mem_union_right _ (mem_union_right _ (mem_union_right _ (mem_union_right _ (hr true h₁'))))
        · exact mem_union_right _ (mem_union_right _ (mem_union_right _ (mem_union_left _ (hb true h₁))))
      · exact mem_union_right _ (mem_union_right _ (mem_union_left _ (hr false h₀')))
    · exact mem_union_right _ (mem_union_left _ (hb false h₀))
  have hdiag : Diag.card ≤ Fintype.card I := by
    apply le_trans (b := (univ : Finset I).card) ?_ (by simp)
    apply card_le_card_of_injOn Prod.fst (fun _ _ => mem_univ _)
    intro e he f hf hef
    apply Prod.ext hef
    exact (mem_filter.mp he).2.symm.trans (hef.trans (mem_filter.mp hf).2)
  have hc₀ := card_union_le Diag (B₀ ∪ (B₀.image Prod.swap ∪ (B₁ ∪ B₁.image Prod.swap)))
  have hc₁ := card_union_le B₀ (B₀.image Prod.swap ∪ (B₁ ∪ B₁.image Prod.swap))
  have hc₂ := card_union_le (B₀.image Prod.swap) (B₁ ∪ B₁.image Prod.swap)
  have hc₃ := card_union_le B₁ (B₁.image Prod.swap)
  have hi₀ : (B₀.image Prod.swap).card ≤ B₀.card := card_image_le
  have hi₁ : (B₁.image Prod.swap).card ≤ B₁.card := card_image_le
  have hmain := card_le_card hsub
  dsimp only [U] at hmain
  change _ ≤ Fintype.card I + 2 * (B₀.card + B₁.card)
  omega

theorem indexedBadPairs_card_le (F : V → V → ℝ) (ε : ℝ) (G : Finset (Finset V)) :
    (indexedBadPairs F ε (fun S : G => S.1)).card ≤ (badPairs F ε G).card := by
  classical
  let f : G × G → Finset V × Finset V := fun e => (e.1.1, e.2.1)
  have hf : Function.Injective f := by
    intro e e' he
    exact Prod.ext (Subtype.ext (congrArg Prod.fst he)) (Subtype.ext (congrArg Prod.snd he))
  have hsub : (indexedBadPairs F ε (fun S : G => S.1)).image f ⊆ badPairs F ε G := by
    intro e he
    obtain ⟨⟨S, T⟩, hST, rfl⟩ := mem_image.mp he
    have hh := (mem_filter.mp hST).2
    exact mem_badPairs.mpr ⟨S.2, T.2, (fun h => hh.1 (Subtype.ext h)), hh.2⟩
  rw [← card_image_of_injective _ hf]
  exact card_le_card hsub

theorem regularStateMask_missing_bound (F : Bool → V → V → ℝ) {ε q : ℝ}
    (G : Finset (Finset V))
    (hreg : ∀ c, ((badPairs (F c) ε G).card : ℝ) ≤ ε * (G.card : ℝ) ^ 2)
    (hlarge : 1 ≤ ε * G.card) (hsmall : 5 * ε ≤ q ^ 2) :
    ((missingPairs (regularStateMask F ε (fun S : G => S.1))).card : ℝ) ≤
      q ^ 2 * (Fintype.card G : ℝ) ^ 2 := by
  have hc := regularStateMask_missing_card F ε (fun S : G => S.1)
  have hb₀ := indexedBadPairs_card_le (F false) ε G
  have hb₁ := indexedBadPairs_card_le (F true) ε G
  have hcR : ((missingPairs (regularStateMask F ε (fun S : G => S.1))).card : ℝ) ≤
      (G.card : ℝ) + 2 * (((badPairs (F false) ε G).card : ℝ) + (badPairs (F true) ε G).card) := by
    have hh := hc.trans (Nat.add_le_add_left (Nat.mul_le_mul_left 2 (Nat.add_le_add hb₀ hb₁)) _)
    have hhR := Nat.cast_le (α := ℝ).mpr hh
    simpa only [Fintype.card_coe, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hhR
  have hlarge' := mul_le_mul_of_nonneg_right hlarge (show (0 : ℝ) ≤ G.card by positivity)
  have hsmall' := mul_le_mul_of_nonneg_right hsmall (sq_nonneg (G.card : ℝ))
  have h₀ := hreg false
  have h₁ := hreg true
  simp only [Fintype.card_coe]
  nlinarith

end DensityHS.Rainbow
