module

public import DensityHS.Rainbow.MapCounting

/-!
# Greedy counting of disjoint labelled blocks

At each stage a positive real lower bound on the available block count is
multiplied into the number of complete choices.  The forbidden set records
all earlier vertices, so the final choices are genuinely injective.

Formalization author and maintainer: Xizhi Liu.
-/

@[expose] public section

open Finset

namespace DensityHS.Rainbow

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

def IsDisjointBlockChoice {r t : ℕ} (F : Fin r → Finset (Fin t → V))
    (B : Finset V) (g : Fin r → Fin t → V) : Prop :=
  (∀ i, g i ∈ F i) ∧ (∀ i j, g i j ∉ B) ∧
    Function.Injective (fun p : Fin r × Fin t => g p.1 p.2)

noncomputable def disjointBlockChoices {r t : ℕ} (F : Fin r → Finset (Fin t → V))
    (B : Finset V) : Finset (Fin r → Fin t → V) :=
  mapFamily (IsDisjointBlockChoice F B)

theorem IsDisjointBlockChoice.cons {r t : ℕ}
    {F : Fin (r + 1) → Finset (Fin t → V)} {B : Finset V}
    {f : Fin t → V} {g : Fin r → Fin t → V}
    (hf : f ∈ F 0) (hinj : Function.Injective f) (havoid : ∀ j, f j ∉ B)
    (hg : IsDisjointBlockChoice (fun i => F i.succ) (B ∪ univ.image f) g) :
    IsDisjointBlockChoice F B (Fin.cons f g) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    induction i using Fin.cases with
    | zero => exact hf
    | succ i => exact hg.1 i
  · intro i j
    induction i using Fin.cases with
    | zero => exact havoid j
    | succ i => exact fun h => hg.2.1 i j (mem_union_left _ h)
  · rintro ⟨i, j⟩ ⟨k, l⟩ heq
    induction i using Fin.cases with
    | zero =>
      induction k using Fin.cases with
      | zero =>
        have hjl : j = l := hinj heq
        subst l
        rfl
      | succ k =>
        exact False.elim (hg.2.1 k l (mem_union_right _
          (mem_image.mpr ⟨j, mem_univ _, heq⟩)))
    | succ i =>
      induction k using Fin.cases with
      | zero =>
        exact False.elim (hg.2.1 i j (mem_union_right _
          (mem_image.mpr ⟨l, mem_univ _, heq.symm⟩)))
      | succ k =>
        have hh : (i, j) = (k, l) := hg.2.2 heq
        have hik := congrArg Prod.fst hh
        have hjl := congrArg Prod.snd hh
        cases hik
        cases hjl
        rfl

theorem disjointBlockChoices_card_lower (r t b : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (F : Fin r → Finset (Fin t → V)) (B : Finset V)
    (hinj : ∀ i f, f ∈ F i → Function.Injective f)
    (hsize : B.card + r * t ≤ b)
    (havailable : ∀ i (U : Finset V), U.card ≤ b →
      M ≤ ((F i |>.filter fun f => ∀ j, f j ∉ U).card : ℝ)) :
    M ^ r ≤ ((disjointBlockChoices F B).card : ℝ) := by
  classical
  induction r generalizing B with
  | zero =>
    have hne : (disjointBlockChoices F B).Nonempty := by
      refine ⟨Fin.elim0, mem_mapFamily.mpr ⟨?_, ?_, ?_⟩⟩
      · intro i; exact i.elim0
      · intro i; exact i.elim0
      · intro p; exact p.1.elim0
    have hh : 1 ≤ (disjointBlockChoices F B).card := Nat.succ_le_of_lt (card_pos.mpr hne)
    simpa only [pow_zero] using (show (1 : ℝ) ≤ (disjointBlockChoices F B).card by exact_mod_cast hh)
  | succ r ih =>
    let A := (F 0).filter fun f => ∀ j, f j ∉ B
    let Tail := fun f : Fin t → V =>
      disjointBlockChoices (fun i : Fin r => F i.succ) (B ∪ univ.image f)
    let choices := A.sigma Tail
    let join : (Σ _f : Fin t → V, Fin r → Fin t → V) → (Fin (r + 1) → Fin t → V) :=
      fun fg => Fin.cons fg.1 fg.2
    have hj : Function.Injective join := by
      rintro ⟨f, g⟩ ⟨f', g'⟩ hfg
      have hff : f = f' := congrFun hfg 0
      subst f'
      have hgg : g = g' := funext fun i => congrFun hfg i.succ
      subst g'
      rfl
    have htail (f : Fin t → V) : M ^ r ≤ (Tail f).card := by
      apply ih (fun i => F i.succ) (B ∪ univ.image f)
        (fun i f hf => hinj i.succ f hf)
      · have hc := card_union_le B (univ.image f)
        have hi : (univ.image f).card ≤ t := (card_image_le).trans_eq (by simp)
        have hh : (B ∪ univ.image f).card + r * t ≤ B.card + (r + 1) * t := by
          nlinarith
        exact hh.trans hsize
      · exact fun i U hU => havailable i.succ U hU
    have hsub : choices.image join ⊆ disjointBlockChoices F B := by
      intro g hg
      obtain ⟨⟨f, g'⟩, hfg, rfl⟩ := mem_image.mp hg
      obtain ⟨hfA, hgTail⟩ := mem_sigma.mp hfg
      obtain ⟨hf, havoid⟩ := mem_filter.mp hfA
      exact mem_mapFamily.mpr ((mem_mapFamily.mp hgTail).cons hf (hinj 0 f hf) havoid)
    have hcard : choices.card ≤ (disjointBlockChoices F B).card := by
      rw [← card_image_of_injective choices hj]
      exact card_le_card hsub
    have hA : M ≤ (A.card : ℝ) := havailable 0 B (by omega)
    have hcount : M ^ (r + 1) ≤ (choices.card : ℝ) := by
      dsimp only [choices]
      rw [card_sigma, Nat.cast_sum]
      calc
        M ^ (r + 1) = M * M ^ r := pow_succ' M r
        _ ≤ A.card * M ^ r := mul_le_mul_of_nonneg_right hA (pow_nonneg hM r)
        _ = ∑ _f ∈ A, M ^ r := by simp only [sum_const, nsmul_eq_mul]
        _ ≤ _ := sum_le_sum fun f _ => htail f
    exact hcount.trans (by exact_mod_cast hcard)

end DensityHS.Rainbow
