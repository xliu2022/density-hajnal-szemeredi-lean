module

public import DensityHS.Rainbow.NearPerfect
public import DensityHS.Rainbow.AbsorbingLemma
public import DensityHS.Rainbow.Restriction

/-!
# Perfect rainbow clique factors at the density-derived threshold

Author and maintainer: Xizhi Liu.

An actual small absorbing set is removed, the actual near-perfect theorem
is applied to the remaining induced coloured graph, and the divisible
leftover is absorbed. The final packing covers every original vertex.
-/

@[expose] public section

namespace DensityHS.Rainbow

open Finset

universe u v

/-- The paper's rainbow application, with every reduction and absorption
step instantiated by the preceding proved theorems. -/
theorem rainbow_clique_factor {r : ℕ} (hr : 4 ≤ r) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V] {K : Type v}
      (G : SimpleGraph V) (C : G.EdgeLabeling K), N ≤ Fintype.card V →
      r ∣ Fintype.card V →
      (∀ x, (rainbowThreshold r + δ) * Fintype.card V ≤ (colorDegree C x : ℝ)) →
      HasPerfectRainbowPackingOn r C (univ : Finset V) := by
  let ζ : ℝ := min (δ / 4) (1 / 4)
  have hζ : 0 < ζ := lt_min (by positivity) (by norm_num)
  have hζδ : ζ ≤ δ / 4 := min_le_left _ _
  have hζ1 : ζ ≤ 1 / 4 := min_le_right _ _
  have hr1 : r - 1 + 1 = r := by omega
  obtain ⟨γ, hγ, N₀, hN₀⟩ := rainbow_absorbing_lemma.{u,v}
    (by omega : 2 ≤ r - 1) (show 0 < δ / 2 by positivity) hζ
  obtain ⟨N₁, hN₁⟩ := rainbow_near_perfect.{u,v} hr
    (show 0 < δ / 2 by positivity) (show 0 < γ / 2 by positivity)
  refine ⟨max N₀ (2*N₁+1), ?_⟩
  intro V _ _ K G C hn hdiv hdeg
  have hn₀ : N₀ ≤ Fintype.card V := by omega
  have hn₁ : 2*N₁+1 ≤ Fintype.card V := by omega
  have hnpos : 0 < Fintype.card V := by omega
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hnpos
  have habsdeg : ∀ x : V,
      (1-1/(2*((r-1 : ℕ) : ℝ))+δ/2)*Fintype.card V ≤ (colorDegree C x : ℝ) := by
    intro x
    have hb := rainbowThreshold_gt_absorption hr
    rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
    have hc : 1-1/(2*((r : ℝ)-1))+δ/2 ≤ rainbowThreshold r+δ := by linarith
    exact (mul_le_mul_of_nonneg_right hc hnR.le).trans (hdeg x)
  obtain ⟨W, hWsmall, hW, hAbs⟩ := hN₀ G C hn₀ habsdeg
  rw [hr1] at hW hAbs
  have hW1 : (W.card : ℝ) ≤ (Fintype.card V : ℝ)/4 := by
    have hh := mul_le_mul_of_nonneg_right hζ1 hnR.le
    linarith
  have hWδ : (W.card : ℝ) ≤ δ/2*Fintype.card V := by
    have hh := mul_le_mul_of_nonneg_right hζδ hnR.le
    nlinarith
  let S : Set V := {x | x ∉ W}
  have hsize : Fintype.card S + W.card = Fintype.card V := by
    rw [card_induced_complement]
    exact Nat.sub_add_cancel (Finset.card_le_univ W)
  have hsizeR : (Fintype.card S : ℝ)+W.card=Fintype.card V := by exact_mod_cast hsize
  have hlarge : N₁ ≤ Fintype.card S := by
    have hN : (2*N₁+1 : ℕ) ≤ Fintype.card V := hn₁
    have hNR : 2*(N₁ : ℝ)+1 ≤ Fintype.card V := by exact_mod_cast hN
    have hh : (N₁ : ℝ) ≤ Fintype.card S := by linarith
    exact_mod_cast hh
  have hdegree : ∀ x : S, (rainbowThreshold r+δ/2)*Fintype.card S ≤
      (colorDegree (inducedColor C S) x : ℝ) := by
    intro x
    have h := colorDegree_induced_loss C W x
    have hloss : (colorDegree C x.val : ℝ) ≤
        (colorDegree (inducedColor C S) x : ℝ)+W.card := by exact_mod_cast h
    have hbase := hdeg x.val
    have hm : 0 ≤ (rainbowThreshold r+δ/2)*(W.card : ℝ) :=
      mul_nonneg (by have := rainbowThreshold_pos hr; linarith) (Nat.cast_nonneg _)
    nlinarith
  obtain ⟨P, hP, hcover⟩ := hN₁ (G.induce S) (inducedColor C S) hlarge hdegree
  let Q := liftPacking S P
  have hQ : IsRainbowPacking r C Q := hP.of_induced
  have hWQ : Disjoint W (Q.biUnion id) := liftPacking_disjoint W P
  have hQcard : (Q.biUnion id).card = r*P.card := by
    rw [hQ.covered_card, liftPacking_card]
  let U := univ \ (W ∪ Q.biUnion id)
  have hUdiv : r ∣ U.card := rainbow_leftover_divisible hW hQ hWQ hdiv
  have hWU : Disjoint W U := by
    apply Finset.disjoint_left.mpr
    intro x hx hxu
    exact (Finset.mem_sdiff.mp hxu).2 (Finset.mem_union_left _ hx)
  have hUQ : Disjoint U (Q.biUnion id) := by
    apply Finset.disjoint_left.mpr
    intro x hxu hx
    exact (Finset.mem_sdiff.mp hxu).2 (Finset.mem_union_right _ hx)
  have hUsize : U.card+W.card+(Q.biUnion id).card=Fintype.card V := by
    have h := Finset.card_sdiff_add_card_inter (univ : Finset V) (W ∪ Q.biUnion id)
    rw [Finset.univ_inter, Finset.card_union_of_disjoint hWQ, Finset.card_univ] at h
    change U.card+(W.card+(Q.biUnion id).card)=Fintype.card V at h
    omega
  have hUbound : (U.card : ℝ) ≤ γ*Fintype.card V := by
    have hUR : (U.card : ℝ)+W.card+(Q.biUnion id).card=Fintype.card V := by exact_mod_cast hUsize
    rw [hQcard, Nat.cast_mul] at hUR
    have hnS : (0 : ℝ) ≤ Fintype.card S := Nat.cast_nonneg _
    have hnW : (0 : ℝ) ≤ W.card := Nat.cast_nonneg _
    nlinarith
  have hWUtile := hAbs U hWU hUdiv hUbound
  have hQtile : HasPerfectRainbowPackingOn r C (Q.biUnion id) := ⟨Q, hQ, rfl⟩
  have hdis : Disjoint (W ∪ U) (Q.biUnion id) := Finset.disjoint_union_left.mpr ⟨hWQ, hUQ⟩
  have he : (W ∪ U) ∪ Q.biUnion id = univ := by
    ext x
    simp only [U, Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and, iff_true]
    tauto
  simpa only [he] using hWUtile.union hQtile hdis

end DensityHS.Rainbow
