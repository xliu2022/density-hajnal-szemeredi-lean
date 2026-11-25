module

public import DensityHS.Weighted.Peeling
public import DensityHS.Basic.WeightedGraph

/-!
# Deleting a universal zero-cover vertex

The graph keeps its finite vertex type; the deleted vertex is isolated and
has weight zero. This makes the smaller-clique induction compatible with
nonnegative probability vectors without introducing subtype sum identities.

Author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS

open Finset

variable {V : Type*} [Fintype V]

def withoutVertex (G : SimpleGraph V) (b : V) : SimpleGraph V where
  Adj u v := u ≠ b ∧ v ≠ b ∧ G.Adj u v
  symm := ⟨by intro u v h; exact ⟨h.2.1, h.1, h.2.2.symm⟩⟩
  loopless := ⟨by intro u h; exact h.2.2.ne rfl⟩

noncomputable def deleteWeight (p : V → ℝ) (b : V) (v : V) : ℝ := by
  classical
  exact if v = b then 0 else p v

theorem deleteWeight_nonneg {p : V → ℝ} (hp : ∀ v, 0 ≤ p v) (b v : V) :
    0 ≤ deleteWeight p b v := by
  classical
  unfold deleteWeight
  split_ifs
  · exact le_rfl
  · exact hp v

theorem sum_deleteWeight (p : V → ℝ) (b : V) :
    ∑ v, deleteWeight p b v = (∑ v, p v) - p b := by
  classical
  have hsum : (∑ v, deleteWeight p b v) + p b = ∑ v, p v := by
    calc
      _ = (∑ v, deleteWeight p b v) + ∑ v, if v = b then p v else 0 := by simp
      _ = ∑ v, (deleteWeight p b v + if v = b then p v else 0) :=
        (Finset.sum_add_distrib).symm
      _ = ∑ v, p v := by
        apply Finset.sum_congr rfl
        intro v _
        by_cases h : v = b <;> simp [deleteWeight, h]
  linarith

theorem coverCost_deleteWeight {p c : V → ℝ} {b : V} (hb : c b = 0) :
    coverCost (deleteWeight p b) c = coverCost p c := by
  classical
  unfold coverCost
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : v = b <;> simp [deleteWeight, hv, hb]

theorem coverCost_scale (p c : V → ℝ) (a : ℝ) :
    coverCost (fun v => a * p v) c = a * coverCost p c := by
  simp only [coverCost, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  ring

theorem edgeMass_scale (G : SimpleGraph V) (p : V → ℝ) (a : ℝ) :
    edgeMass G (fun v => a * p v) = a ^ 2 * edgeMass G p := by
  classical
  have hterm : ∀ u v, (if G.Adj u v then (a * p u) * (a * p v) else 0) =
      a ^ 2 * (if G.Adj u v then p u * p v else 0) := by
    intro u v
    split_ifs <;> ring
  simp only [edgeMass, hterm, ← Finset.mul_sum]
  ring

theorem edgeMass_nonneg {G : SimpleGraph V} {p : V → ℝ} (hp : ∀ v, 0 ≤ p v) :
    0 ≤ edgeMass G p := by
  classical
  apply div_nonneg _ (by norm_num)
  apply Finset.sum_nonneg
  intro u _
  apply Finset.sum_nonneg
  intro v _
  split_ifs
  · exact mul_nonneg (hp u) (hp v)
  · exact le_rfl

theorem edgeMass_le_total_sq_half {G : SimpleGraph V} {p : V → ℝ}
    (hp : ∀ v, 0 ≤ p v) : edgeMass G p ≤ (∑ v, p v) ^ 2 / 2 := by
  classical
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun u _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun v _ =>
      show (if G.Adj u v then p u * p v else 0) ≤ p u * p v from by
        split_ifs
        · exact le_rfl
        · exact mul_nonneg (hp u) (hp v)))
  simp only [← Finset.mul_sum, ← Finset.sum_mul] at hsum
  unfold edgeMass
  nlinarith

theorem edgeMass_delete_universal {G : SimpleGraph V} {p : V → ℝ} {b : V}
    (hb : ∀ v, v ≠ b → G.Adj b v) :
    edgeMass G p = edgeMass (withoutVertex G b) (deleteWeight p b) +
      p b * (∑ v, deleteWeight p b v) := by
  classical
  have hterm : ∀ u v,
      (if G.Adj u v then p u * p v else 0) =
        (if (withoutVertex G b).Adj u v then deleteWeight p b u * deleteWeight p b v else 0) +
          (if u = b then p b * deleteWeight p b v else 0) +
          (if v = b then deleteWeight p b u * p b else 0) := by
    intro u v
    by_cases hu : u = b
    · subst u
      by_cases hv : v = b
      · subst v
        simp [withoutVertex, deleteWeight]
      · simp [withoutVertex, deleteWeight, hv, hb v hv]
    · by_cases hv : v = b
      · subst v
        simp [withoutVertex, deleteWeight, hu, (hb u hu).symm]
      · simp [withoutVertex, deleteWeight, hu, hv]
  have hsum := congrArg (fun f : V → V → ℝ => ∑ u, ∑ v, f u v)
    (funext fun u => funext fun v => hterm u v)
  simp only [Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    ← Finset.mul_sum, ← Finset.sum_mul] at hsum
  unfold edgeMass
  nlinarith

theorem universal_zero_cover_restrict {s : ℕ} (hs : 2 ≤ s)
    {G : SimpleGraph V} {c : V → ℝ} {b : V}
    (hc : IsCliqueCover (s + 1) G c) (hcb : c b = 0)
    (hb : ∀ v, v ≠ b → G.Adj b v) : IsCliqueCover s (withoutVertex G b) c := by
  classical
  refine ⟨hc.1, ?_⟩
  intro K hK
  have hbK : b ∉ K := by
    intro hbK
    obtain ⟨v, hv, hvb⟩ := Finset.exists_mem_ne (s := K) (by rw [hK.card_eq]; omega) b
    exact (hK.isClique hbK hv (Ne.symm hvb)).1 rfl
  have hG : G.IsNClique s K :=
    ⟨fun u hu v hv huv => (hK.isClique hu hv huv).2.2, hK.card_eq⟩
  have hGb : G.IsNClique (s + 1) (insert b K) :=
    hG.insert (fun v hv => hb v (by intro heq; subst v; exact hbK hv))
  have h := hc.2 (insert b K) hGb
  simpa [Finset.sum_insert hbK, hcb] using h

/-- Genuine finite-graph peeling, assuming only the smaller-clique density
bound on the explicitly deleted graph. -/
theorem universal_zero_peeling {s : ℕ} (hs : 2 ≤ s)
    {G : SimpleGraph V} {p c : V → ℝ} {b : V}
    (hp : IsProbabilityWeight p) (hc : IsCliqueCover (s + 1) G c)
    (hcb : c b = 0) (hb : ∀ v, v ≠ b → G.Adj b v)
    (hx : coverCost p c ≤ 1 / ((s : ℝ) + 1))
    (hIH : ∀ p' c' : V → ℝ, IsProbabilityWeight p' →
      IsCliqueCover s (withoutVertex G b) c' → coverCost p' c' ≤ 1 / (s : ℝ) →
      edgeMass (withoutVertex G b) p' ≤ Phi s (coverCost p' c')) :
    edgeMass G p ≤ Phi (s + 1) (coverCost p c) := by
  classical
  let x := coverCost p c
  let q := 1 - p b
  let H := withoutVertex G b
  let p0 := deleteWeight p b
  have hx0 : 0 ≤ x := coverCost_nonneg hp.1 hc.1
  have hpb : p b ≤ 1 := by
    have h := Finset.single_le_sum (s := Finset.univ) (fun v _ => hp.1 v) (Finset.mem_univ b)
    simpa [hp.2] using h
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hq1 : q ≤ 1 := by dsimp [q]; linarith [hp.1 b]
  have hp0 : ∀ v, 0 ≤ p0 v := fun v => deleteWeight_nonneg hp.1 b v
  have hsum : ∑ v, p0 v = q := by simpa [p0, q, hp.2] using sum_deleteWeight p b
  have hdecomp : edgeMass G p = q * (1 - q) + edgeMass H p0 := by
    have h := edgeMass_delete_universal (p := p) hb
    rw [show (∑ v, deleteWeight p b v) = q from hsum] at h
    dsimp [H, p0]
    rw [h]
    dsimp [q]
    ring
  have hrough : edgeMass G p ≤ q * (1 - q) + q ^ 2 / 2 := by
    rw [hdecomp]
    have he := edgeMass_le_total_sq_half (G := H) hp0
    rw [hsum] at he
    linarith
  by_cases hzero : q = 0
  · have he : edgeMass G p ≤ 0 := by simpa [hzero] using hrough
    exact he.trans (Phi_nonneg (by omega) hx0 (by simpa using hx))
  have hq : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hzero)
  by_cases hsmall : q < (s : ℝ) * x
  · have hsreal : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
    have hsx : (s : ℝ) * x ≤ 1 := by
      have h := (le_div_iff₀ (by linarith : (0 : ℝ) < s + 1)).mp hx
      dsimp [x] at hx0 ⊢
      nlinarith
    have hquad := concave_quadratic_left_le (a := (1 / 2 : ℝ)) (b := 1)
      (t := (s : ℝ) * x) (u := q) (by norm_num) hsmall.le (by nlinarith)
    have hB := complete_peel_boundary s x
    have he : edgeMass G p ≤ B (s + 1) s x := by nlinarith
    exact he.trans (B_le_Phi (by omega) (by omega) (by omega) x)
  let p' : V → ℝ := fun v => (1 / q) * p0 v
  have hp' : IsProbabilityWeight p' := by
    constructor
    · intro v
      exact mul_nonneg (by positivity) (hp0 v)
    · simp only [p', ← Finset.mul_sum, hsum]
      field_simp
  have hc' : IsCliqueCover s H c := universal_zero_cover_restrict hs hc hcb hb
  have hcost : coverCost p' c = x / q := by
    rw [coverCost_scale, coverCost_deleteWeight hcb]
    dsimp [x]
    ring
  have hxq : x / q ≤ 1 / (s : ℝ) := by
    apply (div_le_div_iff₀ hq (by exact_mod_cast (by omega : 0 < s))).mpr
    nlinarith [le_of_not_gt hsmall]
  have heIH := hIH p' c hp' hc' (by rw [hcost]; exact hxq)
  rw [hcost] at heIH
  have hscaled : edgeMass H p0 = q ^ 2 * edgeMass H p' := by
    rw [edgeMass_scale]
    field_simp
  have he : edgeMass G p ≤ peelValue (Phi s) x q := by
    rw [hdecomp, hscaled]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left heIH (sq_nonneg q))
  exact he.trans (peel_Phi_le hs hx0 hx hq hq1 (le_of_not_gt hsmall))

end DensityHS
