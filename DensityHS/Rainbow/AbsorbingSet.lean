module

public import DensityHS.Rainbow.LocalAbundance

/-!
# Absorbing sets from labelled local absorber abundance

Candidates are actual injective vertex maps with an internal perfect rainbow
packing.  The overlap estimate counts labelled pairs; duplicate descriptions
of the same nonempty vertex set are therefore removed by the same conflict
selection as all other intersections.

Formalization author and maintainer: Xizhi Liu.
-/

@[expose] public section

set_option maxHeartbeats 800000

open Finset

namespace DensityHS.Rainbow

attribute [local instance] Classical.propDecidable

variable {V K J : Type*} [Fintype V] [DecidableEq V]
    [Fintype J] [DecidableEq J] [Nonempty J]
    {G : SimpleGraph V} {C : G.EdgeLabeling K}

theorem exists_absorbingSet_of_map_supply {r L : ℕ} (hr : 0 < r)
    (p : unitInterval) {m S T : ℝ} (hS : 0 < S) (hT : 0 < T)
    (hgood : ∀ X : Finset V, X.card = r →
      m ≤ ((mapFamily fun f : J → V => Function.Injective f ∧
        IsLocalAbsorber r C X (univ.image f)).card : ℝ))
    (hL : (L : ℝ) ≤ (p : ℝ) * m / 2 - T)
    (hpotential : (p : ℝ) * (Fintype.card V : ℝ) ^ Fintype.card J / S +
      (p : ℝ) ^ 2 * (Fintype.card J : ℝ) ^ 2 *
        (Fintype.card V : ℝ) ^ (2 * Fintype.card J - 1) / T +
      (Fintype.card V : ℝ) ^ r * Real.exp (-selectionDecay * (p : ℝ) * m) < 1) :
    ∃ W : Finset V, (W.card : ℝ) < Fintype.card J * S ∧ IsAbsorbingSet r C L W := by
  classical
  let P := fun f : J → V => Function.Injective f ∧
    HasPerfectRainbowPackingOn r C (univ.image f)
  letI : DecidablePred P := fun f => Classical.propDecidable (P f)
  let I := {f : J → V // P f}
  let A := fun f : I => univ.image f.1
  have hAne : ∀ i : I, (A i).Nonempty := by
    intro i
    obtain ⟨j⟩ := ‹Nonempty J›
    exact ⟨i.1 j, mem_image.mpr ⟨j, mem_univ _, rfl⟩⟩
  have hApack : ∀ i : I, HasPerfectRainbowPackingOn r C (A i) := fun i => i.2.2
  have hsize : ∀ i : I, (A i).card ≤ Fintype.card J := by
    intro i
    exact card_image_le.trans_eq card_univ
  have hgood' : ∀ X : Finset V, X.card = r →
      m ≤ ((univ.filter fun i : I => IsLocalAbsorber r C X (A i)).card : ℝ) := by
    intro X hX
    let F := mapFamily fun f : J → V => Function.Injective f ∧
      IsLocalAbsorber r C X (univ.image f)
    let Q := univ.filter fun i : I => IsLocalAbsorber r C X (A i)
    let lift : F → Q := fun f =>
      ⟨⟨f.1, (mem_mapFamily.mp f.2).1, (mem_mapFamily.mp f.2).2.2.1⟩,
        mem_filter.mpr ⟨mem_univ _, (mem_mapFamily.mp f.2).2⟩⟩
    have hlift : Function.Injective lift := by
      intro f g hfg
      exact Subtype.ext (congrArg (fun q : Q => q.1.1) hfg)
    have hcard : F.card ≤ Q.card := by
      simpa only [Fintype.card_coe] using Fintype.card_le_of_injective lift hlift
    exact (hgood X hX).trans (by exact_mod_cast hcard)
  have hI : (Fintype.card I : ℝ) ≤ (Fintype.card V : ℝ) ^ Fintype.card J := by
    exact_mod_cast candidate_maps_card_le (V := V) P
  have hE : ((candidateConflicts A).card : ℝ) ≤
      (Fintype.card J : ℝ) ^ 2 * (Fintype.card V : ℝ) ^ (2 * Fintype.card J - 1) := by
    exact_mod_cast candidate_maps_conflicts_card_le (V := V) P
  have hQ : (Fintype.card {X : Finset V // X.card = r} : ℝ) ≤
      (Fintype.card V : ℝ) ^ r := by exact_mod_cast card_rsets_le_pow (V := V) r
  have hfirst := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hI p.2.1) hS.le
  have hsecond := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hE (sq_nonneg (p : ℝ))) hT.le
  have hthird := mul_le_mul_of_nonneg_right hQ
    (Real.exp_pos (-selectionDecay * (p : ℝ) * m)).le
  have hpot : (p : ℝ) * Fintype.card I / S +
      (p : ℝ) ^ 2 * (candidateConflicts A).card / T +
      Fintype.card {X : Finset V // X.card = r} *
        Real.exp (-selectionDecay * (p : ℝ) * m) < 1 := by
    calc
      _ ≤ (p : ℝ) * (Fintype.card V : ℝ) ^ Fintype.card J / S +
          (p : ℝ) ^ 2 * ((Fintype.card J : ℝ) ^ 2 *
            (Fintype.card V : ℝ) ^ (2 * Fintype.card J - 1)) / T +
          (Fintype.card V : ℝ) ^ r * Real.exp (-selectionDecay * (p : ℝ) * m) :=
        add_le_add (add_le_add hfirst hsecond) hthird
      _ < 1 := by simpa only [mul_assoc] using hpotential
  exact exists_absorbingSet_of_candidates hr A hAne hApack
    (Fintype.card_pos) hsize p hS hT hgood' hL hpot

theorem exists_absorbingSet_of_connector_supply {t L : ℕ} (ht : 0 < t)
    {β : ℝ} (hβ : 0 ≤ β)
    (hconn : ∀ x y : V, β * (Fintype.card V : ℝ) ^ t ≤
      ((commonConnectorMaps t C x y).card : ℝ))
    (hlarge : ((2 * (t + 1) ^ 3 : ℕ) : ℝ) ≤ β * Fintype.card V)
    (p : unitInterval) {S T : ℝ} (hS : 0 < S) (hT : 0 < T)
    (hL : (L : ℝ) ≤ (p : ℝ) *
      ((β / 2) ^ (t + 2) * (Fintype.card V : ℝ) ^ ((t + 1) ^ 2)) / 2 - T)
    (hpotential : (p : ℝ) * (Fintype.card V : ℝ) ^ ((t + 1) ^ 2) / S +
      (p : ℝ) ^ 2 * (((t + 1) ^ 2 : ℕ) : ℝ) ^ 2 *
        (Fintype.card V : ℝ) ^ (2 * ((t + 1) ^ 2) - 1) / T +
      (Fintype.card V : ℝ) ^ (t + 1) * Real.exp (-selectionDecay * (p : ℝ) *
        ((β / 2) ^ (t + 2) * (Fintype.card V : ℝ) ^ ((t + 1) ^ 2))) < 1) :
    ∃ W : Finset V, (W.card : ℝ) < ((t + 1) ^ 2 : ℕ) * S ∧
      IsAbsorbingSet (t + 1) C L W := by
  classical
  have hcard : Fintype.card (AbsorberPosition t) = (t + 1) ^ 2 := by
    simp only [AbsorberPosition, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    ring
  simpa only [hcard] using exists_absorbingSet_of_map_supply
    (J := AbsorberPosition t) (Nat.zero_lt_succ t) p hS hT
    (fun X hX => localAbsorberMaps_abundant_finset ht hβ hconn hlarge X hX) hL
    (by simpa only [hcard] using hpotential)

end DensityHS.Rainbow
