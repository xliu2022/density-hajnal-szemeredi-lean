module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Tactic

/-!
# Finite block averaging and its energy

Author and maintainer: Xizhi Liu.

These lemmas apply to arbitrary finite arrays, without a symmetry
assumption.  A label map encodes a partition, including empty cells.
They supply the energy argument for simultaneous directed regularity.
-/

@[expose] public section

namespace DensityHS.MatrixRegularity

open Finset Fintype
open scoped BigOperators

variable {X I J : Type*} [Fintype X] [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J]

noncomputable def fiberAverage (f : X → I) (a : X → ℝ) (i : I) : ℝ :=
  (∑ x : {x // f x = i}, a x) / Fintype.card {x // f x = i}

noncomputable def blockProjection (f : X → I) (a : X → ℝ) : X → ℝ :=
  fun x => fiberAverage f a (f x)

noncomputable def energy (f : X → I) (a : X → ℝ) : ℝ :=
  ∑ x, (blockProjection f a x)^2

theorem fiber_card_mul_average (f : X → I) (a : X → ℝ) (i : I) :
    (Fintype.card {x // f x = i} : ℝ) * fiberAverage f a i =
      ∑ x : {x // f x = i}, a x := by
  classical
  by_cases h : Nonempty {x // f x = i}
  · letI := h
    have hn : (Fintype.card {x // f x = i} : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    unfold fiberAverage
    field_simp
  · letI : IsEmpty {x // f x = i} := not_nonempty_iff.mp h
    simp [fiberAverage]

/-- Averaging preserves every scalar test which is constant on a fiber. -/
theorem sum_projection_mul_label (f : X → I) (a : X → ℝ) (b : I → ℝ) :
    (∑ x, blockProjection f a x * b (f x)) = ∑ x, a x * b (f x) := by
  classical
  rw [← Fintype.sum_fiberwise f (fun x => blockProjection f a x * b (f x)),
    ← Fintype.sum_fiberwise f (fun x => a x * b (f x))]
  apply Finset.sum_congr rfl
  intro i _
  have hi (x : {x // f x = i}) : f x = i := x.property
  simp only [blockProjection, hi, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Finset.sum_mul]
  rw [← mul_assoc, fiber_card_mul_average]

theorem sum_residual_mul_label (f : X → I) (a : X → ℝ) (b : I → ℝ) :
    (∑ x, (a x - blockProjection f a x) * b (f x)) = 0 := by
  simp only [sub_mul, Finset.sum_sub_distrib, sum_projection_mul_label, sub_self]

theorem projection_eq_of_fiber_const (f : X → I) (a : X → ℝ)
    (ha : ∀ x y, f x = f y → a x = a y) (x : X) :
    blockProjection f a x = a x := by
  classical
  letI : Nonempty {y // f y = f x} := ⟨⟨x, rfl⟩⟩
  have hn : (Fintype.card {y // f y = f x} : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have heq (y : {y // f y = f x}) : a y = a x := ha y x y.property
  simp only [blockProjection, fiberAverage, heq, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  field_simp

theorem projection_nonneg (f : X → I) {a : X → ℝ} (ha : ∀ x, 0 ≤ a x) (x : X) :
    0 ≤ blockProjection f a x :=
  div_nonneg (Finset.sum_nonneg (fun y _ => ha y)) (Nat.cast_nonneg _)

theorem projection_le_one (f : X → I) {a : X → ℝ} (ha : ∀ x, a x ≤ 1) (x : X) :
    blockProjection f a x ≤ 1 := by
  classical
  letI : Nonempty {y // f y = f x} := ⟨⟨x, rfl⟩⟩
  have hn : (0 : ℝ) < Fintype.card {y // f y = f x} := by
    exact_mod_cast Fintype.card_pos
  unfold blockProjection fiberAverage
  apply (div_le_iff₀ hn).mpr
  simpa using Finset.sum_le_sum (fun (y : {y // f y = f x}) (_ : y ∈ Finset.univ) => ha y)

theorem energy_nonneg (f : X → I) (a : X → ℝ) : 0 ≤ energy f a :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem energy_le_card (f : X → I) {a : X → ℝ}
    (ha0 : ∀ x, 0 ≤ a x) (ha1 : ∀ x, a x ≤ 1) :
    energy f a ≤ Fintype.card X := by
  calc
    _ ≤ ∑ _x : X, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x _
      have h0 := projection_nonneg f ha0 x
      have h1 := projection_le_one f ha1 x
      nlinarith
    _ = _ := by simp

theorem energy_eq_pairing (f : X → I) (a : X → ℝ) :
    energy f a = ∑ x, a x * blockProjection f a x := by
  simpa only [energy, blockProjection, pow_two] using
    sum_projection_mul_label f a (fiberAverage f a)

/-- The orthogonality identity for two successive block averages. -/
theorem refinement_pairing (f : X → I) (g : X → J) (q : J → I)
    (hfg : ∀ x, q (g x) = f x) (a : X → ℝ) :
    (∑ x, blockProjection g a x * blockProjection f a x) = energy f a := by
  have h := sum_projection_mul_label g a (fun j => fiberAverage f a (q j))
  simp only [hfg] at h
  exact h.trans (energy_eq_pairing f a).symm

/-- A genuine squared-norm increment, hence monotonicity under refinement. -/
theorem energy_refinement_identity (f : X → I) (g : X → J) (q : J → I)
    (hfg : ∀ x, q (g x) = f x) (a : X → ℝ) :
    energy g a - energy f a =
      ∑ x, (blockProjection g a x - blockProjection f a x)^2 := by
  have h := refinement_pairing f g q hfg a
  calc
    _ = energy g a - 2 * (∑ x, blockProjection g a x * blockProjection f a x) +
        energy f a := by rw [h]; ring
    _ = _ := by
      simp only [energy, Finset.mul_sum, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      ring

theorem energy_mono_refinement (f : X → I) (g : X → J) (q : J → I)
    (hfg : ∀ x, q (g x) = f x) (a : X → ℝ) : energy f a ≤ energy g a := by
  have h := energy_refinement_identity f g q hfg a
  have hpos : 0 ≤ ∑ x, (blockProjection g a x - blockProjection f a x)^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  linarith

theorem residual_test_refinement (f : X → I) (g : X → J)
    (a : X → ℝ) (b : J → ℝ) :
    (∑ x, (a x - blockProjection f a x) * b (g x)) =
      ∑ x, (blockProjection g a x - blockProjection f a x) * b (g x) := by
  simp only [sub_mul, Finset.sum_sub_distrib, sum_projection_mul_label]

/-- A bounded test with large correlation forces a quantitative energy gain. -/
theorem correlation_sq_le_energy_increment (f : X → I) (g : X → J) (q : J → I)
    (hfg : ∀ x, q (g x) = f x) (a : X → ℝ) (b : J → ℝ) :
    (∑ x, (a x - blockProjection f a x) * b (g x))^2 ≤
      (energy g a - energy f a) * ∑ x, (b (g x))^2 := by
  rw [residual_test_refinement, energy_refinement_identity f g q hfg]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- The block projection maximizes the usual quadratic variational formula. -/
theorem variational_lower_bound (f : X → I) (a : X → ℝ) (b : I → ℝ) :
    (∑ x, (2 * a x * b (f x) - (b (f x))^2)) ≤ energy f a := by
  have h := sum_projection_mul_label f a b
  have hp : 0 ≤ ∑ x, (blockProjection f a x - b (f x))^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have heq : (∑ x, (blockProjection f a x - b (f x))^2) =
      energy f a - 2 * (∑ x, blockProjection f a x * b (f x)) + ∑ x, (b (f x))^2 := by
    simp only [energy, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [heq, h] at hp
  have heq' : (∑ x, (2 * a x * b (f x) - (b (f x))^2)) =
      2 * (∑ x, a x * b (f x)) - ∑ x, (b (f x))^2 := by
    simp only [Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [heq']
  linarith

/-- Discarding a small exceptional set costs at most twice its size in
energy, whenever the old block average is retained on the other entries. -/
theorem energy_discard_bound [DecidableEq X] (f : X → I) (g : X → J)
    (a : X → ℝ) (b : J → ℝ) (B : Finset X)
    (ha0 : ∀ x, 0 ≤ a x) (ha1 : ∀ x, a x ≤ 1)
    (hgood : ∀ x ∉ B, b (g x) = blockProjection f a x)
    (hbad : ∀ x ∈ B, b (g x) = 0) :
    energy f a - 2 * B.card ≤ energy g a := by
  classical
  have hp := variational_lower_bound g a b
  have hOld : (∑ x, (2 * a x * blockProjection f a x - (blockProjection f a x)^2)) =
      energy f a := by
    rw [Finset.sum_sub_distrib]
    have hmul : (∑ x, 2 * a x * blockProjection f a x) =
        2 * ∑ x, a x * blockProjection f a x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [hmul, ← energy_eq_pairing]
    change 2 * energy f a - energy f a = energy f a
    ring
  have hpoint (x : X) :
      (2 * a x * blockProjection f a x - (blockProjection f a x)^2) -
        (2 * a x * b (g x) - (b (g x))^2) ≤ if x ∈ B then 2 else 0 := by
    by_cases hx : x ∈ B
    · rw [hbad x hx, if_pos hx]
      have h0 := projection_nonneg f ha0 x
      have h1 := projection_le_one f ha1 x
      nlinarith [ha0 x, ha1 x, mul_nonneg (sub_nonneg.mpr (ha1 x)) h0]
    · rw [hgood x hx, sub_self, if_neg hx]
  have hs := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hpoint x)
  rw [Finset.sum_sub_distrib, hOld] at hs
  simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
    nsmul_eq_mul] at hs
  linarith

end DensityHS.MatrixRegularity
