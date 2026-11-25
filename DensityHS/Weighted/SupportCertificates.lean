module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic

/-!
# Finite quadratic certificates for support reduction

The support-minimal weighted optimization argument makes the adjacency form
strictly negative on the intersection of two kernels.  This file proves the
linear-algebra obstruction principle and exact certificates for the small
induced graphs needed in the support reduction.  No spectral theory is used.

Authors: Xizhi Liu
-/

@[expose] public section

open scoped BigOperators Matrix

namespace DensityHS.Weighted.Support

/-- The quadratic form of a real matrix. -/
def quadratic {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (z : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, z i * A i j * z j

/-- A form is strictly negative on the common kernel of two linear functionals. -/
def NegativeOnTwoKernels {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : V → ℝ) (l₁ l₂ : V →ₗ[ℝ] ℝ) : Prop :=
  ∀ z, z ≠ 0 → l₁ z = 0 → l₂ z = 0 → Q z < 0

/-- Three free coordinates cannot be killed by only two scalar linear constraints. -/
theorem exists_nonzero_common_kernel
    (l₁ l₂ : (Fin 3 → ℝ) →ₗ[ℝ] ℝ) :
    ∃ z, z ≠ 0 ∧ l₁ z = 0 ∧ l₂ z = 0 := by
  let L : (Fin 3 → ℝ) →ₗ[ℝ] ℝ × ℝ := l₁.prod l₂
  have hdim : Module.finrank ℝ (ℝ × ℝ) < Module.finrank ℝ (Fin 3 → ℝ) := by
    simp
  obtain ⟨z, hz, hnz⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot
      (LinearMap.ker_ne_bot_of_finrank_lt (f := L) hdim)
  have hL : L z = 0 := hz
  exact ⟨z, hnz, congrArg Prod.fst hL, congrArg Prod.snd hL⟩

/-- A three-dimensional nonnegative subspace contradicts strict negativity on
the intersection of two kernels. -/
theorem no_nonnegative_three_dimensional_subspace
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : V → ℝ) (l₁ l₂ : V →ₗ[ℝ] ℝ)
    (hneg : NegativeOnTwoKernels Q l₁ l₂)
    (E : (Fin 3 → ℝ) →ₗ[ℝ] V) (hinj : Function.Injective E)
    (hQ : ∀ z, 0 ≤ Q (E z)) : False := by
  obtain ⟨z, hnz, h₁, h₂⟩ := exists_nonzero_common_kernel (l₁.comp E) (l₂.comp E)
  have hEz : E z ≠ 0 := by
    intro h
    apply hnz
    apply hinj
    simpa using h
  exact (not_lt_of_ge (hQ z)) (hneg (E z) hEz h₁ h₂)

/-- The matrix of an independent triple. -/
def independentTriple : Matrix (Fin 3) (Fin 3) ℝ := 0

/-- The adjacency matrix of the four-cycle, in cyclic order. -/
def fourCycle : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 1, 0, 1; 1, 0, 1, 0; 0, 1, 0, 1; 1, 0, 1, 0]

/-- The adjacency matrix of the complement of a five-cycle. -/
def complementFiveCycle : Matrix (Fin 5) (Fin 5) ℝ :=
  !![0, 0, 1, 1, 0; 0, 0, 0, 1, 1; 1, 0, 0, 0, 1;
     1, 1, 0, 0, 0; 0, 1, 1, 0, 0]

/-- The adjacency matrix of an induced path on four vertices. -/
def fourPath : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 1, 0, 0; 1, 0, 1, 0; 0, 1, 0, 1; 0, 0, 1, 0]

/-- A parametrization of a nonnegative three-dimensional subspace for `C₄`. -/
def fourCycleEmbedding : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) where
  toFun z := ![z 0, z 0 + z 1 - z 2, z 1, z 2]
  map_add' z w := by ext i; fin_cases i <;> simp <;> ring
  map_smul' r z := by ext i; fin_cases i <;> simp <;> ring

theorem fourCycleEmbedding_injective : Function.Injective fourCycleEmbedding := by
  intro z w h
  have h₀ := congrFun h 0
  have h₂ := congrFun h 2
  have h₃ := congrFun h 3
  ext i
  fin_cases i
  · simpa [fourCycleEmbedding] using h₀
  · simpa [fourCycleEmbedding] using h₂
  · simpa [fourCycleEmbedding] using h₃

theorem fourCycle_certificate (z : Fin 3 → ℝ) :
    quadratic fourCycle (fourCycleEmbedding z) = 2 * (z 0 + z 1) ^ 2 := by
  simp [quadratic, fourCycle, fourCycleEmbedding, Fin.sum_univ_succ]
  ring

/-- A parametrization of a positive three-dimensional subspace for `C₅ᶜ`. -/
def complementFiveCycleEmbedding : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 5 → ℝ) where
  toFun z := ![z 0 - z 2, z 1 + z 2, z 0, z 1 - z 2, z 0 + z 2]
  map_add' z w := by ext i; fin_cases i <;> simp <;> ring
  map_smul' r z := by ext i; fin_cases i <;> simp <;> ring

theorem complementFiveCycleEmbedding_injective :
    Function.Injective complementFiveCycleEmbedding := by
  intro z w h
  have h₀ := congrFun h 0
  have h₁ := congrFun h 1
  have h₂ := congrFun h 2
  simp [complementFiveCycleEmbedding] at h₀ h₁ h₂
  ext i
  fin_cases i
  · exact h₂
  · change z 1 = w 1
    linarith
  · change z 2 = w 2
    linarith

theorem complementFiveCycle_certificate (z : Fin 3 → ℝ) :
    quadratic complementFiveCycle (complementFiveCycleEmbedding z) =
      2 * (z 0) ^ 2 + 2 * (z 0 + z 1) ^ 2 + 2 * (z 2) ^ 2 := by
  simp [quadratic, complementFiveCycle, complementFiveCycleEmbedding, Fin.sum_univ_succ]
  ring

theorem independentTriple_obstruction
    (l₁ l₂ : (Fin 3 → ℝ) →ₗ[ℝ] ℝ) :
    ¬ NegativeOnTwoKernels (quadratic independentTriple) l₁ l₂ := by
  intro hneg
  apply no_nonnegative_three_dimensional_subspace _ _ _ hneg (LinearMap.id) Function.injective_id
  intro z
  simp [quadratic, independentTriple]

theorem fourCycle_obstruction
    (l₁ l₂ : (Fin 4 → ℝ) →ₗ[ℝ] ℝ) :
    ¬ NegativeOnTwoKernels (quadratic fourCycle) l₁ l₂ := by
  intro hneg
  apply no_nonnegative_three_dimensional_subspace _ _ _ hneg
    fourCycleEmbedding fourCycleEmbedding_injective
  intro z
  rw [fourCycle_certificate]
  positivity

theorem complementFiveCycle_obstruction
    (l₁ l₂ : (Fin 5 → ℝ) →ₗ[ℝ] ℝ) :
    ¬ NegativeOnTwoKernels (quadratic complementFiveCycle) l₁ l₂ := by
  intro hneg
  apply no_nonnegative_three_dimensional_subspace _ _ _ hneg
    complementFiveCycleEmbedding complementFiveCycleEmbedding_injective
  intro z
  rw [complementFiveCycle_certificate]
  positivity

/-- Sum of vector coordinates as a linear functional. -/
def totalFunctional {ι : Type*} [Fintype ι] : (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun z := ∑ i, z i
  map_add' z w := by simp [Finset.sum_add_distrib]
  map_smul' r z := by simp [Finset.mul_sum]

/-- Pairing with a fixed real coordinate vector. -/
def costFunctional {ι : Type*} [Fintype ι] (c : ι → ℝ) : (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun z := ∑ i, z i * c i
  map_add' z w := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' r z := by simp [mul_assoc, Finset.mul_sum]

/-- The explicit quadratic value in the four-path sign argument. -/
theorem fourPath_certificate (α β : ℝ) :
    quadratic fourPath ![β, -α, -β, α] = -2 * α * β := by
  simp [quadratic, fourPath, Fin.sum_univ_succ]
  ring

/-- The degenerate four-path witness has positive quadratic value. -/
theorem fourPath_degenerate_certificate :
    quadratic fourPath ![1, 1, -1, -1] = 2 := by
  norm_num [quadratic, fourPath, Fin.sum_univ_succ]

/-- Strict negativity on the two relevant kernels forces the cover-level
differences along an induced four-path to have the same strict sign. -/
theorem fourPath_sign_rule (c : Fin 4 → ℝ)
    (hneg : NegativeOnTwoKernels (quadratic fourPath)
      totalFunctional (costFunctional c)) :
    0 < (c 2 - c 0) * (c 3 - c 1) := by
  by_cases hzero : c 2 - c 0 = 0 ∧ c 3 - c 1 = 0
  · have hnz : (![1, 1, -1, -1] : Fin 4 → ℝ) ≠ 0 := by
      intro h
      have := congrFun h 0
      norm_num at this
    have hsum : totalFunctional (![1, 1, -1, -1] : Fin 4 → ℝ) = 0 := by
      norm_num [totalFunctional, Fin.sum_univ_succ]
    have hcost : costFunctional c ![1, 1, -1, -1] = 0 := by
      simp [costFunctional, Fin.sum_univ_succ]
      linarith [hzero.1, hzero.2]
    have hbad := hneg _ hnz hsum hcost
    rw [fourPath_degenerate_certificate] at hbad
    norm_num at hbad
  · let z : Fin 4 → ℝ := ![c 3 - c 1, -(c 2 - c 0), -(c 3 - c 1), c 2 - c 0]
    have hnz : z ≠ 0 := by
      intro h
      have h₀ := congrFun h 0
      have h₃ := congrFun h 3
      simp [z] at h₀ h₃
      exact hzero ⟨h₃, h₀⟩
    have hsum : totalFunctional z = 0 := by
      simp [totalFunctional, z, Fin.sum_univ_succ]
      ring
    have hcost : costFunctional c z = 0 := by
      simp [costFunctional, z, Fin.sum_univ_succ]
      ring
    have hbad := hneg z hnz hsum hcost
    change quadratic fourPath ![c 3 - c 1, -(c 2 - c 0), -(c 3 - c 1), c 2 - c 0] < 0 at hbad
    rw [fourPath_certificate] at hbad
    nlinarith

/-- Extend a vector along an embedding by zero outside its image. -/
noncomputable def pushVector {ι κ : Type*} [Fintype κ] (e : κ ↪ ι)
    (z : κ → ℝ) (v : ι) : ℝ := by
  classical
  exact ∑ i, if e i = v then z i else 0

theorem pushVector_apply {ι κ : Type*} [Fintype κ] (e : κ ↪ ι)
    (z : κ → ℝ) (i : κ) : pushVector e z (e i) = z i := by
  classical
  simp [pushVector, e.injective.eq_iff]

/-- Zero extension is a linear injection. -/
noncomputable def pushLinear {ι κ : Type*} [Fintype κ] (e : κ ↪ ι) :
    (κ → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun := pushVector e
  map_add' z w := by
    classical
    ext v
    simp only [pushVector, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> simp
  map_smul' r z := by
    classical
    ext v
    simp only [pushVector, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> simp

theorem pushLinear_injective {ι κ : Type*} [Fintype κ] (e : κ ↪ ι) :
    Function.Injective (pushLinear e) := by
  intro z w h
  ext i
  have hi := congrFun h (e i)
  simpa [pushLinear, pushVector_apply] using hi

/-- Summation against zero extension is summation over the embedded coordinates. -/
theorem sum_pushVector_mul {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : κ ↪ ι) (z : κ → ℝ) (w : ι → ℝ) :
    (∑ v, pushVector e z v * w v) = ∑ i, z i * w (e i) := by
  classical
  simp only [pushVector, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp [ite_mul]

/-- Zero extension identifies a principal submatrix quadratic form with the
restriction of the ambient quadratic form. -/
theorem quadratic_pushVector {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι ℝ) (e : κ ↪ ι) (z : κ → ℝ) :
    quadratic A (pushVector e z) = quadratic (A.submatrix e e) z := by
  unfold quadratic
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [sum_pushVector_mul]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  simp_rw [mul_comm (A (e i) _)]
  rw [sum_pushVector_mul]
  apply Finset.sum_congr rfl
  intro j hj
  simp [Matrix.submatrix, mul_comm]

/-- The strict negativity property passes to every principal submatrix. -/
theorem negativeOnTwoKernels_submatrix {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι ℝ) (l₁ l₂ : (ι → ℝ) →ₗ[ℝ] ℝ)
    (hneg : NegativeOnTwoKernels (quadratic A) l₁ l₂) (e : κ ↪ ι) :
    NegativeOnTwoKernels (quadratic (A.submatrix e e))
      (l₁.comp (pushLinear e)) (l₂.comp (pushLinear e)) := by
  intro z hnz h₁ h₂
  have hpush : pushLinear e z ≠ 0 := by
    intro h
    apply hnz
    apply pushLinear_injective e
    simpa using h
  have h := hneg _ hpush h₁ h₂
  change quadratic A (pushVector e z) < 0 at h
  rwa [quadratic_pushVector] at h

/-- An ambient matrix with the negativity property has no independent-triple
principal submatrix. -/
theorem no_independentTriple_submatrix {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (l₁ l₂ : (ι → ℝ) →ₗ[ℝ] ℝ)
    (hneg : NegativeOnTwoKernels (quadratic A) l₁ l₂)
    (e : Fin 3 ↪ ι) : A.submatrix e e ≠ independentTriple := by
  intro h
  have hlocal := negativeOnTwoKernels_submatrix A l₁ l₂ hneg e
  rw [h] at hlocal
  exact independentTriple_obstruction _ _ hlocal

/-- An ambient matrix with the negativity property has no four-cycle
principal submatrix. -/
theorem no_fourCycle_submatrix {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (l₁ l₂ : (ι → ℝ) →ₗ[ℝ] ℝ)
    (hneg : NegativeOnTwoKernels (quadratic A) l₁ l₂)
    (e : Fin 4 ↪ ι) : A.submatrix e e ≠ fourCycle := by
  intro h
  have hlocal := negativeOnTwoKernels_submatrix A l₁ l₂ hneg e
  rw [h] at hlocal
  exact fourCycle_obstruction _ _ hlocal

/-- An ambient matrix with the negativity property has no complement-five-cycle
principal submatrix. -/
theorem no_complementFiveCycle_submatrix {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (l₁ l₂ : (ι → ℝ) →ₗ[ℝ] ℝ)
    (hneg : NegativeOnTwoKernels (quadratic A) l₁ l₂)
    (e : Fin 5 ↪ ι) : A.submatrix e e ≠ complementFiveCycle := by
  intro h
  have hlocal := negativeOnTwoKernels_submatrix A l₁ l₂ hneg e
  rw [h] at hlocal
  exact complementFiveCycle_obstruction _ _ hlocal

theorem totalFunctional_comp_pushLinear {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : κ ↪ ι) : totalFunctional.comp (pushLinear e) =
      (totalFunctional : (κ → ℝ) →ₗ[ℝ] ℝ) := by
  ext z
  have h := sum_pushVector_mul e z (fun _ => (1 : ℝ))
  simpa [totalFunctional, pushLinear] using h

theorem costFunctional_comp_pushLinear {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : κ ↪ ι) (c : ι → ℝ) :
    (costFunctional c).comp (pushLinear e) = costFunctional (c ∘ e) := by
  ext z
  exact sum_pushVector_mul e z c

/-- The induced four-path sign rule inside an arbitrary finite matrix. -/
theorem fourPath_sign_rule_submatrix {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (c : ι → ℝ)
    (hneg : NegativeOnTwoKernels (quadratic A) totalFunctional (costFunctional c))
    (e : Fin 4 ↪ ι) (hpath : A.submatrix e e = fourPath) :
    0 < (c (e 2) - c (e 0)) * (c (e 3) - c (e 1)) := by
  have hlocal := negativeOnTwoKernels_submatrix A totalFunctional (costFunctional c) hneg e
  rw [hpath, totalFunctional_comp_pushLinear, costFunctional_comp_pushLinear] at hlocal
  exact fourPath_sign_rule (c ∘ e) hlocal

end DensityHS.Weighted.Support
