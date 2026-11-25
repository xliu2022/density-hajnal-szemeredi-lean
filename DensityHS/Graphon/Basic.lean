module

public import DensityHS.Basic.WeightedGraph
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Measurable kernels and fractional clique covers

Author and maintainer: Xizhi Liu.

This file uses a concrete symmetric kernel on an arbitrary probability space.
The normalization of `density` agrees with the finite `DensityHS.edgeMass`:
each undirected pair contributes once.  Covers are required on almost every
tuple in the support of the clique kernel.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A measurable symmetric kernel with values in the unit interval. -/
structure Kernel (Ω : Type*) [MeasurableSpace Ω] where
  toFun : Ω → Ω → ℝ
  measurable_uncurry : Measurable (Function.uncurry toFun)
  symmetric : ∀ x y, toFun x y = toFun y x
  nonneg : ∀ x y, 0 ≤ toFun x y
  le_one : ∀ x y, toFun x y ≤ 1

instance : CoeFun (Kernel Ω) (fun _ => Ω → Ω → ℝ) := ⟨Kernel.toFun⟩

/-- A measurable unit-interval-valued real function is integrable on a finite
measure space. -/
theorem integrable_of_unitInterval {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : Ω → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, f x ≤ 1) : Integrable f μ := by
  refine (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hf0 x)] using hf1 x

namespace Kernel

theorem measurable_left (W : Kernel Ω) (x : Ω) : Measurable (W x) :=
  W.measurable_uncurry.comp (measurable_const.prodMk measurable_id)

theorem measurable_right (W : Kernel Ω) (y : Ω) : Measurable (fun x => W x y) :=
  W.measurable_uncurry.comp (measurable_id.prodMk measurable_const)

theorem integrable (W : Kernel Ω) (μ : Measure Ω) [IsFiniteMeasure μ] :
    Integrable (Function.uncurry W) (μ.prod μ) :=
  integrable_of_unitInterval W.measurable_uncurry
    (fun z => W.nonneg z.1 z.2) (fun z => W.le_one z.1 z.2)

theorem integrable_left (W : Kernel Ω) (μ : Measure Ω) [IsFiniteMeasure μ]
    (x : Ω) : Integrable (W x) μ :=
  integrable_of_unitInterval (W.measurable_left x) (W.nonneg x) (W.le_one x)

end Kernel

/-- Half of the ordered kernel integral. -/
noncomputable def density (μ : Measure Ω) (W : Kernel Ω) : ℝ :=
  (∫ x, ∫ y, W x y ∂μ ∂μ) / 2

theorem density_eq_prod_integral (μ : Measure Ω) [IsFiniteMeasure μ]
    (W : Kernel Ω) :
    density μ W = (∫ z, W z.1 z.2 ∂μ.prod μ) / 2 := by
  rw [density, integral_integral (W.integrable μ)]

theorem density_nonneg (μ : Measure Ω) (W : Kernel Ω) :
    0 ≤ density μ W := by
  exact div_nonneg (integral_nonneg fun x => integral_nonneg (W.nonneg x)) (by norm_num)

theorem density_le_half (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Kernel Ω) :
    density μ W ≤ 1 / 2 := by
  rw [density_eq_prod_integral]
  have h : (∫ z, W z.1 z.2 ∂μ.prod μ) ≤ 1 := by
    calc
      (∫ z, W z.1 z.2 ∂μ.prod μ) ≤ ∫ _ : Ω × Ω, (1 : ℝ) ∂μ.prod μ :=
        integral_mono (W.integrable μ) (integrable_const _) (fun z => W.le_one z.1 z.2)
      _ = 1 := by simp
  linarith

/-- A fractional kernel clique cover.  The clique condition is imposed almost
everywhere for independently sampled ordered tuples. -/
def IsKernelCover (r : ℕ) (W : Kernel Ω) (μ : Measure Ω) (c : Ω → ℝ) : Prop :=
  Measurable c ∧ (∀ x, 0 ≤ c x ∧ c x ≤ 1) ∧
    ∀ᵐ t : Fin r → Ω ∂Measure.pi (fun _ => μ),
      (∀ i j, i ≠ j → 0 < W (t i) (t j)) → 1 ≤ ∑ i, c (t i)

namespace IsKernelCover

theorem measurable {r : ℕ} {W : Kernel Ω} {μ : Measure Ω} {c : Ω → ℝ}
    (hc : IsKernelCover r W μ c) : Measurable c := hc.1

theorem nonneg {r : ℕ} {W : Kernel Ω} {μ : Measure Ω} {c : Ω → ℝ}
    (hc : IsKernelCover r W μ c) (x : Ω) : 0 ≤ c x := (hc.2.1 x).1

theorem le_one {r : ℕ} {W : Kernel Ω} {μ : Measure Ω} {c : Ω → ℝ}
    (hc : IsKernelCover r W μ c) (x : Ω) : c x ≤ 1 := (hc.2.1 x).2

theorem integrable {r : ℕ} {W : Kernel Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {c : Ω → ℝ} (hc : IsKernelCover r W μ c) : Integrable c μ :=
  integrable_of_unitInterval hc.measurable hc.nonneg hc.le_one

theorem integral_nonneg {r : ℕ} {W : Kernel Ω} {μ : Measure Ω} {c : Ω → ℝ}
    (hc : IsKernelCover r W μ c) : 0 ≤ ∫ x, c x ∂μ :=
  MeasureTheory.integral_nonneg hc.nonneg

theorem integral_le_one {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {c : Ω → ℝ} (hc : IsKernelCover r W μ c) :
    (∫ x, c x ∂μ) ≤ 1 := by
  calc
    (∫ x, c x ∂μ) ≤ ∫ _ : Ω, (1 : ℝ) ∂μ :=
      integral_mono hc.integrable (integrable_const _) hc.le_one
    _ = 1 := by simp

end IsKernelCover

/-- The support graph on a tuple of sampled vertices.  Distinct labels are
required even when two coordinates of the tuple coincide. -/
def sampleGraph (W : Kernel Ω) (n : ℕ) (ω : Fin n → Ω) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ 0 < W (ω i) (ω j)
  symm := ⟨by
    intro i j hij
    exact ⟨hij.1.symm, (W.symmetric (ω i) (ω j)) ▸ hij.2⟩⟩
  loopless := ⟨fun i h => h.1 rfl⟩

@[simp] theorem sampleGraph_adj (W : Kernel Ω) (n : ℕ) (ω : Fin n → Ω)
    (i j : Fin n) :
    (sampleGraph W n ω).Adj i j ↔ i ≠ j ∧ 0 < W (ω i) (ω j) := Iff.rfl

/-- The cover values on a sampled tuple. -/
def sampleCover (c : Ω → ℝ) {n : ℕ} (ω : Fin n → Ω) : Fin n → ℝ := c ∘ ω

@[simp] theorem sampleCover_apply (c : Ω → ℝ) {n : ℕ} (ω : Fin n → Ω)
    (i : Fin n) : sampleCover c ω i = c (ω i) := rfl

end DensityHS.Graphon
