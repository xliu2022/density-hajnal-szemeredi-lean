module

public import DensityHS.Constructions.IntegerRealizations
public import DensityHS.Graphon.FiniteTransference

/-!
# From cut proximity to an exact finite extremal graph

Author and maintainer: Xizhi Liu.

The cut quotient is realized by an actual measure-preserving measurable
bijection. Random vertex assignment and the prescribed-size correction
then produce a graph on the original vertices in the exact finite family.
-/

@[expose] public section

namespace DensityHS.Stability

open MeasureTheory Finset Graphon Constructions Regularity

universe u v

attribute [local instance] Classical.propDecidable

theorem finite_template_prescribed_rounding
    {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    {I : Type v} [Fintype I] [DecidableEq I] [Nonempty I]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : FiniteTemplate I) (hA : ∀ i j, A.entry i j=0 ∨ A.entry i j=1)
    {p : I → ℝ} (hp : IsProbabilityWeight p)
    (q : I → ℕ) (hq : ∑ i, q i=Fintype.card V) {b δ : ℝ}
    (hsize : ∑ i, |(q i : ℝ)-(Fintype.card V : ℝ)*p i| ≤ b)
    (hnear : relabelL1Distance unitMeasure (finiteGraphKernel G) (A.kernel p) < δ) :
    ∃ s : ℝ, 0 ≤ s ∧ s < δ ∧ ∃ f : V → I, (∀ i, fiberCount f i=q i) ∧
      (editDistance G (templateGraph A.entry A.symmetric f) : ℝ) ≤
        ((Fintype.card V : ℝ)^2*s+Fintype.card V)/2+
          (Fintype.card V : ℝ)*(Real.sqrt ((Fintype.card I : ℝ)*
            ((Fintype.card V : ℝ)^2*s+Fintype.card V))+b) := by
  letI : MeasurableSpace V := ⊤
  letI : MeasurableSpace I := ⊤
  obtain ⟨s, hs, hsδ⟩ := exists_lt_of_csInf_lt
    (relabelL1Values_nonempty unitMeasure (finiteGraphKernel G) (A.kernel p)) hnear
  obtain ⟨σ, hσ, rfl⟩ := hs
  let vl : ℝ → V := intervalLabel (uniformWeight V) ∘ σ
  have hv : Measurable vl := (measurable_intervalLabel _).comp hσ.measurable
  have hmass (a : V) : unitMeasure.real {x | vl x=a} = 1/(Fintype.card V : ℝ) := by
    change unitMeasure.real (σ ⁻¹' {x | intervalLabel (uniformWeight V) x=a}) = _
    rw [hσ.measureReal_preimage
      ((measurableSet_eq_fun (measurable_intervalLabel _) measurable_const).nullMeasurableSet)]
    exact intervalLabel_mass uniformWeight_probability a
  have hsize' : (∑ i, |(q i : ℝ)-(Fintype.card V : ℝ)*
      unitMeasure.real {x | intervalLabel p x=i}|) ≤ b := by
    simpa only [intervalLabel_mass hp] using hsize
  obtain ⟨f, hf, he⟩ := exists_kernel_rounding_prescribed_sizes unitMeasure vl hv hmass
    (intervalLabel p) (measurable_intervalLabel p) G A.entry A.symmetric hA
    ((finiteGraphKernel G).comap σ hσ.measurable) (A.kernel p)
    (fun x y => finiteGraphKernel_apply G (σ x) (σ y)) (fun _ _ => rfl) q hq hsize'
  exact ⟨_, kernelL1Distance_nonneg _ _ _, hsδ, f, hf, he⟩

/-- One cut-distance threshold suffices for every branch, integer k, and
simplex parameter. The output graph satisfies the manuscript's exact
integer construction constraints. -/
theorem finite_construction_edit_rounding {r : ℕ} (hr : 3 ≤ r)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ N : ℕ,
      ∀ {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
        (G : SimpleGraph V) [DecidableRel G.Adj], N ≤ Fintype.card V →
        ∀ k : ℕ, r*k ≤ Fintype.card V → ∀ t : ConstructionKind r,
        ∀ z : Fin (r-1) → ℝ, IsProbabilityWeight z →
        constructionDomain r t ((k : ℝ)/Fintype.card V) →
        dist (finiteGraphon G) (constructionGraphon r t ((k : ℝ)/Fintype.card V,z)) < ρ →
        ∃ H : SimpleGraph V, H ∈ finiteConstructionFamily r k t ∧
          (editDistance G H : ℝ) < ε*(Fintype.card V : ℝ)^2 := by
  let M := 2*r-1
  have hM : (0 : ℝ) < M := by dsimp [M]; exact_mod_cast (by omega : 0 < 2*r-1)
  obtain ⟨δ, hδ, N, hparam⟩ := exists_rounding_error_parameters M hε
  refine ⟨δ/(M : ℝ)^2, div_pos hδ (sq_pos_of_pos hM), N, ?_⟩
  intro V _ _ _ G _ hn k hk t z hz hd hdist
  have hn0 : 0 < Fintype.card V := Fintype.card_pos
  have hnp : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn0
  let I := ConstructionIndex r t
  let A := constructionTemplate r t
  let p := constructionWeight r t ((k : ℝ)/Fintype.card V) z
  have hx : (k : ℝ)/Fintype.card V ∈ Set.Icc 0 (1/(r : ℝ)) := by
    refine ⟨by positivity, ?_⟩
    have hrp : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
    apply (div_le_div_iff₀ hnp hrp).mpr
    have hh : (r : ℝ)*k ≤ Fintype.card V := by exact_mod_cast hk
    simpa only [one_mul, mul_one, mul_comm] using hh
  have hp : IsProbabilityWeight p := constructionWeight_probability hr t hx hz hd
  obtain ⟨q, hq, herror⟩ := exists_construction_integer_sizes hr hn0 hk t hz hd
  have hsize : (∑ i, |(q i : ℝ)-(Fintype.card V : ℝ)*p i|) ≤ M := by
    calc
      _ ≤ ∑ _i : I, (1 : ℝ) := Finset.sum_le_sum (fun i _ => herror i)
      _ = (Fintype.card I : ℝ) := by simp
      _ ≤ M := by exact_mod_cast constructionIndex_card_le (by omega : 2 ≤ r) t
  have hcut : Vendor.Graphon.cutDistance ((finiteGraphKernel G).toVendorGraphon unitMeasure)
      ((constructionKernel r t ((k : ℝ)/Fintype.card V,z)).toVendorGraphon unitMeasure) < δ/(M : ℝ)^2 := by
    change dist (finiteGraphon G)
      (Vendor.GraphonSpace.mk ((constructionKernel r t ((k : ℝ)/Fintype.card V,z)).toVendorGraphon unitMeasure)) < _
    have he : Vendor.GraphonSpace.mk ((constructionKernel r t ((k : ℝ)/Fintype.card V,z)).toVendorGraphon unitMeasure) =
        constructionGraphon r t ((k : ℝ)/Fintype.card V,z) := by cases t <;> rfl
    rwa [he]
  have hnear : relabelL1Distance unitMeasure (finiteGraphKernel G) (A.kernel p) < δ := by
    change relabelL1Distance unitMeasure (finiteGraphKernel G)
      ((constructionTemplate r t).kernel (constructionWeight r t ((k : ℝ)/Fintype.card V) z)) < δ
    rw [constructionTemplate_kernel]
    apply (construction_relabelL1_bound (by omega : 2 ≤ r) t _ _).trans_lt
    change (M : ℝ)^2 * _ < δ
    simpa only [mul_comm] using (lt_div_iff₀ (sq_pos_of_pos hM)).mp hcut
  obtain ⟨s, hs, hsδ, f, hf, he⟩ := finite_template_prescribed_rounding G A
    (constructionTemplate_binary r t) hp q hq.1 hsize hnear
  refine ⟨templateGraph A.entry A.symmetric f, ⟨f, ?_, rfl⟩, ?_⟩
  · have hfun : fiberCount f = q := funext hf
    simpa only [hfun] using hq
  · apply he.trans_lt
    exact hparam _ hn s hs hsδ.le (Fintype.card I) (Nat.cast_nonneg _)
      (by exact_mod_cast constructionIndex_card_le (by omega : 2 ≤ r) t)

end DensityHS.Stability
