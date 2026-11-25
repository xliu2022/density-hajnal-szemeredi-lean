module

public import DensityHS.Graphon.RBlocks
public import DensityHS.Graphon.MarkedExtensions

/-!
# Finite marked neighbor sets

Author and maintainer: Xizhi Liu.

Forbidden marked cliques bound both the number of unmarked blocks seen by
one marked vertex and the number seen by the endpoints of a marked edge.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Excluding one fixed finite subset size bounds a set, including a priori
infinite sets. -/
theorem finite_card_le_of_forbidden_subset {I : Type*} {s : Set I} {n : ℕ}
    (h : ∀ F : Finset I, F.card = n + 1 → ¬ ∀ i ∈ F, i ∈ s) :
    ∃ hs : s.Finite, hs.toFinset.card ≤ n := by
  classical
  have hs : s.Finite := by
    by_contra hi
    obtain ⟨F, hF, hcard⟩ := Set.Infinite.exists_subset_card_eq hi (n + 1)
    exact h F hcard (fun i hi => hF hi)
  refine ⟨hs, ?_⟩
  by_contra! hn
  obtain ⟨F, hF, hcard⟩ := Finset.exists_subset_card_eq (show n + 1 ≤ hs.toFinset.card by omega)
  exact h F hcard (fun i hi => hs.mem_toFinset.mp (hF hi))

namespace MarkedBlockSystem

variable {W : Kernel Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : Set Ω}

/-- Every finite completion of marked free coordinates is forbidden. -/
theorem forbid_extension (P : MarkedBlockSystem W μ Z) {r k : ℕ}
    (hk : 0 < k) (hZ : MeasurableSet Z) (hfree : NoCliqueMeets r W μ Z)
    (F : Finset P.Index) (hF : k + F.card = r) :
    ∀ᵐ z : Fin k → Ω ∂Measure.pi (fun _ => μ),
      ¬ ((∀ a, z a ∈ Z) ∧ z ∈ cliqueTuples k W ∧ ∀ a, ∀ j ∈ F, z a ∈ P.neighbor j) := by
  classical
  have h := hfree.forbid_extension hk hZ (J := F)
    (by simpa only [Fintype.card_coe] using hF)
    (fun j => P.block j) (fun j => P.neighbor j)
    (fun j => P.measurable j) (fun j => P.block_nonzero j)
    (fun j => P.neighbor_measurable j)
    (fun i j hij => P.cross_complete i j (fun he => hij (Subtype.ext he)))
    (fun j => P.neighbor_complete j)
  filter_upwards [h] with z hz hp
  exact hz ⟨hp.1, hp.2.1, fun a j => hp.2.2 a j j.2⟩

/-- No marked point sees `r-1` prescribed positive unmarked blocks. -/
theorem ae_not_all_neighbors (P : MarkedBlockSystem W μ Z) {r : ℕ} (hr : 2 ≤ r)
    (hZ : MeasurableSet Z) (hfree : NoCliqueMeets r W μ Z)
    (F : Finset P.Index) (hF : F.card = r - 1) :
    ∀ᵐ z ∂μ, z ∈ Z → ¬ ∀ j ∈ F, z ∈ P.neighbor j := by
  classical
  have he := P.forbid_extension (k := 1) (by omega) hZ hfree F (by omega)
  have hsource : ∀ᵐ z : Fin 1 → Ω ∂Measure.pi (fun _ => μ),
      z 0 ∈ Z → ¬ ∀ j ∈ F, z 0 ∈ P.neighbor j := by
    filter_upwards [he] with z hz hx hnb
    apply hz
    refine ⟨?_, ?_, ?_⟩
    · intro a
      simpa only [Subsingleton.elim a 0] using hx
    · intro a b hab
      exact False.elim (hab (Subsingleton.elim a b))
    · intro a j hj
      simpa only [Subsingleton.elim a 0] using hnb j hj
  have hm : MeasurableSet {z : Ω | z ∈ Z → ¬ ∀ j ∈ F, z ∈ P.neighbor j} := by
    have hbad : MeasurableSet (Z ∩ ⋂ j ∈ F, P.neighbor j) :=
      hZ.inter (Finset.measurableSet_biInter F (fun j _ => P.neighbor_measurable j))
    convert hbad.compl using 1
    congr 1
    ext z
    simp only [mem_setOf_eq, mem_compl_iff, mem_inter_iff, mem_iInter]
    tauto
  have hp := measurePreserving_eval (fun _ : Fin 1 => μ) (0 : Fin 1)
  have hh := (ae_map_iff hp.measurable.aemeasurable hm).mpr hsource
  simpa only [hp.map_eq] using hh

/-- Almost every marked point has at most `r-2` block neighbors, even when
the original partition has infinitely many blocks. -/
theorem ae_finite_neighbors (P : MarkedBlockSystem W μ Z) {r : ℕ} (hr : 2 ≤ r)
    (hZ : MeasurableSet Z) (hfree : NoCliqueMeets r W μ Z) :
    ∀ᵐ z ∂μ, z ∈ Z → ∃ hs : {j | z ∈ P.neighbor j}.Finite,
      hs.toFinset.card ≤ r - 2 := by
  classical
  letI := P.countable
  have hall : ∀ᵐ z ∂μ, ∀ F : Finset P.Index, F.card = r - 1 →
      z ∈ Z → ¬ ∀ j ∈ F, z ∈ P.neighbor j := by
    apply ae_all_iff.mpr
    intro F
    by_cases hF : F.card = r - 1
    · exact (P.ae_not_all_neighbors hr hZ hfree F hF).mono fun _ hz _ => hz
    · exact Eventually.of_forall fun _ h => False.elim (hF h)
  filter_upwards [hall] with z hz hx
  apply finite_card_le_of_forbidden_subset
  intro F hF
  exact hz F (by omega) hx

/-- A marked edge cannot have `r-2` prescribed common positive block
neighbors. This is a product-measure assertion about actual edges. -/
theorem ae_edge_not_all_common_neighbors (P : MarkedBlockSystem W μ Z)
    {r : ℕ} (hr : 2 ≤ r) (hZ : MeasurableSet Z) (hfree : NoCliqueMeets r W μ Z)
    (F : Finset P.Index) (hF : F.card = r - 2) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ Z → z.2 ∈ Z → 0 < W z.1 z.2 →
      ¬ ∀ j ∈ F, z.1 ∈ P.neighbor j ∧ z.2 ∈ P.neighbor j := by
  classical
  have he := P.forbid_extension (k := 2) (by omega) hZ hfree F (by omega)
  have hsource : ∀ᵐ z : Fin 2 → Ω ∂Measure.pi (fun _ => μ),
      z 0 ∈ Z → z 1 ∈ Z → 0 < W (z 0) (z 1) →
        ¬ ∀ j ∈ F, z 0 ∈ P.neighbor j ∧ z 1 ∈ P.neighbor j := by
    filter_upwards [he] with z hz hx hy hxy hn
    apply hz
    refine ⟨?_, ?_, ?_⟩
    · intro a
      fin_cases a <;> assumption
    · intro a b hab
      fin_cases a <;> fin_cases b
      · exact False.elim (hab rfl)
      · exact hxy
      · change 0 < W (z 1) (z 0)
        rw [W.symmetric (z 1) (z 0)]
        exact hxy
      · exact False.elim (hab rfl)
    · intro a j hj
      fin_cases a
      · exact (hn j hj).1
      · exact (hn j hj).2
  have hm : MeasurableSet {z : Ω × Ω |
      z.1 ∈ Z → z.2 ∈ Z → 0 < W z.1 z.2 →
        ¬ ∀ j ∈ F, z.1 ∈ P.neighbor j ∧ z.2 ∈ P.neighbor j} := by
    have hbad := ((hZ.prod hZ).inter (measurableSet_lt (measurable_const (a := (0 : ℝ))) W.measurable_uncurry)).inter
      (Finset.measurableSet_biInter F (fun j _ => (P.neighbor_measurable j).prod (P.neighbor_measurable j)))
    convert hbad.compl using 1
    congr 1
    ext z
    simp only [mem_setOf_eq, mem_compl_iff, mem_inter_iff, mem_iInter, mem_prod]
    tauto
  have hp := measurePreserving_pair_coordinates (fun _ : Fin 2 => μ)
    (show (0 : Fin 2) ≠ 1 by decide)
  have hh := (ae_map_iff hp.measurable.aemeasurable hm).mpr hsource
  simpa only [hp.map_eq] using hh

end MarkedBlockSystem

end DensityHS.Graphon
