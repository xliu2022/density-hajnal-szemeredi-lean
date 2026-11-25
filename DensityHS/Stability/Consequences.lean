module

public import DensityHS.Stability.FiniteCompactness
public import DensityHS.Constructions.IntegerRealizations

/-!
# Sequence and fixed-range consequences of finite stability

Author and maintainer: Xizhi Liu.

The sequence proof chooses a minimum-error finite construction at every
index.  The uniform stability theorem then bounds this error by every
positive tolerance eventually.  The fixed-range proof obtains a positive
gap to every other admissible branch by compactness and continuity.
-/

@[expose] public section

set_option maxHeartbeats 1000000

namespace DensityHS.Stability

open Filter Set Finset Constructions
open scoped Topology BigOperators

attribute [local instance] Classical.propDecidable

/-- The uniform finite stability conclusion, isolated as a reusable
proposition for the two corollaries below. -/
def FiniteStability (r : ℕ) : Prop :=
  ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ δ > 0, ∃ N : ℕ,
    ∀ n : ℕ, N ≤ n → ∀ k : ℕ, r * k ≤ n →
      ∀ G : SimpleGraph (Fin n), HasPackingNumberAtMost r G k →
      (Phi r ((k : ℝ) / n) - δ) * (n : ℝ) ^ 2 ≤ (G.edgeFinset.card : ℝ) →
      ∃ H : SimpleGraph (Fin n), H ∈ nearActiveFiniteFamily r k η ∧
        (editDistance G H : ℝ) < ε * (n : ℝ) ^ 2

theorem exists_finite_ordinary_family {r n k : ℕ} (hr : 3 ≤ r) (hk : r * k ≤ n) :
    ∃ t : ConstructionKind r, ∃ H : SimpleGraph (Fin n),
      constructionDomain r t ((k : ℝ) / n) ∧ H ∈ finiteConstructionFamily r k t := by
  classical
  let t : ConstructionKind r := .ordinary ⟨0, by omega⟩
  by_cases hn : n = 0
  · subst n
    have hk0 : k = 0 := (Nat.mul_eq_zero.mp (Nat.eq_zero_of_le_zero hk)).resolve_left (by omega)
    subst k
    let f : Fin 0 → ConstructionIndex r t := Fin.elim0
    refine ⟨t, templateGraph (constructionTemplate r t).entry
      (constructionTemplate r t).symmetric f, trivial, f, ?_, rfl⟩
    constructor
    · simp only [Fintype.card_fin, sum_fiberCount]
    · simp [t, constructionSizeCondition, IsOrdinarySize, fiberCount]
  · obtain ⟨q, hq, htype, _⟩ := exists_ordinary_integer_sizes
      (i := 1) (by omega : 1 < r) (Nat.pos_of_ne_zero hn) hk
    obtain ⟨f, hf⟩ := exists_map_with_fiberCount (V := Fin n) q
      (by simpa only [Fintype.card_fin] using hq)
    refine ⟨t, templateGraph (constructionTemplate r t).entry
      (constructionTemplate r t).symmetric f, trivial, f, ?_, rfl⟩
    refine ⟨sum_fiberCount f, ?_⟩
    change IsOrdinarySize r 1 k (fiberCount f)
    simpa only [funext hf] using htype

noncomputable def finiteApproximationCost (r n k : ℕ) (G : SimpleGraph (Fin n))
    (t : ConstructionKind r) (H : SimpleGraph (Fin n)) : ℝ :=
  (editDistance G H : ℝ) / (n : ℝ) ^ 2 +
    (Phi r ((k : ℝ) / n) - constructionDensity r t ((k : ℝ) / n))

theorem finiteApproximationCost_nonneg {r n k : ℕ} (hr : 3 ≤ r)
    (G H : SimpleGraph (Fin n)) (t : ConstructionKind r)
    (hd : constructionDomain r t ((k : ℝ) / n)) :
    0 ≤ finiteApproximationCost r n k G t H := by
  exact add_nonneg (div_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
    (sub_nonneg.mpr (constructionDensity_le_Phi hr t hd))

theorem exists_minimum_finite_approximation {r n k : ℕ} (hr : 3 ≤ r)
    (hk : r * k ≤ n) (G : SimpleGraph (Fin n)) :
    ∃ t : ConstructionKind r, ∃ H : SimpleGraph (Fin n),
      constructionDomain r t ((k : ℝ) / n) ∧ H ∈ finiteConstructionFamily r k t ∧
      ∀ s : ConstructionKind r, ∀ E : SimpleGraph (Fin n),
        constructionDomain r s ((k : ℝ) / n) → E ∈ finiteConstructionFamily r k s →
        finiteApproximationCost r n k G t H ≤ finiteApproximationCost r n k G s E := by
  classical
  let F : Finset (ConstructionKind r × SimpleGraph (Fin n)) := univ.filter fun p =>
    constructionDomain r p.1 ((k : ℝ) / n) ∧ p.2 ∈ finiteConstructionFamily r k p.1
  have hF : F.Nonempty := by
    obtain ⟨t, H, hd, hH⟩ := exists_finite_ordinary_family hr hk
    exact ⟨(t, H), mem_filter.mpr ⟨mem_univ _, hd, hH⟩⟩
  obtain ⟨p, hp, hmin⟩ := F.exists_min_image
    (fun p => finiteApproximationCost r n k G p.1 p.2) hF
  obtain ⟨hd, hH⟩ := (mem_filter.mp hp).2
  refine ⟨p.1, p.2, hd, hH, ?_⟩
  intro s E hs hE
  exact hmin (s, E) (mem_filter.mpr ⟨mem_univ _, hs, hE⟩)

/-- Sequence form of finite stability.  The original vertex sets and exact
integer construction families are retained at every index, including any
finite initial segment of empty graphs. -/
theorem finite_stability_sequence {r : ℕ} (hr : 3 ≤ r) (hstab : FiniteStability r)
    (n k : ℕ → ℕ) (G : ∀ j : ℕ, SimpleGraph (Fin (n j)))
    (hn : Tendsto n atTop atTop) (hk : ∀ j, r * k j ≤ n j)
    (hpack : ∀ j, HasPackingNumberAtMost r (G j) (k j))
    (hdeficit : Tendsto (fun j => Phi r ((k j : ℝ) / n j) -
      ((G j).edgeFinset.card : ℝ) / (n j : ℝ) ^ 2) atTop (𝓝 0)) :
    ∃ t : ℕ → ConstructionKind r, ∃ E : ∀ j : ℕ, SimpleGraph (Fin (n j)),
      (∀ j, constructionDomain r (t j) ((k j : ℝ) / n j) ∧
        E j ∈ finiteConstructionFamily r (k j) (t j)) ∧
      Tendsto (fun j => (editDistance (G j) (E j) : ℝ) / (n j : ℝ) ^ 2 +
        (Phi r ((k j : ℝ) / n j) - constructionDensity r (t j) ((k j : ℝ) / n j)))
        atTop (𝓝 0) := by
  classical
  choose t E hdom hfamily hmin using fun j => exists_minimum_finite_approximation hr (hk j) (G j)
  refine ⟨t, E, fun j => ⟨hdom j, hfamily j⟩, ?_⟩
  change Tendsto (fun j => finiteApproximationCost r (n j) (k j) (G j) (t j) (E j)) atTop (𝓝 0)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, N, hN⟩ := hstab (ε / 4) (ε / 4) (by positivity) (by positivity)
  have hlarge : ∀ᶠ j in atTop, max N 1 ≤ n j := hn.eventually (eventually_ge_atTop _)
  have hsmall : ∀ᶠ j in atTop, Phi r ((k j : ℝ) / n j) -
      ((G j).edgeFinset.card : ℝ) / (n j : ℝ) ^ 2 < δ :=
    hdeficit.eventually (gt_mem_nhds hδ)
  filter_upwards [hlarge, hsmall] with j hjN hjδ
  have hnpos : (0 : ℝ) < n j := by exact_mod_cast (show 0 < n j by omega)
  have hsquare : (0 : ℝ) < (n j : ℝ) ^ 2 := sq_pos_of_pos hnpos
  have hlow : (Phi r ((k j : ℝ) / n j) - δ) * (n j : ℝ) ^ 2 ≤
      ((G j).edgeFinset.card : ℝ) := by
    apply (le_div_iff₀ hsquare).mp
    linarith
  obtain ⟨H, hnear, hEdit⟩ := hN (n j) (by omega) (k j) (hk j) (G j) (hpack j) hlow
  obtain ⟨s, hs, hgap, hH⟩ := hnear
  simp only [Fintype.card_fin] at hs hgap
  have hEdit' : (editDistance (G j) H : ℝ) / (n j : ℝ) ^ 2 < ε / 4 :=
    (div_lt_iff₀ hsquare).mpr hEdit
  have hcost : finiteApproximationCost r (n j) (k j) (G j) s H < ε := by
    unfold finiteApproximationCost
    linarith
  have hmin' := hmin j s H hs hH
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (finiteApproximationCost_nonneg hr (G j) (E j) (t j) (hdom j))]
  exact hmin'.trans_lt hcost

/-- On a compact set with a unique active branch, every other admissible
branch has a uniform positive density gap.  Inadmissible branches are not
included in the comparison. -/
theorem compact_unique_construction_gap {r : ℕ} (hr : 3 ≤ r)
    (J : Set ℝ) (hJ : IsCompact J) (hJrange : J ⊆ Icc 0 (1 / (r : ℝ)))
    (t₀ : ConstructionKind r)
    (hunique : ∀ x ∈ J, ∀ t : ConstructionKind r, constructionDomain r t x →
      constructionDensity r t x = Phi r x → t = t₀) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ x ∈ J, ∀ t : ConstructionKind r, t ≠ t₀ →
      constructionDomain r t x → γ ≤ Phi r x - constructionDensity r t x := by
  classical
  have hper (t : ConstructionKind r) : ∃ γ : ℝ, 0 < γ ∧ ∀ x ∈ J,
      t ≠ t₀ → constructionDomain r t x → γ ≤ Phi r x - constructionDensity r t x := by
    by_cases ht : t = t₀
    · exact ⟨1, by norm_num, fun _ _ h _ => False.elim (h ht)⟩
    let X := J ∩ {x | constructionDomain r t x}
    have hX : IsCompact X := hJ.inter_right (isClosed_constructionDomain r t)
    by_cases hne : X.Nonempty
    · let f := fun x => continuousEnvelope r x - constructionDensity r t x
      have hf : Continuous f := (continuous_continuousEnvelope r).sub (continuous_constructionDensity r t)
      obtain ⟨x₀, hx₀, hmin⟩ := hX.exists_isMinOn hne hf.continuousOn
      have heq (x : ℝ) (hx : x ∈ J) : f x = Phi r x - constructionDensity r t x := by
        dsimp only [f]
        rw [← Phi_eq_continuousEnvelope hr (hJrange hx)]
      have hpos : 0 < f x₀ := by
        rw [heq x₀ hx₀.1]
        apply sub_pos.mpr
        rcases lt_or_eq_of_le (constructionDensity_le_Phi hr t hx₀.2) with h | h
        · exact h
        · exact False.elim (ht (hunique x₀ hx₀.1 t hx₀.2 h))
      refine ⟨f x₀, hpos, ?_⟩
      intro x hx _ hdom
      rw [← heq x hx]
      exact hmin ⟨hx, hdom⟩
    · exact ⟨1, by norm_num, fun x hx _ hdom => False.elim (hne ⟨x, hx, hdom⟩)⟩
  choose γ hγ hbound using hper
  letI : Nonempty (ConstructionKind r) := ⟨.exceptional⟩
  obtain ⟨s, _, hs⟩ := (univ : Finset (ConstructionKind r)).exists_min_image γ univ_nonempty
  exact ⟨γ s, hγ s, fun x hx t ht hd => (hs t (mem_univ _)).trans (hbound t x hx ht hd)⟩

/-- Fixed-range form of finite stability on any compact parameter set with
a unique active construction. -/
theorem finite_stability_unique_range {r : ℕ} (hr : 3 ≤ r) (hstab : FiniteStability r)
    (J : Set ℝ) (hJ : IsCompact J) (hJrange : J ⊆ Icc 0 (1 / (r : ℝ)))
    (t₀ : ConstructionKind r)
    (hunique : ∀ x ∈ J, ∀ t : ConstructionKind r, constructionDomain r t x →
      constructionDensity r t x = Phi r x → t = t₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ k : ℕ, r * k ≤ n →
      (k : ℝ) / n ∈ J → ∀ G : SimpleGraph (Fin n), HasPackingNumberAtMost r G k →
      (Phi r ((k : ℝ) / n) - δ) * (n : ℝ) ^ 2 ≤ (G.edgeFinset.card : ℝ) →
      ∃ H : SimpleGraph (Fin n), H ∈ finiteConstructionFamily r k t₀ ∧
        (editDistance G H : ℝ) < ε * (n : ℝ) ^ 2 := by
  obtain ⟨γ, hγ, hgap⟩ := compact_unique_construction_gap hr J hJ hJrange t₀ hunique
  obtain ⟨δ, hδ, N, hN⟩ := hstab ε (γ / 2) hε (half_pos hγ)
  refine ⟨δ, hδ, N, ?_⟩
  intro n hn k hk hx G hpack hlow
  obtain ⟨H, hnear, hEdit⟩ := hN n hn k hk G hpack hlow
  obtain ⟨t, hd, hnear, hH⟩ := hnear
  simp only [Fintype.card_fin] at hd hnear
  have ht : t = t₀ := by
    by_contra hne
    have hh := hgap _ hx t hne hd
    linarith
  exact ⟨H, ht ▸ hH, hEdit⟩

end DensityHS.Stability
