module

public import DensityHS.Rainbow.BlockCounting
public import DensityHS.Rainbow.ConnectorAbundance

/-!
# Counting concrete local absorber maps

A base rainbow clique and a disjoint common connector at each of its vertices
give quadratically many labelled positions.  Greedy block counting proves a
uniform positive lower bound for the number of these actual local absorbers.

Formalization author and maintainer: Xizhi Liu.
-/

@[expose] public section

open Finset

namespace DensityHS.Rainbow

attribute [local instance] Classical.propDecidable

variable {V K : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {C : G.EdgeLabeling K}

abbrev AbsorberPosition (t : ℕ) := Fin (t + 1) ⊕ (Fin (t + 1) × Fin t)

def absorberMerge {r t : ℕ} (y : Fin r → V) (g : Fin r → Fin t → V) :
    (Fin r ⊕ (Fin r × Fin t)) → V := Sum.elim y fun p => g p.1 p.2

theorem absorberMerge_image {r t : ℕ} (y : Fin r → V) (g : Fin r → Fin t → V) :
    univ.image (absorberMerge y g) = univ.image y ∪ univ.biUnion (fun i => univ.image (g i)) := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨a, _, rfl⟩ := mem_image.mp hv
    rcases a with i | ⟨i, j⟩
    · exact mem_union_left _ (mem_image.mpr ⟨i, mem_univ _, rfl⟩)
    · exact mem_union_right _ (mem_biUnion.mpr ⟨i, mem_univ _,
        mem_image.mpr ⟨j, mem_univ _, rfl⟩⟩)
  · intro hv
    rcases mem_union.mp hv with hv | hv
    · obtain ⟨i, _, rfl⟩ := mem_image.mp hv
      exact mem_image.mpr ⟨Sum.inl i, mem_univ _, rfl⟩
    · obtain ⟨i, _, hi⟩ := mem_biUnion.mp hv
      obtain ⟨j, _, rfl⟩ := mem_image.mp hi
      exact mem_image.mpr ⟨Sum.inr (i, j), mem_univ _, rfl⟩

theorem absorberMerge_injective {r t : ℕ} {y : Fin r → V} {g : Fin r → Fin t → V}
    (hy : Function.Injective y)
    (hg : Function.Injective (fun p : Fin r × Fin t => g p.1 p.2))
    (havoid : ∀ i j k, g i j ≠ y k) : Function.Injective (absorberMerge y g) := by
  intro a b hab
  rcases a with i | ⟨i, j⟩ <;> rcases b with k | ⟨k, l⟩
  · exact congrArg Sum.inl (hy hab)
  · exact False.elim (havoid k l i hab.symm)
  · exact False.elim (havoid i j k hab)
  · exact congrArg Sum.inr (hg hab)

noncomputable def localAbsorberMaps (t : ℕ) (C : G.EdgeLabeling K) (X : Finset V) :
    Finset (AbsorberPosition t → V) :=
  mapFamily fun f => Function.Injective f ∧ IsLocalAbsorber (t + 1) C X (univ.image f)

theorem merge_mem_localAbsorberMaps {t : ℕ} (x : Fin (t + 1) ↪ V)
    {y : Fin (t + 1) → V} {g : Fin (t + 1) → Fin t → V}
    (hy : y ∈ rainbowCliqueMaps (t + 1) C) (hYX : ∀ i, y i ∉ univ.image x)
    (hg : IsDisjointBlockChoice
      (fun i => commonConnectorMaps t C (x i) (y i)) (univ.image x ∪ univ.image y) g) :
    absorberMerge y g ∈ localAbsorberMaps t C (univ.image x) := by
  classical
  obtain ⟨hyinj, hyclique⟩ := mem_mapFamily.mp hy
  let ye : Fin (t + 1) ↪ V := ⟨y, hyinj⟩
  let S := fun i => univ.image (g i)
  have hSdis : (Set.univ : Set (Fin (t + 1))).PairwiseDisjoint S := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro v hvi hvj
    obtain ⟨a, _, ha⟩ := mem_image.mp hvi
    obtain ⟨b, _, hb⟩ := mem_image.mp hvj
    have hh : (i, a) = (j, b) := hg.2.2 (ha.trans hb.symm)
    exact hij (congrArg Prod.fst hh)
  have hSavoid : ∀ i j, x j ∉ S i ∧ ye j ∉ S i := by
    intro i j
    constructor
    · intro hx
      obtain ⟨a, _, ha⟩ := mem_image.mp hx
      exact hg.2.1 i a (mem_union_left _ (mem_image.mpr ⟨j, mem_univ _, ha.symm⟩))
    · intro hy
      obtain ⟨a, _, ha⟩ := mem_image.mp hy
      exact hg.2.1 i a (mem_union_right _ (mem_image.mpr ⟨j, mem_univ _, ha.symm⟩))
  have hconn : ∀ i, IsCommonConnector (t + 1) C (x i) (ye i) (S i) := by
    intro i
    exact (mem_mapFamily.mp (hg.1 i)).2
  have hXY : Disjoint (univ.image x) (univ.image ye) := by
    apply Finset.disjoint_left.mpr
    intro v hvX hvY
    obtain ⟨i, _, rfl⟩ := mem_image.mp hvY
    exact hYX i hvX
  have hlocal := localAbsorber_of_disjoint_connectors x ye S hyclique hXY hSdis hSavoid hconn
  apply mem_mapFamily.mpr
  refine ⟨absorberMerge_injective hyinj hg.2.2 ?_, ?_⟩
  · intro i j k heq
    exact hg.2.1 i j (mem_union_right _ (mem_image.mpr ⟨k, mem_univ _, heq.symm⟩))
  · rw [absorberMerge_image]
    convert hlocal using 1

theorem localAbsorberMaps_card_lower (t : ℕ) (x : Fin (t + 1) ↪ V)
    {M₀ M : ℝ} (hM : 0 ≤ M)
    (hbase : M₀ ≤ (((rainbowCliqueMaps (t + 1) C).filter
      (fun y => ∀ i, y i ∉ univ.image x)).card : ℝ))
    (hconn : ∀ u v (U : Finset V), U.card ≤ (t + 1) * (t + 2) →
      M ≤ (((commonConnectorMaps t C u v).filter (fun f => ∀ j, f j ∉ U)).card : ℝ)) :
    M₀ * M ^ (t + 1) ≤ ((localAbsorberMaps t C (univ.image x)).card : ℝ) := by
  classical
  let Base := (rainbowCliqueMaps (t + 1) C).filter (fun y => ∀ i, y i ∉ univ.image x)
  let Tail := fun y : Fin (t + 1) → V => disjointBlockChoices
    (fun i => commonConnectorMaps t C (x i) (y i)) (univ.image x ∪ univ.image y)
  let Choices := Base.sigma Tail
  let merge : (Σ _y : Fin (t + 1) → V, Fin (t + 1) → Fin t → V) → (AbsorberPosition t → V) :=
    fun yg => absorberMerge yg.1 yg.2
  have hm : Function.Injective merge := by
    rintro ⟨y, g⟩ ⟨y', g'⟩ h
    have hyy : y = y' := funext fun i => congrFun h (Sum.inl i)
    subst y'
    have hgg : g = g' := funext fun i => funext fun j => congrFun h (Sum.inr (i, j))
    subst g'
    rfl
  have htail (y : Fin (t + 1) → V) : M ^ (t + 1) ≤ (Tail y).card := by
    apply disjointBlockChoices_card_lower (t + 1) t ((t + 1) * (t + 2)) hM
    · intro i f hf
      exact (mem_mapFamily.mp hf).1
    · have hxcard : (univ.image x).card = t + 1 := by
        rw [card_image_of_injective _ x.injective, card_univ, Fintype.card_fin]
      have hycard : (univ.image y).card ≤ t + 1 := card_image_le.trans_eq (by simp)
      have hh := card_union_le (univ.image x) (univ.image y)
      nlinarith
    · exact fun i U hU => hconn (x i) (y i) U hU
  have hsub : Choices.image merge ⊆ localAbsorberMaps t C (univ.image x) := by
    intro f hf
    obtain ⟨⟨y, g⟩, hyg, rfl⟩ := mem_image.mp hf
    obtain ⟨hyBase, hgTail⟩ := mem_sigma.mp hyg
    obtain ⟨hy, hYX⟩ := mem_filter.mp hyBase
    exact merge_mem_localAbsorberMaps x hy hYX (mem_mapFamily.mp hgTail)
  have hcard : Choices.card ≤ (localAbsorberMaps t C (univ.image x)).card := by
    rw [← card_image_of_injective Choices hm]
    exact card_le_card hsub
  have hcount : M₀ * M ^ (t + 1) ≤ (Choices.card : ℝ) := by
    dsimp only [Choices]
    rw [card_sigma, Nat.cast_sum]
    calc
      _ ≤ (Base.card : ℝ) * M ^ (t + 1) :=
        mul_le_mul_of_nonneg_right hbase (pow_nonneg hM _)
      _ = ∑ _y ∈ Base, M ^ (t + 1) := by simp only [sum_const, nsmul_eq_mul]
      _ ≤ _ := sum_le_sum fun y _ => htail y
  exact hcount.trans (by exact_mod_cast hcard)

theorem localAbsorberMaps_abundant {t : ℕ} (ht : 0 < t) {β : ℝ} (hβ : 0 ≤ β)
    (hconn : ∀ x y : V, β * (Fintype.card V : ℝ) ^ t ≤
      ((commonConnectorMaps t C x y).card : ℝ))
    (hlarge : ((2 * (t + 1) ^ 3 : ℕ) : ℝ) ≤ β * Fintype.card V)
    (x : Fin (t + 1) ↪ V) :
    (β / 2) ^ (t + 2) * (Fintype.card V : ℝ) ^ ((t + 1) ^ 2) ≤
      ((localAbsorberMaps t C (univ.image x)).card : ℝ) := by
  have hbase := rainbowCliqueMaps_card_lower_of_connectors (fun v => hconn v v)
  have hbsize : ((2 * (t + 1) * (t + 1) : ℕ) : ℝ) ≤ β * Fintype.card V := by
    apply le_trans ?_ hlarge
    have hh := Nat.mul_le_mul_left (2 * (t + 1) * (t + 1))
      (show 1 ≤ t + 1 by omega)
    convert (show (2 * (t + 1) * (t + 1) : ℕ) ≤ 2 * (t + 1) ^ 3 from
      by convert hh using 1 <;> ring) using 1 <;> norm_cast
  have hcsize : ((2 * t * ((t + 1) * (t + 2)) : ℕ) : ℝ) ≤ β * Fintype.card V := by
    apply le_trans ?_ hlarge
    exact_mod_cast (show 2 * t * ((t + 1) * (t + 2)) ≤ 2 * (t + 1) ^ 3 by nlinarith)
  have hba := maps_avoiding_abundant (Nat.zero_lt_succ t)
    (rainbowCliqueMaps (t + 1) C) hbase hbsize (univ.image x)
    (show (univ.image x).card ≤ t + 1 by simpa using card_image_le (s := univ) (f := x))
  have hco (u v : V) (U : Finset V) (hU : U.card ≤ (t + 1) * (t + 2)) :=
    maps_avoiding_abundant ht (commonConnectorMaps t C u v) (hconn u v) hcsize U hU
  have hh := localAbsorberMaps_card_lower t x
    (show 0 ≤ (β / 2) * (Fintype.card V : ℝ) ^ t by positivity) hba hco
  have heq : β / 2 * (Fintype.card V : ℝ) ^ (t + 1) *
      (β / 2 * (Fintype.card V : ℝ) ^ t) ^ (t + 1) =
      (β / 2) ^ (t + 2) * (Fintype.card V : ℝ) ^ ((t + 1) ^ 2) := by
    rw [mul_pow, ← pow_mul,
      show (t + 1) ^ 2 = (t + 1) + t * (t + 1) by ring,
      pow_add (Fintype.card V : ℝ) (t + 1) (t * (t + 1)),
      pow_succ (β / 2) (t + 1)]
    ring
  rw [heq] at hh
  exact hh

theorem localAbsorberMaps_abundant_finset {t : ℕ} (ht : 0 < t) {β : ℝ} (hβ : 0 ≤ β)
    (hconn : ∀ x y : V, β * (Fintype.card V : ℝ) ^ t ≤
      ((commonConnectorMaps t C x y).card : ℝ))
    (hlarge : ((2 * (t + 1) ^ 3 : ℕ) : ℝ) ≤ β * Fintype.card V)
    (X : Finset V) (hX : X.card = t + 1) :
    (β / 2) ^ (t + 2) * (Fintype.card V : ℝ) ^ ((t + 1) ^ 2) ≤
      ((localAbsorberMaps t C X).card : ℝ) := by
  classical
  let e : Fin (t + 1) ≃ X := (X.equivFinOfCardEq hX).symm
  let x : Fin (t + 1) ↪ V := e.toEmbedding.trans (Function.Embedding.subtype _)
  have himage : univ.image x = X := by
    ext v
    constructor
    · intro hv
      obtain ⟨i, _, rfl⟩ := mem_image.mp hv
      exact (e i).property
    · intro hv
      exact mem_image.mpr ⟨e.symm ⟨v, hv⟩, mem_univ _, by simp [x]⟩
  simpa only [himage] using localAbsorberMaps_abundant ht hβ hconn hlarge x

end DensityHS.Rainbow
