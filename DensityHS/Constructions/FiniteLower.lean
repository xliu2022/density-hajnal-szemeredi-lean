module

public import DensityHS.Constructions.FiniteModel
public import DensityHS.Constructions.FiniteAlgebra

/-!
# Finite lower constructions with a uniform error bound

Author and maintainer: Xizhi Liu.

The core parts have equal integer sizes.  Fewer than `r` isolated vertices
absorb the remainder, giving an error at most `(r+1)/n` in normalized density.
-/

@[expose] public section

namespace DensityHS.Constructions

open Finset

theorem exists_relabel_construction {a b t q z n r k : ℕ}
    (hsize : n = a + b + t * q + z)
    (hpack : HasPackingNumberAtMost r (constructionGraph a b t q z) k) :
    ∃ G : SimpleGraph (Fin n), HasPackingNumberAtMost r G k ∧
      edgeMass G (fun _ => 1) = coreEdgePolynomial a b t q := by
  classical
  let e : Fin n ≃ ConstructionVertices a b t q z :=
    Fintype.equivOfCardEq (by simpa only [Fintype.card_fin, constructionVertices_card] using hsize)
  refine ⟨(constructionGraph a b t q z).comap e,
    packing_bound_pullback hpack e.toEmbedding, ?_⟩
  exact (edgeMass_reindex e (constructionGraph a b t q z) (fun _ => 1)).trans
    (constructionGraph_mass a b t q z)

theorem uniform_lower_of_one_lower {n : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) {D C : ℝ}
    (h : D * (n : ℝ) ^ 2 - C * n ≤ edgeMass G (fun _ => 1)) :
    D - C / n ≤ edgeMass G (Regularity.uniformWeight (Fin n)) := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have heq : (D - C / n) * (n : ℝ) ^ 2 = D * (n : ℝ) ^ 2 - C * n := by
    field_simp
  rw [Regularity.edgeMass_one] at h
  rw [Regularity.edgeMass_uniform, Fintype.card_fin]
  exact (le_div_iff₀ (sq_pos_of_pos hnR)).mpr (heq ▸ h)

/-- The finite `B_i` construction, with isolated integer remainders. -/
theorem exists_finite_B {r i n k : ℕ} (hn : 0 < n)
    (hi : 1 ≤ i) (hir : i < r) (hk : r * k ≤ n) :
    ∃ G : SimpleGraph (Fin n), HasPackingNumberAtMost r G k ∧
      B r i ((k : ℝ) / n) - ((r : ℝ) + 1) / n ≤
        edgeMass G (Regularity.uniformWeight (Fin n)) := by
  let q := (n - i * k) / (r - i)
  let z := (n - i * k) % (r - i)
  have ht : 0 < r - i := Nat.sub_pos_of_lt hir
  have hia : i * k ≤ n := (Nat.mul_le_mul_right k hir.le).trans hk
  have hmod := Nat.mod_add_div (n - i * k) (r - i)
  have hsize : n = i * k + (r - i) * q + z := by dsimp [q, z]; omega
  have hz : z < r - i := Nat.mod_lt _ ht
  have hpack : HasPackingNumberAtMost r
      (constructionGraph (i * k) 0 (r - i) q z) k := by
    simpa only [Nat.add_sub_of_le hir.le] using
      (constructionB_packing (k := k) (q := q) (z := z) (by omega : 0 < i) ht)
  obtain ⟨G, hG, hmass⟩ := exists_relabel_construction
    (by simpa only [Nat.add_zero] using hsize) hpack
  refine ⟨G, hG, uniform_lower_of_one_lower hn G ?_⟩
  rw [hmass]
  simpa only [Nat.cast_mul, Nat.cast_zero] using B_finite_lower hn hir hk hsize hz

/-- The finite exceptional `A` construction on its admissible domain. -/
theorem exists_finite_A {r n k : ℕ} (hr : 3 ≤ r) (hn : 0 < n)
    (hdom : ADomain r ((k : ℝ) / n)) :
    ∃ G : SimpleGraph (Fin n), HasPackingNumberAtMost r G k ∧
      A r ((k : ℝ) / n) - ((r : ℝ) + 1) / n ≤
        edgeMass G (Regularity.uniformWeight (Fin n)) := by
  let q := n / (r - 1)
  let z := n % (r - 1)
  have hq : 2 * k ≤ q := A_integer_capacity hr hn hdom
  have ht : 0 < r - 1 := by omega
  have hsize : n = (r - 1) * q + z := (Nat.div_add_mod n (r - 1)).symm
  have hz : z < r - 1 := Nat.mod_lt _ ht
  have hsum : 2 * k + (q - 2 * k) = q := Nat.add_sub_of_le hq
  have hparts : (r - 1) * q = q + (r - 2) * q := by
    have heq : r - 1 = 1 + (r - 2) := by omega
    rw [heq, Nat.add_mul, Nat.one_mul]
  have hmodelsize : n = 2 * k + (q - 2 * k) + (r - 2) * q + z := by
    rw [hsum, ← hparts]
    exact hsize
  have hpack : HasPackingNumberAtMost r
      (constructionGraph (2 * k) (q - 2 * k) (r - 2) q z) k := by
    simpa only [Nat.sub_add_cancel (by omega : 2 ≤ r)] using
      constructionA_packing k (q - 2 * k) (r - 2) q z
  obtain ⟨G, hG, hmass⟩ := exists_relabel_construction hmodelsize hpack
  refine ⟨G, hG, uniform_lower_of_one_lower hn G ?_⟩
  rw [hmass]
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using A_finite_lower hn hr hq hsize hz

/-- The finite `R` construction, using all zero-cover vertices in one part. -/
theorem exists_finite_R {r n k : ℕ} (hr : 3 ≤ r) (hn : 0 < n)
    (hk : r * k ≤ n) (hdom : RDomain r ((k : ℝ) / n)) :
    ∃ G : SimpleGraph (Fin n), HasPackingNumberAtMost r G k ∧
      R r ((k : ℝ) / n) - ((r : ℝ) + 1) / n ≤
        edgeMass G (Regularity.uniformWeight (Fin n)) := by
  let L := n - r * k
  let a := n - (r - 1) * L
  have hcap : (r - 1) * L ≤ n := R_integer_capacity hr hn hk hdom
  have hL : (L : ℝ) = (n : ℝ) - (r : ℝ) * k := by
    dsimp [L]
    rw [Nat.cast_sub hk, Nat.cast_mul]
  have hsize : n = a + (r - 1) * L := (Nat.sub_add_cancel hcap).symm
  have hparts : (r - 1) * L = L + (r - 2) * L := by
    have heq : r - 1 = 1 + (r - 2) := by omega
    rw [heq, Nat.add_mul, Nat.one_mul]
  have hmodelsize : n = a + L + (r - 2) * L + 0 := by
    rw [hsize, hparts]
    omega
  have hactive : a + (r - 2) * L ≤ (r - 2 + 2) * k := by
    have hnk : r * k + L = n := Nat.add_sub_of_le hk
    have hr2 : r - 2 + 2 = r := by omega
    rw [hr2]
    rw [hparts] at hsize
    omega
  have hpack : HasPackingNumberAtMost r
      (constructionGraph a L (r - 2) L 0) k := by
    simpa only [Nat.sub_add_cancel (by omega : 2 ≤ r)] using
      (constructionR_packing (b := L) (z := 0) hactive)
  obtain ⟨G, hG, hmass⟩ := exists_relabel_construction hmodelsize hpack
  refine ⟨G, hG, uniform_lower_of_one_lower hn G ?_⟩
  rw [hmass]
  exact R_finite_lower hn hr hL hsize

/-- The three explicit finite families realize the full envelope with a
uniform error at most `(r+1)/n`. -/
theorem finite_lower_construction {r n k : ℕ} (hr : 3 ≤ r)
    (hn : 0 < n) (hk : r * k ≤ n) :
    ∃ G : SimpleGraph (Fin n), HasPackingNumberAtMost r G k ∧
      Phi r ((k : ℝ) / n) - ((r : ℝ) + 1) / n ≤
        edgeMass G (Regularity.uniformWeight (Fin n)) := by
  rcases Phi_mem_branchValues hr ((k : ℝ) / n) with
    ⟨i, hi, hir, heq⟩ | ⟨hdom, heq⟩ | ⟨hdom, heq⟩
  · simpa only [heq] using exists_finite_B hn hi hir hk
  · simpa only [heq] using exists_finite_A hr hn hdom
  · simpa only [heq] using exists_finite_R hr hn hk hdom

end DensityHS.Constructions
