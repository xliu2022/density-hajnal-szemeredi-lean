module

public import DensityHS.Finite.Extremal
public import DensityHS.Constructions.FiniteLower

/-!
# The density Hajnal–Szemerédi theorem for finite graphs

Author and maintainer: Xizhi Liu.

The upper bound comes from the fully proved weighted theorem, Szemerédi
regularity, and integral rounding. Explicit finite constructions give the
lower bound with at most `(r+1)n` missing edges. Together these prove the
asymptotic extremal number uniformly throughout the entire packing range.
-/

@[expose] public section

namespace DensityHS

/-- The explicit uniform lower bound for the extremal number. -/
theorem packingExtremalNumber_lower {r n k : ℕ} (hr : 3 ≤ r)
    (hn : 0 < n) (hk : r*k ≤ n) :
    Phi r ((k:ℝ)/n)*(n:ℝ)^2 - ((r:ℝ)+1)*n ≤
      (packingExtremalNumber r n k : ℝ) := by
  classical
  obtain ⟨G, hG, hlow⟩ := Constructions.finite_lower_construction hr hn hk
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hed : (G.edgeFinset.card : ℝ) ≤ packingExtremalNumber r n k := by
    exact_mod_cast card_edges_le_packingExtremalNumber G hG
  rw [Regularity.edgeMass_uniform, Fintype.card_fin] at hlow
  have hnormalized : Phi r ((k:ℝ)/n) - ((r:ℝ)+1)/n ≤
      (packingExtremalNumber r n k : ℝ)/(n:ℝ)^2 :=
    hlow.trans (div_le_div_of_nonneg_right hed (sq_nonneg _))
  have h := (le_div_iff₀ (sq_pos_of_pos hnR)).mp hnormalized
  have heq : (Phi r ((k:ℝ)/n)-((r:ℝ)+1)/n)*(n:ℝ)^2 =
      Phi r ((k:ℝ)/n)*(n:ℝ)^2 - ((r:ℝ)+1)*n := by
    field_simp
  rwa [heq] at h

/-- **The density Hajnal–Szemerédi theorem.** For every fixed `r≥3`, the
error in `ex(n,(k+1)K_r)=Phi_r(k/n)n²+o(n²)` is uniform over all admissible
integers `k`. Both sides refer to actual finite integral clique packings. -/
theorem density_hajnal_szemeredi {r : ℕ} (hr : 3 ≤ r) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ k : ℕ,
      r*k ≤ n →
      |(packingExtremalNumber r n k : ℝ)-Phi r ((k:ℝ)/n)*(n:ℝ)^2| ≤
        ε*(n:ℝ)^2 := by
  intro ε hε
  obtain ⟨n₁, hupp⟩ := packingExtremalNumber_upper hr hε
  obtain ⟨n₂, hn₂⟩ := exists_nat_gt (((r:ℝ)+1)/ε)
  refine ⟨max n₁ (n₂+1), ?_⟩
  intro n hn k hk
  have hn₁ : n₁ ≤ n := (le_max_left _ _).trans hn
  have hn₂n : n₂+1 ≤ n := (le_max_right _ _).trans hn
  have hnpos : 0 < n := by omega
  have hnR : (0:ℝ) < n := by exact_mod_cast hnpos
  have hn₂R : (n₂:ℝ) < n := by exact_mod_cast (show n₂ < n by omega)
  have hCn : (r:ℝ)+1 ≤ ε*n := by
    have h := (div_lt_iff₀ hε).mp (hn₂.trans hn₂R)
    nlinarith only [h]
  have herror : ((r:ℝ)+1)*n ≤ ε*(n:ℝ)^2 := by
    have h := mul_le_mul_of_nonneg_right hCn hnR.le
    nlinarith only [h]
  have hlow := packingExtremalNumber_lower hr hnpos hk
  have hhigh := hupp n hn₁ k hk
  apply abs_le.mpr
  constructor <;> nlinarith only [hlow, hhigh, herror]

/-- The same theorem with the manuscript's range written as `k≤floor(n/r)`.
Natural-number division is precisely the required floor. -/
theorem density_hajnal_szemeredi_floor {r : ℕ} (hr : 3 ≤ r) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ k : ℕ,
      k ≤ n/r →
      |(packingExtremalNumber r n k : ℝ)-Phi r ((k:ℝ)/n)*(n:ℝ)^2| ≤
        ε*(n:ℝ)^2 := by
  intro ε hε
  obtain ⟨n₀, h⟩ := density_hajnal_szemeredi hr ε hε
  refine ⟨n₀, ?_⟩
  intro n hn k hk
  apply h n hn k
  have hkr := (Nat.le_div_iff_mul_le (by omega : 0 < r)).mp hk
  simpa only [Nat.mul_comm] using hkr

end DensityHS
