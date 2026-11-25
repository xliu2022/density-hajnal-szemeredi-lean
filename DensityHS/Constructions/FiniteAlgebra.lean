module

public import DensityHS.Basic.Envelope
public import Mathlib.Tactic

/-!
# Exact edge-count algebra for the finite extremal constructions

Author and maintainer: Xizhi Liu.

The constructions use equal core parts and fewer than `r` isolated leftover
vertices. These lemmas give a common error of at most `(r+1)n` edges, uniformly
in the packing parameter. All counts are for undirected edges.
-/

@[expose] public section

namespace DensityHS.Constructions

/-- Edges in `(K_a disjointUnion independent_b) join completeEquipartite(t,q)`. -/
noncomputable def coreEdgePolynomial (a b t q : ℝ) : ℝ :=
  a * (a - 1) / 2 + (a + b) * t * q + t * (t - 1) * q ^ 2 / 2

private theorem B_core_deficit {a t q z n : ℝ}
    (ht : 0 < t) (hq : 0 ≤ q) (hz : 0 ≤ z) (hn : n = a + t*q + z) :
    (n^2 - (n-a)^2/t)/2 - coreEdgePolynomial a 0 t q ≤ n*z+a/2 := by
  have hi : (n^2-(n-a)^2/t)/2 - coreEdgePolynomial a 0 t q =
      n*z - z^2/2 - q*z - z^2/(2*t) + a/2 := by
    rw [hn]
    unfold coreEdgePolynomial
    field_simp
    <;> ring
  rw [hi]
  have hz2 : 0 ≤ z^2/2 := by positivity
  have hqz := mul_nonneg hq hz
  have hzt : 0 ≤ z^2/(2*t) := by positivity
  linarith

private theorem A_core_deficit {a b t q z n : ℝ}
    (ht : 0 ≤ t) (hn0 : 0 ≤ n) (hz : 0 ≤ z)
    (hab : a+b=q) (hn : n=(t+1)*q+z) :
    t/(2*(t+1))*n^2+a^2/2 - coreEdgePolynomial a b t q ≤ n*z+a/2 := by
  have ht1 : t+1 ≠ 0 := by positivity
  have hi : t/(2*(t+1))*n^2+a^2/2 - coreEdgePolynomial a b t q =
      n*z+a/2 - n*z/(t+1) - t*z^2/(2*(t+1)) := by
    unfold coreEdgePolynomial
    rw [hab, hn]
    field_simp
    <;> ring
  rw [hi]
  have h1 : 0 ≤ n*z/(t+1) := by positivity
  have h2 : 0 ≤ t*z^2/(2*(t+1)) := by positivity
  linarith

theorem B_scaled {r i n k : ℕ} (hn : 0 < n) (hi : i < r) :
    B r i ((k:ℝ)/n)*(n:ℝ)^2 =
      ((n:ℝ)^2 - ((n:ℝ)-(i:ℝ)*k)^2/((r:ℝ)-i))/2 := by
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hri : (r:ℝ)-(i:ℝ) ≠ 0 := by
    have h : (i:ℝ) < r := by exact_mod_cast hi
    linarith
  unfold B
  field_simp
  <;> ring

theorem A_scaled {r n k : ℕ} (hn : 0 < n) (hr : 2 ≤ r) :
    A r ((k:ℝ)/n)*(n:ℝ)^2 =
      ((r:ℝ)-2)/(2*((r:ℝ)-1))*(n:ℝ)^2+2*(k:ℝ)^2 := by
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hrR : (r:ℝ)-1 ≠ 0 := by
    have h : (2:ℝ) ≤ r := by exact_mod_cast hr
    linarith
  unfold A
  field_simp
  <;> ring

theorem R_scaled {r n k : ℕ} (hn : 0 < n) :
    R r ((k:ℝ)/n)*(n:ℝ)^2 =
      (n:ℝ)^2/2 - (n:ℝ)*((n:ℝ)-(r:ℝ)*k) +
        ((r:ℝ)-1)/2*((n:ℝ)-(r:ℝ)*k)^2 := by
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  unfold R
  field_simp
  <;> ring

/-- Uniform finite error for the `B_i` construction with equal core parts. -/
theorem B_finite_lower {r i n k q z : ℕ} (hn : 0 < n)
    (hi : i < r) (hk : r*k ≤ n)
    (hsize : n=i*k+(r-i)*q+z) (hz : z < r-i) :
    B r i ((k:ℝ)/n)*(n:ℝ)^2 - ((r:ℝ)+1)*n ≤
      coreEdgePolynomial ((i:ℝ)*k) 0 (r-i:ℕ) q := by
  have hcast : ((r-i:ℕ):ℝ) = (r:ℝ)-i := Nat.cast_sub hi.le
  have hpos : (0:ℝ) < (r-i:ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hi
  have hsizeR : (n:ℝ)=(i:ℝ)*k+((r-i:ℕ):ℝ)*q+z := by exact_mod_cast hsize
  have hdef := B_core_deficit hpos (Nat.cast_nonneg q) (Nat.cast_nonneg z) hsizeR
  rw [B_scaled hn hi, ← hcast]
  have ha : (i:ℝ)*k ≤ n := by exact_mod_cast ((Nat.mul_le_mul_right k hi.le).trans hk)
  have hzR : (z:ℝ) ≤ r := by exact_mod_cast (le_trans hz.le (Nat.sub_le r i))
  have hm := mul_le_mul_of_nonneg_left hzR (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  nlinarith only [hdef, ha, hm, (Nat.cast_nonneg n : (0:ℝ) ≤ n)]

/-- Uniform finite error for `A`, allowing isolated leftover vertices. -/
theorem A_finite_lower {r n k q z : ℕ} (hn : 0 < n) (hr : 3 ≤ r)
    (hq : 2*k ≤ q) (hsize : n=(r-1)*q+z) (hz : z < r-1) :
    A r ((k:ℝ)/n)*(n:ℝ)^2 - ((r:ℝ)+1)*n ≤
      coreEdgePolynomial (2*(k:ℝ)) (q-2*k:ℕ) (r-2:ℕ) q := by
  have hc1 : ((r-1:ℕ):ℝ)=(r:ℝ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
  have hc2 : ((r-2:ℕ):ℝ)=(r:ℝ)-2 := by rw [Nat.cast_sub (by omega)]; norm_num
  have hcb : ((q-2*k:ℕ):ℝ)=(q:ℝ)-2*k := by rw [Nat.cast_sub hq]; push_cast; rfl
  have hab : 2*(k:ℝ)+((q-2*k:ℕ):ℝ)=q := by rw [hcb]; ring
  have hs : (n:ℝ)=(((r-2:ℕ):ℝ)+1)*q+z := by
    have hs' : (n:ℝ)=((r-1:ℕ):ℝ)*q+z := by exact_mod_cast hsize
    rw [hc1] at hs'
    rw [hc2]
    linarith
  have hd := A_core_deficit (Nat.cast_nonneg (r-2)) (Nat.cast_nonneg n)
    (Nat.cast_nonneg z) hab hs
  rw [A_scaled hn (by omega)]
  rw [hc2] at hd
  have hden : (r:ℝ)-2+1=(r:ℝ)-1 := by ring
  rw [hden] at hd
  have hqN : q ≤ n := by
    have hq' : q ≤ (r-1)*q := by nlinarith
    omega
  have ha : (2:ℝ)*k ≤ n := by exact_mod_cast hq.trans hqN
  have hzR : (z:ℝ) ≤ r := by exact_mod_cast (le_trans hz.le (Nat.sub_le r 1))
  have hm := mul_le_mul_of_nonneg_left hzR (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  rw [hc2]
  nlinarith only [hd, ha, hm, (Nat.cast_nonneg n : (0:ℝ) ≤ n)]

/-- The `R` construction has only the clique's diagonal correction. -/
theorem R_finite_exact {r n k a L : ℕ} (hn : 0 < n) (hr : 3 ≤ r)
    (hL : (L:ℝ)=(n:ℝ)-(r:ℝ)*k) (hsize : n=a+(r-1)*L) :
    coreEdgePolynomial a L (r-2:ℕ) L =
      R r ((k:ℝ)/n)*(n:ℝ)^2 - (a:ℝ)/2 := by
  rw [R_scaled hn, ← hL]
  have hc1 : ((r-1:ℕ):ℝ)=(r:ℝ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
  have hc2 : ((r-2:ℕ):ℝ)=(r:ℝ)-2 := by rw [Nat.cast_sub (by omega)]; norm_num
  have hs : (n:ℝ)=(a:ℝ)+((r:ℝ)-1)*L := by
    have hs' : (n:ℝ)=(a:ℝ)+((r-1:ℕ):ℝ)*L := by exact_mod_cast hsize
    rwa [hc1] at hs'
  rw [hc2, hs]
  unfold coreEdgePolynomial
  ring

theorem R_finite_lower {r n k a L : ℕ} (hn : 0 < n) (hr : 3 ≤ r)
    (hL : (L:ℝ)=(n:ℝ)-(r:ℝ)*k) (hsize : n=a+(r-1)*L) :
    R r ((k:ℝ)/n)*(n:ℝ)^2 - ((r:ℝ)+1)*n ≤
      coreEdgePolynomial a L (r-2:ℕ) L := by
  rw [R_finite_exact hn hr hL hsize]
  have ha : (a:ℝ) ≤ n := by exact_mod_cast (show a ≤ n by omega)
  have hm : (n:ℝ) ≤ ((r:ℝ)+1)*n := by
    nlinarith [mul_nonneg (Nat.cast_nonneg r : (0:ℝ) ≤ r) (Nat.cast_nonneg n)]
  linarith


/-- The continuous domain of `A` guarantees room for its integer clique. -/
theorem A_integer_capacity {r n k : ℕ} (hr : 3 ≤ r) (hn : 0 < n)
    (hdom : ADomain r ((k:ℝ)/n)) : 2*k ≤ n/(r-1) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hrR : (2:ℝ) < r := by exact_mod_cast (show 2 < r by omega)
  have hden : (0:ℝ) < 2*((r:ℝ)-1) := by linarith
  have hc := (div_le_div_iff₀ hnR hden).mp hdom.2
  apply (Nat.le_div_iff_mul_le (by omega : 0 < r-1)).mpr
  have he : ((2*k*(r-1):ℕ):ℝ) = (k:ℝ)*(2*((r:ℝ)-1)) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega)]
    push_cast
    ring
  have hreal : ((2*k*(r-1):ℕ):ℝ) ≤ n := by
    rw [he]
    simpa using hc
  exact_mod_cast hreal

/-- The continuous `R` domain guarantees that its clique size is nonnegative. -/
theorem R_integer_capacity {r n k : ℕ} (hr : 3 ≤ r) (hn : 0 < n)
    (hk : r*k ≤ n) (hdom : RDomain r ((k:ℝ)/n)) :
    (r-1)*(n-r*k) ≤ n := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hrR : (2:ℝ) < r := by exact_mod_cast (show 2 < r by omega)
  have hden : (0:ℝ) < (r:ℝ)*((r:ℝ)-1) := mul_pos (by linarith) (by linarith)
  have hc := (div_le_div_iff₀ hden hnR).mp hdom.1
  have hreal : (((r-1)*(n-r*k):ℕ):ℝ) ≤ n := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_sub hk]
    push_cast
    nlinarith only [hc]
  exact_mod_cast hreal

end DensityHS.Constructions
