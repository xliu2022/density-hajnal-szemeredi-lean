module

public import DensityHS.Weighted.SupportCoverLevels
public import DensityHS.Weighted.Clique

/-!
# Elementary rigidity consequences of a saturated clique path support

These lemmas work with the saturation clique itself instead of sorting the
middle coordinates.  They establish uniqueness of zero endpoints and the
separation of positive endpoint levels from the high middle level.

Authors: Xizhi Liu
-/

@[expose] public section

open scoped BigOperators

namespace DensityHS.Weighted.Support

variable {V : Type*} [Fintype V]

/-- Exchange the two end cliques. -/
def CliquePathPartition.swap {G : SimpleGraph V} (P : CliquePathPartition G) :
    CliquePathPartition G where
  left := P.right
  middle := P.middle
  right := P.left
  left_nonempty := P.right_nonempty
  right_nonempty := P.left_nonempty
  left_middle_disjoint := P.middle_right_disjoint.symm
  left_right_disjoint := P.left_right_disjoint.symm
  middle_right_disjoint := P.left_middle_disjoint.symm
  union_eq := by
    ext v
    have h := P.mem_parts v
    simp only [Set.mem_union, Finset.mem_coe, Set.mem_univ, iff_true]
    tauto
  left_clique := P.right_clique
  middle_clique := P.middle_clique
  right_clique := P.left_clique
  middle_eq_universal := P.middle_eq_universal
  ends_anticomplete := by
    intro a ha b hb hab
    exact P.ends_anticomplete b hb a ha hab.symm

/-- An `(r-2)`-clique and two further vertices in the same complete side
give a cover inequality. -/
theorem cover_pair_bound_in_clique {r : ℕ} (hr : 2 ≤ r)
    {G : SimpleGraph V} {c : V → ℝ} (hc : IsCliqueCover r G c)
    {S Q : Finset V} (hS : G.IsClique S) (hQ : G.IsNClique (r - 2) Q)
    (hQS : Q ⊆ S) {a b : V} (haS : a ∈ S) (hbS : b ∈ S)
    (haQ : a ∉ Q) (hbQ : b ∉ Q) (hab : a ≠ b) :
    1 ≤ c a + c b + ∑ q ∈ Q, c q := by
  classical
  have hQa := hQ.insert (fun q hq => hS haS (hQS hq) (by
    intro heq; subst q; exact haQ hq))
  have hbQa : b ∉ insert a Q := by simp [hbQ, Ne.symm hab]
  have hQab := hQa.insert (fun q hq => hS hbS (by
    rcases Finset.mem_insert.mp hq with heq | hmem
    · simpa [heq] using haS
    · exact hQS hmem) (by intro heq; subst q; exact hbQa hq))
  have hsize : r - 2 + 1 + 1 = r := by omega
  rw [hsize] at hQab
  have h := hc.2 _ hQab
  simpa [Finset.sum_insert hbQa, Finset.sum_insert haQ, add_comm, add_left_comm, add_assoc] using h

theorem CliquePathPartition.common_neighbors_mem_middle
    {G : SimpleGraph V} (P : CliquePathPartition G)
    {a z q : V} (ha : a ∈ P.left) (hz : z ∈ P.right)
    (haq : G.Adj a q) (hzq : G.Adj z q) : q ∈ P.middle := by
  rcases P.mem_parts q with hq | hq | hq
  · exact False.elim (P.ends_anticomplete q hq z hz hzq.symm)
  · exact hq
  · exact False.elim (P.ends_anticomplete a ha q hq haq)

theorem CliquePathPartition.saturation_certificate_middle
    {r : ℕ} {G : SimpleGraph V} {c : V → ℝ} (P : CliquePathPartition G)
    (hsat : EdgeSaturatedCover r G c) {a z : V}
    (ha : a ∈ P.left) (hz : z ∈ P.right) :
    ∃ Q : Finset V, G.IsNClique (r - 2) Q ∧ Q ⊆ P.middle ∧
      c a + c z + ∑ q ∈ Q, c q < 1 := by
  have haz : a ≠ z := by
    intro h
    subst z
    exact Finset.disjoint_left.mp P.left_right_disjoint ha hz
  obtain ⟨Q, hQ, hcommon, hcost⟩ := hsat a z haz (P.ends_anticomplete a ha z hz)
  exact ⟨Q, hQ, fun q hq => P.common_neighbors_mem_middle ha hz
    (hcommon q hq).1 (hcommon q hq).2, hcost⟩

/-- There is at most one zero-cover vertex in the left end. -/
theorem CliquePathPartition.zero_left_unique
    {r : ℕ} (hr : 2 ≤ r) {G : SimpleGraph V} {c : V → ℝ}
    (P : CliquePathPartition G) (hc : IsCliqueCover r G c)
    (hsat : EdgeSaturatedCover r G c)
    {a b : V} (ha : a ∈ P.left) (hb : b ∈ P.left)
    (hca : c a = 0) (hcb : c b = 0) : a = b := by
  classical
  by_contra hab
  obtain ⟨z, hz⟩ := P.right_nonempty
  obtain ⟨Q, hQ, hQB, hcost⟩ := P.saturation_certificate_middle hsat ha hz
  have haQ : a ∉ Q := fun h => Finset.disjoint_left.mp P.left_middle_disjoint ha (hQB h)
  have hbQ : b ∉ Q := fun h => Finset.disjoint_left.mp P.left_middle_disjoint hb (hQB h)
  have hlow := cover_pair_bound_in_clique hr hc P.leftSide_clique hQ
    (fun q hq => (P.mem_leftSide q).mpr (Or.inr (hQB hq)))
    ((P.mem_leftSide a).mpr (Or.inl ha)) ((P.mem_leftSide b).mpr (Or.inl hb)) haQ hbQ hab
  have hcz := hc.1 z
  rw [hca, hcb] at hlow
  rw [hca] at hcost
  linarith

/-- There is at most one zero-cover vertex in the right end. -/
theorem CliquePathPartition.zero_right_unique
    {r : ℕ} (hr : 2 ≤ r) {G : SimpleGraph V} {c : V → ℝ}
    (P : CliquePathPartition G) (hc : IsCliqueCover r G c)
    (hsat : EdgeSaturatedCover r G c)
    {a b : V} (ha : a ∈ P.right) (hb : b ∈ P.right)
    (hca : c a = 0) (hcb : c b = 0) : a = b :=
  P.swap.zero_left_unique hr hc hsat ha hb hca hcb

/-- If the middle has at least `r-1` vertices, every pair of endpoints has a
middle vertex with cover value strictly larger than both endpoint values. -/
theorem CliquePathPartition.endpoints_below_middle
    {r : ℕ} (hr : 3 ≤ r) {G : SimpleGraph V} {c : V → ℝ}
    (P : CliquePathPartition G) (hc : IsCliqueCover r G c)
    (hsat : EdgeSaturatedCover r G c) (hB : r - 1 ≤ P.middle.card)
    {a z : V} (ha : a ∈ P.left) (hz : z ∈ P.right) :
    ∃ b ∈ P.middle, c a < c b ∧ c z < c b := by
  classical
  obtain ⟨Q, hQ, hQB, hcost⟩ := P.saturation_certificate_middle hsat ha hz
  have hcard : Q.card < P.middle.card := by rw [hQ.card_eq]; omega
  obtain ⟨b, hb, hbQ⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have haQ : a ∉ Q := fun h => Finset.disjoint_left.mp P.left_middle_disjoint ha (hQB h)
  have hzQ : z ∉ Q := fun h => Finset.disjoint_left.mp P.middle_right_disjoint (hQB h) hz
  have hab : a ≠ b := by
    intro h
    subst b
    exact Finset.disjoint_left.mp P.left_middle_disjoint ha hb
  have hzb : z ≠ b := by
    intro h
    subst b
    exact Finset.disjoint_left.mp P.middle_right_disjoint hb hz
  have hleft := cover_pair_bound_in_clique (by omega : 2 ≤ r) hc P.leftSide_clique hQ
    (fun q hq => (P.mem_leftSide q).mpr (Or.inr (hQB hq)))
    ((P.mem_leftSide a).mpr (Or.inl ha)) ((P.mem_leftSide b).mpr (Or.inr hb)) haQ hbQ hab
  have hright := cover_pair_bound_in_clique (by omega : 2 ≤ r) hc P.rightSide_clique hQ
    (fun q hq => (P.mem_rightSide q).mpr (Or.inl (hQB hq)))
    ((P.mem_rightSide z).mpr (Or.inr hz)) ((P.mem_rightSide b).mpr (Or.inl hb)) hzQ hbQ hzb
  exact ⟨b, hb, by linarith, by linarith⟩

/-- Once two positive levels occur, every cover coordinate is zero or one of
those levels. This is the usable pointwise form of the cardinality theorem. -/
theorem CliquePathPartition.cover_values_of_two_levels
    {r : ℕ} {G : SimpleGraph V} {c : V → ℝ}
    (P : CliquePathPartition G)
    (hext : c ∈ ({d | IsCliqueCover r G d} : Set (V → ℝ)).extremePoints ℝ)
    (u v : V) (hu : 0 < c u) (hv : 0 < c v) (huv : c u ≠ c v) :
    ∀ w, c w = 0 ∨ c w = c u ∨ c w = c v := by
  intro w
  by_cases hw : c w = 0
  · exact Or.inl hw
  · by_cases hwu : c w = c u
    · exact Or.inr (Or.inl hwu)
    · by_cases hwv : c w = c v
      · exact Or.inr (Or.inr hwv)
      · have hp : 0 < c w := lt_of_le_of_ne (hext.1.1 w) (Ne.symm hw)
        exact False.elim (no_three_positive_cover_levels P hext u v w hu hv hp
          huv (Ne.symm hwu) (Ne.symm hwv))

/-- Equal cover coordinates on a missing edge would give a zero tangent
direction, contradicting support minimality. -/
theorem cover_ne_of_nonadj (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → ℝ)
    (hneg : NegativeOnTwoKernels (quadratic (G.adjMatrix ℝ))
      totalFunctional (costFunctional c))
    {u v : V} (huv : u ≠ v) (hnuv : ¬ G.Adj u v) : c u ≠ c v := by
  classical
  intro hcv
  let e : Fin 2 ↪ V := ⟨![u, v], by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all⟩
  have he0 : e 0 = u := rfl
  have he1 : e 1 = v := rfl
  have hnvu : ¬ G.Adj v u := fun h => hnuv h.symm
  have hm : (G.adjMatrix ℝ).submatrix e e = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.submatrix, he0, he1, hnuv, hnvu]
  have hl := negativeOnTwoKernels_submatrix (G.adjMatrix ℝ)
    totalFunctional (costFunctional c) hneg e
  rw [hm, totalFunctional_comp_pushLinear, costFunctional_comp_pushLinear] at hl
  have hnz : (![1, -1] : Fin 2 → ℝ) ≠ 0 := by
    intro h
    have := congrFun h 0
    norm_num at this
  have hsum : totalFunctional (![1, -1] : Fin 2 → ℝ) = 0 := by
    norm_num [totalFunctional, Fin.sum_univ_succ]
  have hcost : costFunctional (c ∘ e) ![1, -1] = 0 := by
    simp [costFunctional, Fin.sum_univ_succ, he0, he1, hcv]
  have h := hl _ hnz hsum hcost
  simpa [quadratic] using h

/-- A finite set of vertices at one designated cover level. -/
noncomputable def coverLevelSet (S : Finset V) (c : V → ℝ) (a : ℝ) : Finset V := by
  classical
  exact S.filter (fun v => c v = a)

@[simp] theorem mem_coverLevelSet (S : Finset V) (c : V → ℝ) (a : ℝ) (v : V) :
    v ∈ coverLevelSet S c a ↔ v ∈ S ∧ c v = a := by
  classical
  simp [coverLevelSet]

/-- With the positive endpoint on the left, the other end is one zero vertex;
all left vertices have one common low value and the middle has low/high values.
The low middle class has at most `r-2` vertices. -/
theorem CliquePathPartition.one_zero_end_two_levels
    {r : ℕ} (hr : 3 ≤ r) {G : SimpleGraph V} [DecidableRel G.Adj] {c : V → ℝ}
    (P : CliquePathPartition G)
    (hext : c ∈ ({d | IsCliqueCover r G d} : Set (V → ℝ)).extremePoints ℝ)
    (hsat : EdgeSaturatedCover r G c)
    (hneg : NegativeOnTwoKernels (quadratic (G.adjMatrix ℝ))
      totalFunctional (costFunctional c))
    (hB : r - 1 ≤ P.middle.card) (hBpos : ∀ b ∈ P.middle, 0 < c b)
    (hleft : ∃ a ∈ P.left, 0 < c a) :
    ∃ z α γ, P.right = {z} ∧ c z = 0 ∧ 0 < α ∧ α < γ ∧
      (∀ a ∈ P.left, c a = α) ∧ (∀ b ∈ P.middle, c b = α ∨ c b = γ) ∧
      (coverLevelSet P.middle c α).card ≤ r - 2 ∧ ∃ b ∈ P.middle, c b = γ := by
  classical
  obtain ⟨a, ha, hca⟩ := hleft
  obtain ⟨z, hz⟩ := P.right_nonempty
  obtain ⟨b, hb, hab, hzb⟩ := P.endpoints_below_middle hr hext.1 hsat hB ha hz
  have hcb : 0 < c b := hBpos b hb
  have hvalues := P.cover_values_of_two_levels hext a b hca hcb (ne_of_lt hab)
  have hupper : ∀ w, c w ≤ c b := by
    intro w
    rcases hvalues w with hw | hw | hw
    · rw [hw]; exact le_of_lt hcb
    · rw [hw]; exact le_of_lt hab
    · exact le_of_eq hw
  have hleftvalues : ∀ w ∈ P.left, c w = 0 ∨ c w = c a := by
    intro w hw
    obtain ⟨b', hb', hwb', _⟩ := P.endpoints_below_middle hr hext.1 hsat hB hw hz
    have hwb : c w < c b := lt_of_lt_of_le hwb' (hupper b')
    rcases hvalues w with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim ((ne_of_lt hwb) h)
  have hrightvalues : ∀ w ∈ P.right, c w = 0 ∨ c w = c a := by
    intro w hw
    obtain ⟨b', hb', _, hwb'⟩ := P.endpoints_below_middle hr hext.1 hsat hB ha hw
    have hwb : c w < c b := lt_of_lt_of_le hwb' (hupper b')
    rcases hvalues w with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim ((ne_of_lt hwb) h)
  have hrightzero : ∀ w ∈ P.right, c w = 0 := by
    intro w hw
    rcases hrightvalues w hw with h | h
    · exact h
    · have haw : a ≠ w := by
        intro heq; subst w
        exact Finset.disjoint_left.mp P.left_right_disjoint ha hw
      exact False.elim (cover_ne_of_nonadj G c hneg haw
        (P.ends_anticomplete a ha w hw) h.symm)
  have hcz : c z = 0 := hrightzero z hz
  have hright : P.right = {z} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨hz, ?_⟩
    intro w hw
    exact P.zero_right_unique (by omega : 2 ≤ r) hext.1 hsat hw hz (hrightzero w hw) hcz
  have hleftlow : ∀ w ∈ P.left, c w = c a := by
    intro w hw
    rcases hleftvalues w hw with h | h
    · have hwz : w ≠ z := by
        intro heq; subst z
        exact Finset.disjoint_left.mp P.left_right_disjoint hw hz
      exact False.elim (cover_ne_of_nonadj G c hneg hwz
        (P.ends_anticomplete w hw z hz) (h.trans hcz.symm))
    · exact h
  have hBlowhigh : ∀ w ∈ P.middle, c w = c a ∨ c w = c b := by
    intro w hw
    rcases hvalues w with h | h | h
    · exact False.elim ((ne_of_gt (hBpos w hw)) h)
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨Q, hQ, hQB, hcost⟩ := P.saturation_certificate_middle hsat ha hz
  have hsubset : coverLevelSet P.middle c (c a) ⊆ Q := by
    intro w hw
    obtain ⟨hwB, hwc⟩ := (mem_coverLevelSet _ _ _ _).mp hw
    by_contra hwQ
    have hzQ : z ∉ Q := fun h => Finset.disjoint_left.mp P.middle_right_disjoint (hQB h) hz
    have hzw : z ≠ w := by
      intro h; subst w
      exact Finset.disjoint_left.mp P.middle_right_disjoint hwB hz
    have hbound := cover_pair_bound_in_clique (by omega : 2 ≤ r) hext.1
      P.rightSide_clique hQ
      (fun q hq => (P.mem_rightSide q).mpr (Or.inl (hQB hq)))
      ((P.mem_rightSide z).mpr (Or.inr hz)) ((P.mem_rightSide w).mpr (Or.inl hwB))
      hzQ hwQ hzw
    rw [hwc] at hbound
    linarith
  have hcount : (coverLevelSet P.middle c (c a)).card ≤ r - 2 := by
    rw [← hQ.card_eq]
    exact Finset.card_le_card hsubset
  exact ⟨z, c a, c b, hright, hcz, hca, hab, hleftlow, hBlowhigh, hcount, b, hb, rfl⟩

end DensityHS.Weighted.Support
