module

public import DensityHS.Basic.WeightedGraph
public import DensityHS.Weighted.SupportGraphs

/-!
# Saturated supports are cliques or clique blow-ups of a three-vertex path

The proof uses a dominating edge of the chain complement.  The saturation
certificate at that edge consists entirely of universal vertices.  Any
remaining cross-edge would be an induced four-path whose cover levels violate
the strict sign rule.

Authors: Xizhi Liu
-/

@[expose] public section

open scoped BigOperators

namespace DensityHS.Weighted.Support

variable {V : Type*} [Fintype V]

/-- A vertex joined to every other vertex. -/
def IsUniversal (G : SimpleGraph V) (v : V) : Prop :=
  ∀ w, v ≠ w → G.Adj v w

/-- The universal vertices as a finite set. -/
noncomputable def universalVertices (G : SimpleGraph V) : Finset V := by
  classical
  exact Finset.univ.filter (IsUniversal G)

@[simp] theorem mem_universalVertices (G : SimpleGraph V) (v : V) :
    v ∈ universalVertices G ↔ IsUniversal G v := by
  classical
  simp [universalVertices]

/-- The explicit clique certificate obtained when adding any missing edge
would invalidate a fractional cover. -/
def EdgeSaturatedCover (r : ℕ) (G : SimpleGraph V) (c : V → ℝ) : Prop :=
  ∀ u v, u ≠ v → ¬ G.Adj u v →
    ∃ Q : Finset V, G.IsNClique (r - 2) Q ∧
      (∀ q ∈ Q, G.Adj u q ∧ G.Adj v q) ∧
      c u + c v + ∑ q ∈ Q, c q < 1

/-- An edge of the complement witnesses that either endpoint is not universal. -/
theorem not_universal_of_complement_adj (G : SimpleGraph V) {u v : V}
    (huv : Gᶜ.Adj u v) : ¬ IsUniversal G u := by
  intro h
  exact huv.2 (h v huv.1)

/-- Common neighbors of a dominating complement edge are universal. -/
theorem common_neighbors_universal_of_dominating_complement
    (G : SimpleGraph V) {u v : V} (hdom : IsDominatingEdge Gᶜ u v)
    {q : V} (huq : G.Adj u q) (hvq : G.Adj v q) : IsUniversal G q := by
  intro w hqw
  by_contra h
  have hqw' : Gᶜ.Adj q w := ⟨hqw, h⟩
  rcases hdom.2 q w hqw' with h | h
  · exact h.2 huq
  · exact h.2 hvq

/-- Adjoining two nonuniversal adjacent vertices to a universal clique gives
the cover inequality needed in the saturation argument. -/
theorem cover_pair_bound_of_universal_clique
    {r : ℕ} (hr : 2 ≤ r) {G : SimpleGraph V} {c : V → ℝ}
    (hc : IsCliqueCover r G c) {Q : Finset V}
    (hQ : G.IsNClique (r - 2) Q) (hU : ∀ q ∈ Q, IsUniversal G q)
    {a b : V} (ha : ¬ IsUniversal G a) (hb : ¬ IsUniversal G b)
    (hab : G.Adj a b) : 1 ≤ c a + c b + ∑ q ∈ Q, c q := by
  classical
  have haQ : a ∉ Q := fun h => ha (hU a h)
  have hbQ : b ∉ Q := fun h => hb (hU b h)
  have haadj : ∀ q ∈ Q, G.Adj a q := by
    intro q hq
    exact (hU q hq a (by intro heq; subst q; exact haQ hq)).symm
  have hQa := hQ.insert haadj
  have hbadj : ∀ q ∈ insert a Q, G.Adj b q := by
    intro q hq
    rcases Finset.mem_insert.mp hq with h | h
    · subst q
      exact hab.symm
    · exact (hU q h b (by intro heq; subst q; exact hbQ h)).symm
  have hQab := hQa.insert hbadj
  have hsize : r - 2 + 1 + 1 = r := by omega
  rw [hsize] at hQab
  have h := hc.2 (insert b (insert a Q)) hQab
  have hbQa : b ∉ insert a Q := by simp [hbQ, Ne.symm hab.ne]
  simpa [Finset.sum_insert hbQa, Finset.sum_insert haQ, add_comm, add_left_comm, add_assoc] using h

/-- The four-path sign rule in graph notation. -/
theorem fourPath_sign_rule_graph (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → ℝ)
    (hneg : NegativeOnTwoKernels (quadratic (G.adjMatrix ℝ))
      totalFunctional (costFunctional c))
    {a b d e : V} (hab : G.Adj a b) (hbd : G.Adj b d) (hde : G.Adj d e)
    (hnad : ¬ G.Adj a d) (hnae : ¬ G.Adj a e) (hnbe : ¬ G.Adj b e) :
    0 < (c d - c a) * (c e - c b) := by
  classical
  have had : a ≠ d := by rintro rfl; exact hnae hde
  have hae : a ≠ e := by rintro rfl; exact hnbe hab.symm
  have hbe : b ≠ e := by rintro rfl; exact hnae hab
  have hnda : ¬ G.Adj d a := fun h => hnad h.symm
  have hnea : ¬ G.Adj e a := fun h => hnae h.symm
  have hneb : ¬ G.Adj e b := fun h => hnbe h.symm
  let f : Fin 4 → V := ![a, b, d, e]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [f, hab.ne, hbd.ne, hde.ne, Ne.symm had, Ne.symm hae, Ne.symm hbe]
  let ι : Fin 4 ↪ V := ⟨f, hf⟩
  have hm : (G.adjMatrix ℝ).submatrix ι ι = fourPath := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.submatrix, ι, f, fourPath, hab, hab.symm, hbd, hbd.symm,
        hde, hde.symm, hnad, hnae, hnbe, hnda, hnea, hneb]
  simpa [ι, f] using fourPath_sign_rule_submatrix (G.adjMatrix ℝ) c hneg ι hm

/-- At a dominating complement edge, saturation and the four-path sign rule
force all cross-edges in the complement to be present. -/
theorem complete_cross_of_saturated_dominating_edge
    {r : ℕ} (hr : 2 ≤ r) (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → ℝ) (hc : IsCliqueCover r G c)
    (hsat : EdgeSaturatedCover r G c)
    (hneg : NegativeOnTwoKernels (quadratic (G.adjMatrix ℝ))
      totalFunctional (costFunctional c))
    (htri : NoTriangle Gᶜ) {u v : V} (hdom : IsDominatingEdge Gᶜ u v) :
    ∀ x y, Gᶜ.Adj v x → Gᶜ.Adj u y → Gᶜ.Adj x y := by
  classical
  obtain ⟨Q, hQ, hcommon, hcost⟩ := hsat u v hdom.1.1 hdom.1.2
  have hU : ∀ q ∈ Q, IsUniversal G q := by
    intro q hq
    exact common_neighbors_universal_of_dominating_complement G hdom
      (hcommon q hq).1 (hcommon q hq).2
  intro x y hvx huy
  by_contra hnxy
  have hxy : x ≠ y := by
    rintro rfl
    exact htri u v x hdom.1 hvx huy.symm
  have hux : u ≠ x := by
    rintro rfl
    exact hnxy huy
  have hyv : y ≠ v := by
    rintro rfl
    exact hnxy hvx.symm
  have hGux : G.Adj u x := by
    by_contra h
    exact htri u v x hdom.1 hvx (show Gᶜ.Adj x u from ⟨Ne.symm hux, fun hx => h hx.symm⟩)
  have hGyv : G.Adj y v := by
    by_contra h
    exact htri v u y hdom.1.symm huy (show Gᶜ.Adj y v from ⟨hyv, h⟩)
  have hGxy : G.Adj x y := by
    by_contra h
    exact hnxy ⟨hxy, h⟩
  have hsign := fourPath_sign_rule_graph G c hneg hGux hGxy hGyv
    huy.2 hdom.1.2 hvx.symm.2
  have hlu := cover_pair_bound_of_universal_clique hr hc hQ hU
    (not_universal_of_complement_adj G hdom.1)
    (not_universal_of_complement_adj G hvx.symm) hGux
  have hrv := cover_pair_bound_of_universal_clique hr hc hQ hU
    (not_universal_of_complement_adj G huy.symm)
    (not_universal_of_complement_adj G hdom.1.symm) hGyv
  have hpos : 0 < c y - c u := by linarith
  have hminus : c v - c x < 0 := by linarith
  exact (not_lt_of_ge (le_of_lt (mul_neg_of_pos_of_neg hpos hminus))) hsign

/-- A clique blow-up of a three-vertex path, allowing the middle clique to be
empty. The end cliques are the two nonempty sides of the complete bipartite
component of the complement; remaining vertices are universal. -/
def IsCliquePathBlowup (G : SimpleGraph V) : Prop :=
  ∃ A C : Set V, A.Nonempty ∧ C.Nonempty ∧ Disjoint A C ∧
    ∀ x y, Gᶜ.Adj x y ↔ (x ∈ A ∧ y ∈ C) ∨ (x ∈ C ∧ y ∈ A)

theorem cliquePathBlowup_of_complete_cross
    (G : SimpleGraph V) (htri : NoTriangle Gᶜ)
    {u v : V} (hdom : IsDominatingEdge Gᶜ u v)
    (hcross : ∀ x y, Gᶜ.Adj v x → Gᶜ.Adj u y → Gᶜ.Adj x y) :
    IsCliquePathBlowup G := by
  refine ⟨Gᶜ.neighborSet v, Gᶜ.neighborSet u,
    ⟨u, hdom.1.symm⟩, ⟨v, hdom.1⟩, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    intro x hvx hux
    exact htri u v x hdom.1 hvx hux.symm
  · intro x y
    constructor
    · intro hxy
      rcases hdom.2 x y hxy with hux | hvx
      · right
        refine ⟨hux, ?_⟩
        rcases hdom.2 y x hxy.symm with huy | hvy
        · exact False.elim (htri u x y hux hxy huy.symm)
        · exact hvy
      · left
        refine ⟨hvx, ?_⟩
        rcases hdom.2 y x hxy.symm with huy | hvy
        · exact huy
        · exact False.elim (htri v x y hvx hxy hvy.symm)
    · rintro (⟨hvx, huy⟩ | ⟨hux, hvy⟩)
      · exact hcross x y hvx huy
      · exact (hcross y x hvy hux).symm

/-- The full support-structure conclusion from the optimizer's cover,
saturation, and strict tangent negativity properties. -/
theorem complete_or_cliquePathBlowup
    {r : ℕ} (hr : 2 ≤ r) (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → ℝ) (hc : IsCliqueCover r G c)
    (hsat : EdgeSaturatedCover r G c)
    (hneg : NegativeOnTwoKernels (quadratic (G.adjMatrix ℝ))
      totalFunctional (costFunctional c)) :
    G = ⊤ ∨ (IsCliquePathBlowup G ∧ r - 2 ≤ (universalVertices G).card) := by
  classical
  by_cases hG : G = ⊤
  · exact Or.inl hG
  · right
    have hbot : Gᶜ ≠ ⊥ := by
      intro h
      apply hG
      have := congrArg (fun H : SimpleGraph V => Hᶜ) h
      simpa using this
    have hm : Gᶜᶜ.adjMatrix ℝ = G.adjMatrix ℝ := by
      ext x y
      simp only [SimpleGraph.adjMatrix_apply, SimpleGraph.compl_adj]
      by_cases hxy : x = y
      · subst y
        simp
      · simp [hxy]
    have hn : NegativeOnTwoKernels (quadratic (Gᶜᶜ.adjMatrix ℝ))
        totalFunctional (costFunctional c) := by rw [hm]; exact hneg
    have htri := noTriangle_of_negative_complement Gᶜ totalFunctional (costFunctional c) hn
    have htwo := noInducedTwoEdges_of_negative_complement Gᶜ totalFunctional (costFunctional c) hn
    have hfive := noInducedFiveCycle_of_negative_complement Gᶜ totalFunctional (costFunctional c) hn
    obtain ⟨u, v, hdom⟩ := exists_dominating_edge Gᶜ htwo
      (bipartite_of_three_obstructions Gᶜ htri htwo hfive) hbot
    refine ⟨cliquePathBlowup_of_complete_cross G htri hdom
      (complete_cross_of_saturated_dominating_edge hr G c hc hsat hneg htri hdom), ?_⟩
    obtain ⟨Q, hQ, hcommon, _⟩ := hsat u v hdom.1.1 hdom.1.2
    rw [← hQ.card_eq]
    apply Finset.card_le_card
    intro q hq
    apply (mem_universalVertices G q).mpr
    exact common_neighbors_universal_of_dominating_complement G hdom
      (hcommon q hq).1 (hcommon q hq).2

/-- The three finite parts of a clique blow-up of a three-vertex path. -/
structure CliquePathPartition (G : SimpleGraph V) where
  left : Finset V
  middle : Finset V
  right : Finset V
  left_nonempty : left.Nonempty
  right_nonempty : right.Nonempty
  left_middle_disjoint : Disjoint left middle
  left_right_disjoint : Disjoint left right
  middle_right_disjoint : Disjoint middle right
  union_eq : (left : Set V) ∪ (middle : Set V) ∪ (right : Set V) = Set.univ
  left_clique : G.IsClique left
  middle_clique : G.IsClique middle
  right_clique : G.IsClique right
  middle_eq_universal : middle = universalVertices G
  ends_anticomplete : ∀ a ∈ left, ∀ b ∈ right, ¬ G.Adj a b

/-- The complement description produces the ordinary finite three-part
partition used in the cover-rigidity argument. -/
theorem IsCliquePathBlowup.exists_partition
    {G : SimpleGraph V} (h : IsCliquePathBlowup G) :
    Nonempty (CliquePathPartition G) := by
  classical
  obtain ⟨A, C, hA, hC, hdisj, hshape⟩ := h
  have hU : ∀ x, IsUniversal G x ↔ x ∉ A ∧ x ∉ C := by
    intro x
    constructor
    · intro hx
      constructor
      · intro hxa
        obtain ⟨y, hy⟩ := hC
        have hxy := (hshape x y).mpr (Or.inl ⟨hxa, hy⟩)
        exact hxy.2 (hx y hxy.1)
      · intro hxc
        obtain ⟨y, hy⟩ := hA
        have hxy := (hshape x y).mpr (Or.inr ⟨hxc, hy⟩)
        exact hxy.2 (hx y hxy.1)
    · rintro ⟨hxa, hxc⟩ y hxy
      by_contra hnxy
      rcases (hshape x y).mp ⟨hxy, hnxy⟩ with h | h
      · exact hxa h.1
      · exact hxc h.1
  have hAclique : G.IsClique A := by
    intro x hx y hy hxy
    by_contra hnxy
    rcases (hshape x y).mp ⟨hxy, hnxy⟩ with h | h
    · exact Set.disjoint_left.mp hdisj hy h.2
    · exact Set.disjoint_left.mp hdisj hx h.1
  have hCclique : G.IsClique C := by
    intro x hx y hy hxy
    by_contra hnxy
    rcases (hshape x y).mp ⟨hxy, hnxy⟩ with h | h
    · exact Set.disjoint_left.mp hdisj h.1 hx
    · exact Set.disjoint_left.mp hdisj h.2 hy
  refine ⟨{
    left := A.toFinset
    middle := universalVertices G
    right := C.toFinset
    left_nonempty := by simpa using hA
    right_nonempty := by simpa using hC
    left_middle_disjoint := ?_
    left_right_disjoint := ?_
    middle_right_disjoint := ?_
    union_eq := ?_
    left_clique := by simpa using hAclique
    middle_clique := ?_
    right_clique := by simpa using hCclique
    middle_eq_universal := rfl
    ends_anticomplete := ?_ }⟩
  · apply Finset.disjoint_left.mpr
    intro x hxa hxm
    exact ((hU x).mp ((mem_universalVertices G x).mp hxm)).1 (by simpa using hxa)
  · apply Finset.disjoint_left.mpr
    intro x hxa hxc
    exact Set.disjoint_left.mp hdisj (by simpa using hxa) (by simpa using hxc)
  · apply Finset.disjoint_left.mpr
    intro x hxm hxc
    exact ((hU x).mp ((mem_universalVertices G x).mp hxm)).2 (by simpa using hxc)
  · ext x
    simp only [Set.mem_union, Finset.mem_coe, Set.mem_toFinset, Set.mem_univ, iff_true]
    by_cases hxa : x ∈ A
    · exact Or.inl (Or.inl hxa)
    · by_cases hxc : x ∈ C
      · exact Or.inr hxc
      · exact Or.inl (Or.inr ((mem_universalVertices G x).mpr ((hU x).mpr ⟨hxa, hxc⟩)))
  · intro x hx y hy hxy
    exact ((mem_universalVertices G x).mp hx) y hxy
  · intro x hx y hy
    exact ((hshape x y).mpr (Or.inl ⟨by simpa using hx, by simpa using hy⟩)).2

/-- Every vertex in an end clique is joined to every vertex in the middle. -/
theorem CliquePathPartition.left_middle_adj
    {G : SimpleGraph V} (P : CliquePathPartition G)
    {a b : V} (ha : a ∈ P.left) (hb : b ∈ P.middle) : G.Adj a b := by
  have hab : b ≠ a := by
    intro h
    subst b
    exact Finset.disjoint_left.mp P.left_middle_disjoint ha hb
  have hU : IsUniversal G b := (mem_universalVertices G b).mp
    (P.middle_eq_universal ▸ hb)
  exact (hU a hab).symm

theorem CliquePathPartition.middle_right_adj
    {G : SimpleGraph V} (P : CliquePathPartition G)
    {a b : V} (ha : a ∈ P.middle) (hb : b ∈ P.right) : G.Adj a b := by
  have hab : a ≠ b := by
    intro h
    subst b
    exact Finset.disjoint_left.mp P.middle_right_disjoint ha hb
  have hU : IsUniversal G a := (mem_universalVertices G a).mp
    (P.middle_eq_universal ▸ ha)
  exact hU b hab

/-- The finite partition version of the support theorem, with all three parts
nonempty for clique size at least three. -/
theorem complete_or_three_nonempty_cliques
    {r : ℕ} (hr : 3 ≤ r) (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → ℝ) (hc : IsCliqueCover r G c)
    (hsat : EdgeSaturatedCover r G c)
    (hneg : NegativeOnTwoKernels (quadratic (G.adjMatrix ℝ))
      totalFunctional (costFunctional c)) :
    G = ⊤ ∨ ∃ P : CliquePathPartition G, P.middle.Nonempty ∧ r - 2 ≤ P.middle.card := by
  rcases complete_or_cliquePathBlowup (by omega : 2 ≤ r) G c hc hsat hneg with h | ⟨hP, hcard⟩
  · exact Or.inl h
  · obtain ⟨P⟩ := hP.exists_partition
    right
    have hmiddle : r - 2 ≤ P.middle.card := by simpa [P.middle_eq_universal] using hcard
    exact ⟨P, Finset.card_pos.mp (by omega), hmiddle⟩

end DensityHS.Weighted.Support
