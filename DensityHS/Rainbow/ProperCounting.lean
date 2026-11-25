module

public import DensityHS.Rainbow.BadEmbeddings

/-!
# Counting non-rainbow maps with one prescribed root

In a properly coloured graph, a repeated edge colour determines one free
vertex once the other vertices are specified.  This gives a polynomial error
term for the common-connector construction without requiring any whole
multipartite blow-up to be properly coloured.

Formalization author and maintainer: Xizhi Liu.
-/

@[expose] public section

open Finset

namespace DensityHS.Rainbow

variable {V K : Type*} {G : SimpleGraph V} {C : G.EdgeLabeling K}

theorem IsProper.collision_endpoint_ne (hp : IsProper C)
    {x y u v : V} (hxy : G.Adj x y) (huv : G.Adj u v)
    (hc : edgeColor C x y = edgeColor C u v) (hne : s(x, y) ≠ s(u, v)) :
    x ≠ v ∧ y ≠ v := by
  constructor
  · intro hxv
    subst x
    have hyu := hp hxy huv.symm (hc.trans (edgeColor_comm C u v))
    apply hne
    rw [hyu]
    exact Sym2.eq_swap
  · intro hyv
    subst y
    have hxu := hp hxy.symm huv.symm
      ((edgeColor_comm C v x).trans (hc.trans (edgeColor_comm C u v)))
    apply hne
    rw [hxu]

def rootedValue {r : ℕ} (x : V) (f : Fin r → V) : Fin (r + 1) → V := Fin.cons x f

theorem rootedValue_image [DecidableEq V] {r : ℕ} (x : V) (f : Fin r → V) :
    univ.image (rootedValue x f) = Insert.insert x (univ.image f) := by
  ext v
  constructor
  · intro hv
    obtain ⟨i, _, rfl⟩ := mem_image.mp hv
    induction i using Fin.cases with
    | zero => exact mem_insert_self _ _
    | succ i => exact mem_insert_of_mem (mem_image.mpr ⟨i, mem_univ i, rfl⟩)
  · intro hv
    rcases mem_insert.mp hv with hv | hv
    · exact mem_image.mpr ⟨0, mem_univ _, hv.symm⟩
    · obtain ⟨i, _, rfl⟩ := mem_image.mp hv
      exact mem_image.mpr ⟨i.succ, mem_univ _, rfl⟩

theorem rootedValue_eq_of_except {r : ℕ} (x : V) {f g : Fin r → V} {l : Fin r}
    (hfg : ∀ i, i ≠ l → f i = g i) (i : Fin (r + 1)) (hi : i ≠ l.succ) :
    rootedValue x f i = rootedValue x g i := by
  induction i using Fin.cases with
  | zero => rfl
  | succ j =>
    exact hfg j (fun hj => hi (congrArg Fin.succ hj))

noncomputable def rootedCollisionMaps [Fintype V] {r : ℕ}
    (C : G.EdgeLabeling K) (x : V) (i j k : Fin (r + 1)) (l : Fin r) :
    Finset (Fin r → V) :=
  mapFamily fun f : Fin r → V => i ≠ l.succ ∧ j ≠ l.succ ∧ k ≠ l.succ ∧
    G.Adj (rootedValue x f k) (f l) ∧
    edgeColor C (rootedValue x f i) (rootedValue x f j) =
      edgeColor C (rootedValue x f k) (f l)

theorem rootedCollisionMaps_card_le [Fintype V] {r : ℕ} (hp : IsProper C)
    (x : V) (i j k : Fin (r + 1)) (l : Fin r) :
    (rootedCollisionMaps C x i j k l).card ≤ Fintype.card V ^ (r - 1) := by
  classical
  unfold rootedCollisionMaps
  apply (mapFamily_card_le_of_coordinate_determined _ l ?_).trans_eq
    (by simp only [Fintype.card_fin])
  intro f g hf hg heq
  obtain ⟨hil, hjl, hkl, hfk, hfc⟩ := hf
  obtain ⟨_, _, _, hgk, hgc⟩ := hg
  have hi := rootedValue_eq_of_except x heq i hil
  have hj := rootedValue_eq_of_except x heq j hjl
  have hk := rootedValue_eq_of_except x heq k hkl
  apply hp hfk (by simpa only [hk] using hgk)
  calc
    edgeColor C (rootedValue x f k) (f l) =
        edgeColor C (rootedValue x f i) (rootedValue x f j) := hfc.symm
    _ = edgeColor C (rootedValue x g i) (rootedValue x g j) := by rw [hi, hj]
    _ = edgeColor C (rootedValue x g k) (g l) := hgc
    _ = edgeColor C (rootedValue x f k) (g l) := by rw [hk]

noncomputable def rootedNonRainbowMaps [Fintype V] [DecidableEq V]
    (r : ℕ) (C : G.EdgeLabeling K) (x : V) : Finset (Fin r → V) :=
  mapFamily fun f => ¬IsRainbowOn C (univ.image (rootedValue x f))

theorem rootedNonRainbowMap_has_collision [Fintype V] [DecidableEq V]
    {r : ℕ} (hp : IsProper C) (x : V) {f : Fin r → V}
    (hf : f ∈ rootedNonRainbowMaps r C x) :
    ∃ q : Fin (r + 1) × (Fin (r + 1) × (Fin (r + 1) × Fin r)),
      f ∈ rootedCollisionMaps C x q.1 q.2.1 q.2.2.1 q.2.2.2 := by
  classical
  have hbad : ¬IsRainbowOn C (univ.image (rootedValue x f)) := mem_mapFamily.mp hf
  simp only [IsRainbowOn] at hbad
  push Not at hbad
  obtain ⟨a, b, c, d, ha, hb, hc, hd, hab, hcd, hcol, hne⟩ := hbad
  obtain ⟨i, _, rfl⟩ := mem_image.mp ha
  obtain ⟨j, _, rfl⟩ := mem_image.mp hb
  obtain ⟨k, _, rfl⟩ := mem_image.mp hc
  obtain ⟨l, _, rfl⟩ := mem_image.mp hd
  have hfinish (i j k l : Fin (r + 1))
      (hij : G.Adj (rootedValue x f i) (rootedValue x f j))
      (hkl : G.Adj (rootedValue x f k) (rootedValue x f l))
      (hcolor : edgeColor C (rootedValue x f i) (rootedValue x f j) =
        edgeColor C (rootedValue x f k) (rootedValue x f l))
      (hneq : s(rootedValue x f i, rootedValue x f j) ≠
        s(rootedValue x f k, rootedValue x f l)) (hl : l ≠ 0) :
      ∃ q : Fin (r + 1) × (Fin (r + 1) × (Fin (r + 1) × Fin r)),
        f ∈ rootedCollisionMaps C x q.1 q.2.1 q.2.2.1 q.2.2.2 := by
    obtain ⟨l', rfl⟩ := Fin.eq_succ_of_ne_zero hl
    have hdis := hp.collision_endpoint_ne hij hkl hcolor hneq
    refine ⟨(i, j, k, l'), mem_mapFamily.mpr ⟨?_, ?_, ?_, hkl, hcolor⟩⟩
    · intro hh
      exact hdis.1 (congrArg (rootedValue x f) hh)
    · intro hh
      exact hdis.2 (congrArg (rootedValue x f) hh)
    · intro hh
      exact hkl.ne (congrArg (rootedValue x f) hh)
  by_cases hl : l = 0
  · have hk : k ≠ 0 := by
      intro hk
      apply hcd.ne
      rw [hk, hl]
    exact hfinish i j l k hab hcd.symm
      (hcol.trans (edgeColor_comm C _ _))
      (fun hh => hne (hh.trans Sym2.eq_swap)) hk
  · exact hfinish i j k l hab hcd hcol hne hl

/-- With one root fixed, the number of non-rainbow maps has one lower power
of the ambient graph order. -/
theorem rootedNonRainbowMaps_card_le [Fintype V] [DecidableEq V]
    {r : ℕ} (hp : IsProper C) (x : V) :
    (rootedNonRainbowMaps r C x).card ≤
      (r + 1) ^ 3 * r * Fintype.card V ^ (r - 1) := by
  classical
  let collisions := univ.biUnion fun q :
      Fin (r + 1) × (Fin (r + 1) × (Fin (r + 1) × Fin r)) =>
    rootedCollisionMaps C x q.1 q.2.1 q.2.2.1 q.2.2.2
  have hsub : rootedNonRainbowMaps r C x ⊆ collisions := by
    intro f hf
    obtain ⟨q, hq⟩ := rootedNonRainbowMap_has_collision hp x hf
    exact mem_biUnion.mpr ⟨q, mem_univ q, hq⟩
  calc
    _ ≤ collisions.card := card_le_card hsub
    _ ≤ ∑ q : Fin (r + 1) × (Fin (r + 1) × (Fin (r + 1) × Fin r)),
        (rootedCollisionMaps C x q.1 q.2.1 q.2.2.1 q.2.2.2).card := card_biUnion_le
    _ ≤ ∑ _q : Fin (r + 1) × (Fin (r + 1) × (Fin (r + 1) × Fin r)),
        Fintype.card V ^ (r - 1) :=
      sum_le_sum fun q _ => rootedCollisionMaps_card_le hp x q.1 q.2.1 q.2.2.1 q.2.2.2
    _ = _ := by
      simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_id]
      ring

end DensityHS.Rainbow
