module

public import DensityHS.Constructions.IntegerParts
public import DensityHS.Constructions.FamilyDistance
public import DensityHS.Stability.PrescribedRounding

/-!
# Exact finite extremal construction families

Author and maintainer: Xizhi Liu.

The integer constraints here are those of the manuscript: an exact ik or
2k clique cell, balanced ordinary or Turán parts, and exact final-family
part totals and exceptional mass. Labels specify graphs on the original
vertex type, so no implicit change of vertices is involved.
-/

@[expose] public section

namespace DensityHS.Constructions

open Finset Stability

def ConstructionIndex (r : ℕ) : ConstructionKind r → Type
  | .ordinary i => Option (Fin (r - (i.val + 1)))
  | .exceptional => Option (Option (Fin (r - 2)))
  | .final => Option (Fin (r - 1) × Bool)

instance (r : ℕ) (t : ConstructionKind r) : Fintype (ConstructionIndex r t) := by
  cases t <;> dsimp [ConstructionIndex] <;> infer_instance

instance (r : ℕ) (t : ConstructionKind r) : DecidableEq (ConstructionIndex r t) := by
  cases t <;> dsimp [ConstructionIndex] <;> infer_instance

instance (r : ℕ) (t : ConstructionKind r) : Nonempty (ConstructionIndex r t) := by
  cases t <;> dsimp [ConstructionIndex] <;> infer_instance

noncomputable def constructionTemplate (r : ℕ) (t : ConstructionKind r) :
    FiniteTemplate (ConstructionIndex r t) :=
  match t with
  | .ordinary i => ordinaryTemplate (r - (i.val + 1))
  | .exceptional => exceptionalTemplate (r - 2)
  | .final => finalTemplate (r - 1)

noncomputable def constructionWeight (r : ℕ) (t : ConstructionKind r)
    (x : ℝ) (z : Fin (r - 1) → ℝ) : ConstructionIndex r t → ℝ :=
  match t with
  | .ordinary i => ordinaryWeight (r - (i.val + 1)) (((i.val + 1 : ℕ) : ℝ) * x)
  | .exceptional => exceptionalWeight (r - 2) x
  | .final => finalWeight (r - 1) (1 - (r : ℝ) * x) z

theorem constructionTemplate_kernel (r : ℕ) (t : ConstructionKind r)
    (x : ℝ) (z : Fin (r - 1) → ℝ) :
    (constructionTemplate r t).kernel (constructionWeight r t x z) =
      constructionKernel r t (x, z) := by cases t <;> rfl

theorem constructionWeight_probability {r : ℕ} (hr : 3 ≤ r) (t : ConstructionKind r)
    {x : ℝ} {z : Fin (r - 1) → ℝ} (hx : x ∈ Set.Icc 0 (1 / (r : ℝ)))
    (hz : IsProbabilityWeight z) (hd : constructionDomain r t x) :
    IsProbabilityWeight (constructionWeight r t x z) := by
  cases t with
  | ordinary i => exact ordinaryWeight_admissible (by have := i.isLt; omega) hx
  | exceptional => exact exceptionalWeight_admissible (by omega) hd
  | final => exact finalWeight_admissible (by omega) hd hz

theorem constructionTemplate_binary (r : ℕ) (t : ConstructionKind r)
    (i j : ConstructionIndex r t) :
    (constructionTemplate r t).entry i j = 0 ∨ (constructionTemplate r t).entry i j = 1 := by
  cases t with
  | ordinary k => exact ordinaryTemplate_binary _ i j
  | exceptional => exact exceptionalTemplate_binary _ i j
  | final => exact finalTemplate_binary _ i j

theorem constructionIndex_card_le {r : ℕ} (hr : 2 ≤ r) (t : ConstructionKind r) :
    Fintype.card (ConstructionIndex r t) ≤ 2 * r - 1 := by
  cases t with
  | ordinary i => simp only [ConstructionIndex, Fintype.card_option, Fintype.card_fin]; omega
  | exceptional => simp only [ConstructionIndex, Fintype.card_option, Fintype.card_fin]; omega
  | final =>
    simp only [ConstructionIndex, Fintype.card_option, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_bool]
    omega

def IsOrdinarySize (r i k : ℕ) (q : Option (Fin (r - i)) → ℕ) : Prop :=
  q none = i * k ∧ ∀ a b, q (some a) ≤ q (some b) + 1

def exceptionalPartSize {t : ℕ} (q : Option (Option (Fin t)) → ℕ) : Option (Fin t) → ℕ
  | none => q none + q (some none)
  | some i => q (some (some i))

def IsExceptionalSize (r k : ℕ) (q : Option (Option (Fin (r - 2))) → ℕ) : Prop :=
  q none = 2 * k ∧
    (∀ a b, exceptionalPartSize q a ≤ exceptionalPartSize q b + 1) ∧
    ∀ a, exceptionalPartSize q a ≤ exceptionalPartSize q none

def IsFinalSize (r n k : ℕ) (q : Option (Fin (r - 1) × Bool) → ℕ) : Prop :=
  q none = n - (r - 1) * (n - r * k) ∧
    (∀ j, q (some (j, false)) + q (some (j, true)) = n - r * k) ∧
    (∑ j, q (some (j, true))) = n - r * k

def constructionSizeCondition (r n k : ℕ) (t : ConstructionKind r) :
    (ConstructionIndex r t → ℕ) → Prop :=
  match t with
  | .ordinary i => IsOrdinarySize r (i.val + 1) k
  | .exceptional => IsExceptionalSize r k
  | .final => IsFinalSize r n k

def IsConstructionSize (r n k : ℕ) (t : ConstructionKind r)
    (q : ConstructionIndex r t → ℕ) : Prop :=
  (∑ i, q i) = n ∧ constructionSizeCondition r n k t q

/-- Exact graph family on V, allowing every relabelling of its integer parts. -/
def finiteConstructionFamily {V : Type*} [Fintype V] [DecidableEq V]
    (r k : ℕ) (t : ConstructionKind r) : Set (SimpleGraph V) :=
  {H | ∃ f : V → ConstructionIndex r t,
    IsConstructionSize r (Fintype.card V) k t (fiberCount f) ∧
    H = templateGraph (constructionTemplate r t).entry (constructionTemplate r t).symmetric f}

def nearActiveFiniteFamily {V : Type*} [Fintype V] [DecidableEq V]
    (r k : ℕ) (η : ℝ) : Set (SimpleGraph V) :=
  {H | ∃ t : ConstructionKind r,
    constructionDomain r t ((k : ℝ) / Fintype.card V) ∧
    Phi r ((k : ℝ) / Fintype.card V) - η ≤
      constructionDensity r t ((k : ℝ) / Fintype.card V) ∧
    H ∈ finiteConstructionFamily r k t}

end DensityHS.Constructions
