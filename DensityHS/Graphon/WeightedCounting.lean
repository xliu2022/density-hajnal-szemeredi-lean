module

/-
Copyright (c) 2026 Cameron Freer and Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer, Xizhi Liu

The factorization and telescoping argument is adapted from Cameron Freer's
Graphon/Counting.lean at 9f7be59fa754d260a544b4cfd83d6a5b94f7552e.
The adaptation permits diagonal factors in the fixed prefix, representing
arbitrary measurable vertex weights. All kernels here are pointwise bounded.
-/

public import DensityHS.Graphon.VendorBridge
public import DensityHS.Vendor.Graphon.Counting

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set Filter
open scoped BigOperators

variable {α V : Type*} [MeasurableSpace α] {μ : Measure α}
  [IsProbabilityMeasure μ] [Fintype V] [DecidableEq V]

abbrev Kernel.pairFun (W : Kernel α) : α × α → ℝ := Function.uncurry W

theorem Kernel.pairFun_mem_Icc (W : Kernel α) (z : α × α) :
    W.pairFun z ∈ Icc (0:ℝ) 1 := ⟨W.nonneg z.1 z.2,W.le_one z.1 z.2⟩

theorem kernel_eval_pair_ae (W : Kernel α) {u v : V} (huv : u ≠ v) :
    ∀ᵐ x : V → α ∂Measure.pi (fun _ => μ),
      (W.toVendorGraphon μ).toAEEqFun (x u,x v) = W.pairFun (x u,x v) := by
  have hind := (ProbabilityTheory.iIndepFun_pi (μ := fun _ : V => μ)
    (fun _ => aemeasurable_id)).indepFun huv
  have hm : MeasurePreserving (fun x : V → α => (x u,x v))
      (Measure.pi (fun _ => μ)) (μ.prod μ) := by
    refine ⟨(measurable_pi_apply u).prodMk (measurable_pi_apply v),?_⟩
    have h := hind.map_prod_eq_prod_map_map
      (measurable_pi_apply u).aemeasurable (measurable_pi_apply v).aemeasurable
    simpa only [id, (measurePreserving_eval (fun _ : V => μ) u).map_eq,
      (measurePreserving_eval (fun _ : V => μ) v).map_eq] using h
  exact hm.quasiMeasurePreserving.ae (W.toVendorGraphon_ae μ)

theorem abs_weighted_kernel_pi_diff_le_ae (U W : Kernel α) (u v : V) (huv : u ≠ v)
    (f g : α → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hf_ae : ∀ᵐ a ∂μ, f a ∈ Icc 0 1) (hg_ae : ∀ᵐ a ∂μ, g a ∈ Icc 0 1) :
    |∫ x : V → α, f (x u)*g (x v)*(U.pairFun (x u,x v)-W.pairFun (x u,x v))
      ∂Measure.pi (fun _ => μ)| ≤ kernelCutDistance μ U W := by
  have h := Vendor.Graphon.abs_weighted_pi_integral_diff_le_ae
    (U.toVendorGraphon μ) (W.toVendorGraphon μ) u v huv f g hf hg hf_ae hg_ae
  rw [cutNormDiff_toVendorGraphon] at h
  convert h using 2
  apply integral_congr_ae
  filter_upwards [kernel_eval_pair_ae U huv,kernel_eval_pair_ae W huv] with x hxU hxW
  rw [hxU,hxW]

theorem kernel_edge_product_mem_Icc (R : Finset (Sym2 V)) (f : Sym2 V → Kernel α)
    (x : V → α) :
    (∏ e ∈ R, (f e).pairFun (x (Quot.out e).1,x (Quot.out e).2)) ∈ Icc (0:ℝ) 1 :=
  ⟨Finset.prod_nonneg (fun e _ => (f e).nonneg _ _),
   Finset.prod_le_one₀ (fun e _ => (f e).nonneg _ _) (fun e _ => (f e).le_one _ _)⟩

theorem measurable_kernel_edge_product (R : Finset (Sym2 V)) (f : Sym2 V → Kernel α) :
    Measurable (fun x : V → α =>
      ∏ e ∈ R, (f e).pairFun (x (Quot.out e).1,x (Quot.out e).2)) := by
  apply Finset.measurable_prod
  intro e _
  exact (f e).measurable_uncurry.comp
    ((measurable_pi_apply _).prodMk (measurable_pi_apply _))

theorem kernel_counting_integrable_term (U W : Kernel α)
    (S R : Finset (Sym2 V)) (f : Sym2 V → Kernel α) :
    Integrable (fun x : V → α =>
      (∏ e ∈ R, (f e).pairFun (x (Quot.out e).1,x (Quot.out e).2))*
      ((∏ e ∈ S, U.pairFun (x (Quot.out e).1,x (Quot.out e).2))-
       ∏ e ∈ S, W.pairFun (x (Quot.out e).1,x (Quot.out e).2)))
      (Measure.pi (fun _ => μ)) := by
  apply Integrable.of_mem_Icc (-1) 1
  · exact ((measurable_kernel_edge_product R f).mul
      ((measurable_kernel_edge_product S (fun _ => U)).sub
        (measurable_kernel_edge_product S (fun _ => W)))).aemeasurable
  · exact Filter.Eventually.of_forall fun x => by
      have hR := kernel_edge_product_mem_Icc R f x
      have hU := kernel_edge_product_mem_Icc S (fun _ => U) x
      have hW := kernel_edge_product_mem_Icc S (fun _ => W) x
      have hu := mul_le_one₀ hR.2 hU.1 hU.2
      have hw := mul_le_one₀ hR.2 hW.1 hW.2
      have hun := mul_nonneg hR.1 hU.1
      have hwn := mul_nonneg hR.1 hW.1
      constructor <;> nlinarith

theorem weighted_prod_kernel_diff_le
    (U W : Kernel α) (T : Finset (Sym2 V)) (e₀ : Sym2 V)
    (he₀T : e₀ ∉ T)
    (f : Sym2 V → Kernel α)
    (he₀_edge : (Quot.out e₀).1 ≠ (Quot.out e₀).2) :
    |∫ x : V → α,
      (∏ e ∈ T, (f e).pairFun (x (Quot.out e).1, x (Quot.out e).2)) *
      (U.pairFun (x (Quot.out e₀).1, x (Quot.out e₀).2) -
       W.pairFun (x (Quot.out e₀).1, x (Quot.out e₀).2))
    ∂Measure.pi (fun _ => μ)| ≤ kernelCutDistance μ U W := by
  set u₀ := (Quot.out e₀).1 with hu₀_def
  set v₀ := (Quot.out e₀).2 with hv₀_def
  set F : (V → α) → ℝ := fun x =>
    (∏ e ∈ T, (f e).pairFun (x (Quot.out e).1, x (Quot.out e).2)) *
    (U.pairFun (x u₀, x v₀) - W.pairFun (x u₀, x v₀)) with hF_def
  set p : V → Prop := fun i => i = u₀ ∨ i = v₀ with hp_def
  set equiv := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : V => α) p
  set π := Measure.pi (fun _ : V => μ)
  set π_pair := Measure.pi (fun _ : {i : V // p i} => μ)
  set π_rest := Measure.pi (fun _ : {i : V // ¬p i} => μ)
  -- Rewrite integral via the decomposition
  have h_rewrite : ∫ x, F x ∂π = ∫ y, F (equiv.symm y) ∂(π_pair.prod π_rest) := by
    have mp := measurePreserving_piEquivPiSubtypeProd (fun _ : V => μ) p
    have key := mp.integral_comp' (fun y => F (equiv.symm y))
    convert key using 1
    congr 1; ext x; congr 1
    exact (equiv.symm_apply_apply x).symm
  rw [show ∫ x, (∏ e ∈ T, (f e).pairFun (x (Quot.out e).1, x (Quot.out e).2)) *
    (U.pairFun (x u₀, x v₀) - W.pairFun (x u₀, x v₀)) ∂π = ∫ x, F x ∂π from rfl]
  rw [h_rewrite]
  -- Integrability
  have hF_int : Integrable (fun y => F (equiv.symm y)) (π_pair.prod π_rest) := by
    have hF_pi : Integrable F π := by
      have := kernel_counting_integrable_term (μ := μ) U W {e₀} T f
      simp only [Finset.prod_singleton] at this; exact this
    have mp := measurePreserving_piEquivPiSubtypeProd (fun _ : V => μ) p
    rw [show (fun y => F (equiv.symm y)) = F ∘ equiv.symm from rfl]
    rw [← mp.map_eq, integrable_map_equiv equiv]
    convert hF_pi using 1; ext x; simp [Function.comp]
  -- Fubini + triangle inequality + per-section bound
  calc |∫ y, F (equiv.symm y) ∂(π_pair.prod π_rest)|
      = |∫ rest, (∫ pair, F (equiv.symm (pair, rest)) ∂π_pair) ∂π_rest| := by
        rw [integral_prod_symm _ hF_int]
    _ ≤ ∫ rest, |∫ pair, F (equiv.symm (pair, rest)) ∂π_pair| ∂π_rest :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _, kernelCutDistance μ U W ∂π_rest := by
        apply integral_mono_ae
        · exact hF_int.integral_prod_right.norm
        · exact integrable_const _
        · -- Per-section bound: for a.e. rest, |inner integral| ≤ kernelCutDistance μ U W
          -- First derive: under π, all edge evals in T are a.e. in [0,1]
          have h_all_evals_ae : ∀ᵐ x ∂π, ∀ e ∈ T,
              (f e).pairFun (x (Quot.out e).1, x (Quot.out e).2) ∈ Set.Icc 0 1 :=
            Filter.Eventually.of_forall (fun x e _ => (f e).pairFun_mem_Icc _)
          -- Push through equiv: under π_pair.prod π_rest, the same bound holds
          have h_decomp_ae : ∀ᵐ y ∂(π_pair.prod π_rest), ∀ e ∈ T,
              (f e).pairFun (equiv.symm y (Quot.out e).1,
                                equiv.symm y (Quot.out e).2) ∈ Set.Icc 0 1 := by
            have mp := measurePreserving_piEquivPiSubtypeProd (fun _ : V => μ) p
            exact (mp.symm equiv).quasiMeasurePreserving.ae h_all_evals_ae
          -- Swap to get rest first: under π_rest.prod π_pair
          have h_decomp_swap : ∀ᵐ y ∂(π_rest.prod π_pair), ∀ e ∈ T,
              (f e).pairFun (equiv.symm y.swap (Quot.out e).1,
                                equiv.symm y.swap (Quot.out e).2) ∈ Set.Icc 0 1 := by
            have h_swap_mp : MeasurePreserving Prod.swap (π_rest.prod π_pair) (π_pair.prod π_rest) :=
              Measure.measurePreserving_swap
            exact h_swap_mp.quasiMeasurePreserving.ae h_decomp_ae
          -- Fubini: for a.e. rest, for a.e. pair, all evals in [0,1]
          have h_ae_rest : ∀ᵐ rest ∂π_rest, ∀ᵐ pair ∂π_pair, ∀ e ∈ T,
              (f e).pairFun (equiv.symm (pair, rest) (Quot.out e).1,
                                equiv.symm (pair, rest) (Quot.out e).2) ∈ Set.Icc 0 1 :=
            Measure.ae_ae_of_ae_prod h_decomp_swap
          filter_upwards [h_ae_rest] with rest h_pair_ae
          -- Key subtypes for the pair coordinates
          set u₀s : {i : V // p i} := ⟨u₀, Or.inl rfl⟩
          set v₀s : {i : V // p i} := ⟨v₀, Or.inr rfl⟩
          have huv_s : u₀s ≠ v₀s := fun h => he₀_edge (congr_arg Subtype.val h)
          -- The substitution function: sub(a, b)(i) = a if i=u₀, b if i=v₀, rest(i) otherwise
          have h_not_p : ∀ i, i ≠ u₀ → i ≠ v₀ → ¬p i := by
            intro i h1 h2 hi; rcases hi with rfl | rfl <;> contradiction
          set sub : α → α → V → α := fun a b i =>
            if h1 : i = u₀ then a else if h2 : i = v₀ then b
            else rest ⟨i, h_not_p i h1 h2⟩
          -- equiv.symm(pair, rest) agrees with sub(pair u₀s, pair v₀s)
          have h_equiv_sub : ∀ (pair : {i // p i} → α) (i : V),
              equiv.symm (pair, rest) i = sub (pair u₀s) (pair v₀s) i := by
            intro pair i
            -- equiv.symm (pair, rest) i = if p i then pair ⟨i,_⟩ else rest ⟨i,_⟩
            have h_symm_def : equiv.symm (pair, rest) i =
                if h : p i then pair ⟨i, h⟩ else rest ⟨i, h⟩ := by
              simp [equiv, MeasurableEquiv.piEquivPiSubtypeProd,
                Equiv.piEquivPiSubtypeProd]
            by_cases hi_u : i = u₀
            · -- i = u₀: p i holds, equiv gives pair ⟨u₀, _⟩ = pair u₀s
              subst hi_u
              rw [h_symm_def, dif_pos (Or.inl rfl : p u₀)]
              simp only [sub, dite_true]; exact congr_arg pair (Subtype.ext rfl)
            · by_cases hi_v : i = v₀
              · -- i = v₀: p i holds, equiv gives pair ⟨v₀, _⟩ = pair v₀s
                subst hi_v
                rw [h_symm_def, dif_pos (Or.inr rfl : p v₀)]
                simp only [sub, dif_neg hi_u, dite_true]; exact congr_arg pair (Subtype.ext rfl)
              · -- i ≠ u₀, i ≠ v₀: ¬p i, both sides give rest
                rw [h_symm_def, dif_neg (h_not_p i hi_u hi_v)]
                simp only [sub, dif_neg hi_u, dif_neg hi_v]
          -- Rewrite the integrand using sub
          have h_integrand_eq : ∀ (pair : {i // p i} → α),
              F (equiv.symm (pair, rest)) =
              (∏ e ∈ T, (f e).pairFun
                (sub (pair u₀s) (pair v₀s) (Quot.out e).1,
                 sub (pair u₀s) (pair v₀s) (Quot.out e).2)) *
              (U.pairFun (pair u₀s, pair v₀s) -
               W.pairFun (pair u₀s, pair v₀s)) := by
            intro pair
            -- Key substitution equalities
            have h_sub_u : sub (pair u₀s) (pair v₀s) u₀ = pair u₀s := by
              simp only [sub, dite_true]
            have h_sub_v : sub (pair u₀s) (pair v₀s) v₀ = pair v₀s := by
              simp only [sub, dif_neg (Ne.symm he₀_edge), dite_true]
            simp only [F]
            have h_coord : ∀ (i : V), equiv.symm (pair, rest) i =
                sub (pair u₀s) (pair v₀s) i := h_equiv_sub pair
            simp_rw [h_coord]
            rw [h_sub_u, h_sub_v]
          -- Map from π_pair to μ × μ via φ(pair) = (pair u₀s, pair v₀s)
          set φ : ({i // p i} → α) → α × α := fun pair => (pair u₀s, pair v₀s)
          have hφ_meas : Measurable φ :=
            Measurable.prodMk (measurable_pi_apply _) (measurable_pi_apply _)
          have h_map_φ : Measure.map φ π_pair = μ.prod μ := by
            have h_indep : ProbabilityTheory.IndepFun
                (fun pair : {i // p i} → α => pair u₀s)
                (fun pair : {i // p i} → α => pair v₀s)
                π_pair := by
              have := (ProbabilityTheory.iIndepFun_pi
                (μ := fun _ : {i // p i} => μ)
                (fun _ => aemeasurable_id)).indepFun huv_s
              simpa only [id] using this
            rw [show φ = fun pair => ((fun pair : {i // p i} → α => pair u₀s) pair,
                (fun pair : {i // p i} → α => pair v₀s) pair) from rfl]
            rw [ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
              (measurable_pi_apply _).aemeasurable
              (measurable_pi_apply _).aemeasurable |>.mp h_indep,
              (measurePreserving_eval (fun _ : {i // p i} => μ) u₀s).map_eq,
              (measurePreserving_eval (fun _ : {i // p i} => μ) v₀s).map_eq]
          -- No edge in T has both u₀ and v₀ as endpoints
          have h_no_uv : ∀ e ∈ T,
              ¬((Quot.out e).1 = u₀ ∧ (Quot.out e).2 = v₀) ∧
              ¬((Quot.out e).1 = v₀ ∧ (Quot.out e).2 = u₀) := by
            intro e he
            have h_out_e : s((Quot.out e).1, (Quot.out e).2) = e := Quot.out_eq e
            have h_out_e₀ : s((Quot.out e₀).1, (Quot.out e₀).2) = e₀ := Quot.out_eq e₀
            constructor
            · rintro ⟨h1, h2⟩
              apply he₀T
              have : e = e₀ := by
                rw [← h_out_e, ← h_out_e₀, h1, h2]
              rw [this] at he; exact he
            · rintro ⟨h1, h2⟩
              apply he₀T
              have : e = e₀ := by
                rw [← h_out_e, ← h_out_e₀, h1, h2, Sym2.eq_swap]
              rw [this] at he; exact he
          -- Split T based on whether edge touches v₀
          set touchesV : Sym2 V → Bool := fun e =>
            decide ((Quot.out e).1 = v₀) || decide ((Quot.out e).2 = v₀)
          set T_u := T.filter (fun e => !touchesV e)
          set T_v := T.filter (fun e => touchesV e)
          have h_T_disj : Disjoint T_u T_v := by
            rw [Finset.disjoint_filter]; intro e _; simp
          -- For e ∈ T_u: weight depends only on a (not on b)
          have h_Tu_no_v : ∀ e ∈ T_u, (Quot.out e).1 ≠ v₀ ∧ (Quot.out e).2 ≠ v₀ := by
            intro e he
            have hmem := (Finset.mem_filter.mp he).2
            simp only [touchesV] at hmem
            constructor
            · intro h; simp [h] at hmem
            · intro h; simp [h] at hmem
          -- For e ∈ T_v: touching v₀ but not u₀ (since both would make e = e₀)
          have h_Tv_no_u : ∀ e ∈ T_v, (Quot.out e).1 ≠ u₀ ∧ (Quot.out e).2 ≠ u₀ := by
            intro e he
            have heT := (Finset.mem_filter.mp he).1
            have h_touches : (Quot.out e).1 = v₀ ∨ (Quot.out e).2 = v₀ := by
              simp only [T_v, Finset.mem_filter, touchesV, Bool.or_eq_true,
                decide_eq_true_eq] at he
              exact he.2
            have h_nb := h_no_uv e heT
            -- h_nb.1 : ¬(.1 = u₀ ∧ .2 = v₀)
            -- h_nb.2 : ¬(.1 = v₀ ∧ .2 = u₀)
            constructor
            · intro h_eq  -- (Quot.out e).1 = u₀
              rcases h_touches with h | h
              · -- .1 = v₀, but also .1 = u₀, contradicts u₀ ≠ v₀
                exact he₀_edge (h_eq.symm.trans h)
              · -- .2 = v₀, and .1 = u₀ → contradicts h_nb.1
                exact h_nb.1 ⟨h_eq, h⟩
            · intro h_eq  -- (Quot.out e).2 = u₀
              rcases h_touches with h | h
              · -- .1 = v₀, and .2 = u₀ → contradicts h_nb.2
                exact h_nb.2 ⟨h, h_eq⟩
              · -- .2 = v₀, but also .2 = u₀, contradicts u₀ ≠ v₀
                exact he₀_edge (h_eq.symm.trans h)
          -- For e ∈ T_u: weight(e, a, b) = weight(e, a, b') for all b, b'
          -- Helper: sub a b i doesn't depend on b when i ≠ v₀
          have sub_indep_b : ∀ a b₁ b₂ i, i ≠ v₀ → sub a b₁ i = sub a b₂ i := by
            intro a b₁ b₂ i hne
            simp only [sub, dif_neg hne]
          -- Helper: sub a b i doesn't depend on a when i ≠ u₀
          have sub_indep_a : ∀ a₁ a₂ b i, i ≠ u₀ → sub a₁ b i = sub a₂ b i := by
            intro a₁ a₂ b i hne
            simp only [sub, dif_neg hne]
          have h_Tu_indep : ∀ e ∈ T_u, ∀ a b₁ b₂,
              (f e).pairFun (sub a b₁ (Quot.out e).1, sub a b₁ (Quot.out e).2) =
              (f e).pairFun (sub a b₂ (Quot.out e).1, sub a b₂ (Quot.out e).2) := by
            intro e he a b₁ b₂
            have ⟨hne1, hne2⟩ := h_Tu_no_v e he
            rw [sub_indep_b a b₁ b₂ _ hne1, sub_indep_b a b₁ b₂ _ hne2]
          -- For e ∈ T_v: weight(e, a, b) = weight(e, a', b) for all a, a'
          have h_Tv_indep : ∀ e ∈ T_v, ∀ a₁ a₂ b,
              (f e).pairFun (sub a₁ b (Quot.out e).1, sub a₁ b (Quot.out e).2) =
              (f e).pairFun (sub a₂ b (Quot.out e).1, sub a₂ b (Quot.out e).2) := by
            intro e he a₁ a₂ b
            have ⟨hne1, hne2⟩ := h_Tv_no_u e he
            -- Since (.1) ≠ u₀ and (.2) ≠ u₀, the a argument is irrelevant
            have h1 : sub a₁ b (Quot.out e).1 = sub a₂ b (Quot.out e).1 := by
              simp only [sub, dif_neg hne1]
            have h2 : sub a₁ b (Quot.out e).2 = sub a₂ b (Quot.out e).2 := by
              simp only [sub, dif_neg hne2]
            rw [h1, h2]
          -- Define weight factors
          haveI : Nonempty α := by
            by_contra h; rw [not_nonempty_iff] at h
            exact absurd (Measure.eq_zero_of_isEmpty μ) (IsProbabilityMeasure.ne_zero μ)
          set b₀ := Classical.arbitrary α
          set a₀ := Classical.arbitrary α
          set f_raw : α → ℝ := fun a =>
            ∏ e ∈ T_u, (f e).pairFun
              (sub a b₀ (Quot.out e).1, sub a b₀ (Quot.out e).2)
          set g_raw : α → ℝ := fun b =>
            ∏ e ∈ T_v, (f e).pairFun
              (sub a₀ b (Quot.out e).1, sub a₀ b (Quot.out e).2)
          -- The original product factors: ∏_T w_e(sub a b) = f_raw(a) * g_raw(b)
          have h_prod_factor : ∀ a b,
              ∏ e ∈ T, (f e).pairFun (sub a b (Quot.out e).1, sub a b (Quot.out e).2) =
              f_raw a * g_raw b := by
            intro a b
            have h_split : T = T_u ∪ T_v := by
              ext e; simp only [T_u, T_v, Finset.mem_union, Finset.mem_filter]
              constructor
              · intro he; by_cases h : touchesV e = true
                · exact Or.inr ⟨he, h⟩
                · exact Or.inl ⟨he, by simp [h]⟩
              · rintro (⟨he, _⟩ | ⟨he, _⟩) <;> exact he
            rw [h_split, Finset.prod_union h_T_disj]
            congr 1
            · apply Finset.prod_congr rfl; intro e he
              exact h_Tu_indep e he a b b₀
            · apply Finset.prod_congr rfl; intro e he
              exact h_Tv_indep e he a a₀ b
          -- Measurability helpers
          have sub_a_meas : ∀ i, Measurable (fun a => sub a b₀ i) := by
            intro i
            by_cases h1 : i = u₀
            · simp only [sub, dif_pos h1]; exact measurable_id
            · simp only [sub, dif_neg h1]
              by_cases h2 : i = v₀
              · simp only [dif_pos h2]; exact measurable_const
              · simp only [dif_neg h2]; exact measurable_const
          have sub_b_meas : ∀ i, Measurable (fun b => sub a₀ b i) := by
            intro i
            by_cases h1 : i = u₀
            · simp only [sub, dif_pos h1]; exact measurable_const
            · simp only [sub, dif_neg h1]
              by_cases h2 : i = v₀
              · simp only [dif_pos h2]; exact measurable_id
              · simp only [dif_neg h2]; exact measurable_const
          have hf_raw_meas : Measurable f_raw := by
            apply Finset.measurable_prod; intro e _
            exact (f e).measurable_uncurry.comp
              (Measurable.prodMk (sub_a_meas _) (sub_a_meas _))
          have hg_raw_meas : Measurable g_raw := by
            apply Finset.measurable_prod; intro e _
            exact (f e).measurable_uncurry.comp
              (Measurable.prodMk (sub_b_meas _) (sub_b_meas _))
          -- From h_pair_ae, derive: for a.e. pair, f_raw(pair u₀s) ∈ [0,1]
          -- Each T_u edge eval doesn't depend on pair v₀s (by h_Tu_indep),
          -- so from h_pair_ae, the eval with b₀ is in [0,1] for a.e. pair too.
          have h_fraw_ae_pair : ∀ᵐ pair ∂π_pair, f_raw (pair u₀s) ∈ Set.Icc 0 1 := by
            filter_upwards [h_pair_ae] with pair h_all
            -- For each e ∈ T_u, the eval is in [0,1]
            have h_each_Tu : ∀ e ∈ T_u, (f e).pairFun
                (sub (pair u₀s) b₀ (Quot.out e).1,
                 sub (pair u₀s) b₀ (Quot.out e).2) ∈ Set.Icc 0 1 := by
              intro e he
              have heT := (Finset.mem_filter.mp he).1
              -- h_all says the eval with equiv.symm(pair, rest) is in [0,1]
              have h_bound := h_all e heT
              -- Rewrite using h_equiv_sub to get sub form
              simp_rw [h_equiv_sub pair] at h_bound
              -- By h_Tu_indep, changing v₀s to b₀ doesn't matter
              rw [h_Tu_indep e he (pair u₀s) (pair v₀s) b₀] at h_bound
              exact h_bound
            exact ⟨Finset.prod_nonneg (fun e he => (h_each_Tu e he).1),
              Finset.prod_le_one₀ (fun e he => (h_each_Tu e he).1)
                (fun e he => (h_each_Tu e he).2)⟩
          -- Similarly: for a.e. pair, g_raw(pair v₀s) ∈ [0,1]
          have h_graw_ae_pair : ∀ᵐ pair ∂π_pair, g_raw (pair v₀s) ∈ Set.Icc 0 1 := by
            filter_upwards [h_pair_ae] with pair h_all
            have h_each_Tv : ∀ e ∈ T_v, (f e).pairFun
                (sub a₀ (pair v₀s) (Quot.out e).1,
                 sub a₀ (pair v₀s) (Quot.out e).2) ∈ Set.Icc 0 1 := by
              intro e he
              have heT := (Finset.mem_filter.mp he).1
              have h_bound := h_all e heT
              simp_rw [h_equiv_sub pair] at h_bound
              rw [h_Tv_indep e he (pair u₀s) a₀ (pair v₀s)] at h_bound
              exact h_bound
            exact ⟨Finset.prod_nonneg (fun e he => (h_each_Tv e he).1),
              Finset.prod_le_one₀ (fun e he => (h_each_Tv e he).1)
                (fun e he => (h_each_Tv e he).2)⟩
          -- Push a.e. bounds from π_pair to μ via ae_map_iff
          have h_fraw_ae_mu : ∀ᵐ a ∂μ, f_raw a ∈ Set.Icc 0 1 := by
            rw [← (measurePreserving_eval (fun _ : {i // p i} => μ) u₀s).map_eq]
            exact (ae_map_iff (measurable_pi_apply _).aemeasurable
              (show MeasurableSet {x | f_raw x ∈ Set.Icc 0 1} from
                hf_raw_meas measurableSet_Icc)).mpr h_fraw_ae_pair
          have h_graw_ae_mu : ∀ᵐ b ∂μ, g_raw b ∈ Set.Icc 0 1 := by
            rw [← (measurePreserving_eval (fun _ : {i // p i} => μ) v₀s).map_eq]
            exact (ae_map_iff (measurable_pi_apply _).aemeasurable
              (show MeasurableSet {x | g_raw x ∈ Set.Icc 0 1} from
                hg_raw_meas measurableSet_Icc)).mpr h_graw_ae_pair
          -- Rewrite integrand using factored form and apply ae bound
          have h_integral_rw : ∫ pair, F (equiv.symm (pair, rest)) ∂π_pair =
              ∫ pair : {i // p i} → α,
                f_raw (pair u₀s) * g_raw (pair v₀s) *
                (U.pairFun (pair u₀s, pair v₀s) -
                 W.pairFun (pair u₀s, pair v₀s))
              ∂π_pair := by
            apply integral_congr_ae
            filter_upwards with pair
            rw [h_integrand_eq pair, h_prod_factor (pair u₀s) (pair v₀s)]
          rw [h_integral_rw]
          exact abs_weighted_kernel_pi_diff_le_ae U W u₀s v₀s huv_s
            f_raw g_raw hf_raw_meas hg_raw_meas h_fraw_ae_mu h_graw_ae_mu
    _ = kernelCutDistance μ U W := by
        simp

/-- Strengthened counting lemma with weighted prefix product.

For a set of edges `S` (each with distinct endpoints), a prefix product of graphon
evaluations at edges in `R` (disjoint from `S`), the integral of the prefix times
the difference of products is bounded by `|S| * cutNormDiff`.

This is the induction step used to prove the counting lemma. -/
theorem weighted_kernel_product_sub_le
    (U W : Kernel α) (S : Finset (Sym2 V))
    (R : Finset (Sym2 V))
    (f : Sym2 V → Kernel α)
    (hRS : Disjoint R S)
    (hS_edges : ∀ e ∈ S, (Quot.out e).1 ≠ (Quot.out e).2) :
    |∫ x : V → α,
      (∏ e ∈ R, (f e).pairFun (x (Quot.out e).1, x (Quot.out e).2)) *
      (∏ e ∈ S, U.pairFun (x (Quot.out e).1, x (Quot.out e).2) -
       ∏ e ∈ S, W.pairFun (x (Quot.out e).1, x (Quot.out e).2))
    ∂Measure.pi (fun _ => μ)| ≤ S.card * kernelCutDistance μ U W := by
  induction S using Finset.induction generalizing R f with
  | empty =>
    simp
  | @insert e₀ S' he₀ ih =>
    have he₀_edge : (Quot.out e₀).1 ≠ (Quot.out e₀).2 :=
      hS_edges e₀ (Finset.mem_insert_self e₀ S')
    have hS'_edges : ∀ e ∈ S', (Quot.out e).1 ≠ (Quot.out e).2 :=
      fun e he => hS_edges e (Finset.mem_insert_of_mem he)
    -- Key: e₀ ∉ R (from disjointness)
    have he₀R : e₀ ∉ R :=
      Finset.disjoint_right.mp hRS (Finset.mem_insert_self e₀ S')
    -- Set up R' = insert e₀ R, f' = Function.update f e₀ U
    set R' := insert e₀ R with hR'_def
    set f' : Sym2 V → Kernel α := Function.update f e₀ U with hf'_def
    -- Set up f'' for Term 2
    set f'' : Sym2 V → Kernel α := fun e => if e ∈ S' then W else f e with hf''_def
    -- Algebraic identity: the integrand splits as Term1 + Term2
    have h_eq : ∀ x : V → α,
        (∏ e ∈ R, (f e).pairFun (x (Quot.out e).1, x (Quot.out e).2)) *
        (∏ e ∈ insert e₀ S', U.pairFun (x (Quot.out e).1, x (Quot.out e).2) -
         ∏ e ∈ insert e₀ S', W.pairFun (x (Quot.out e).1, x (Quot.out e).2)) =
        ((∏ e ∈ R', (f' e).pairFun (x (Quot.out e).1, x (Quot.out e).2)) *
         (∏ e ∈ S', U.pairFun (x (Quot.out e).1, x (Quot.out e).2) -
          ∏ e ∈ S', W.pairFun (x (Quot.out e).1, x (Quot.out e).2))) +
        ((∏ e ∈ R ∪ S', (f'' e).pairFun (x (Quot.out e).1, x (Quot.out e).2)) *
         (U.pairFun (x (Quot.out e₀).1, x (Quot.out e₀).2) -
          W.pairFun (x (Quot.out e₀).1, x (Quot.out e₀).2))) := by
      intro x
      -- Simplify prod over R' = insert e₀ R with f' (update)
      have hR'_prod : ∏ e ∈ R', (f' e).pairFun (x (Quot.out e).1, x (Quot.out e).2) =
          U.pairFun (x (Quot.out e₀).1, x (Quot.out e₀).2) *
          ∏ e ∈ R, (f e).pairFun (x (Quot.out e).1, x (Quot.out e).2) := by
        rw [hR'_def, Finset.prod_insert he₀R]
        congr 1
        · show (Function.update f e₀ U e₀).pairFun _ = _
          rw [Function.update_self]
        · apply Finset.prod_congr rfl
          intro e he
          show (Function.update f e₀ U e).pairFun _ = _
          have hne : e ≠ e₀ := fun heq => he₀R (heq ▸ he)
          rw [Function.update_of_ne hne]
      -- Simplify prod over R ∪ S' with f''
      have hRS'_prod : ∏ e ∈ R ∪ S', (f'' e).pairFun (x (Quot.out e).1, x (Quot.out e).2) =
          (∏ e ∈ R, (f e).pairFun (x (Quot.out e).1, x (Quot.out e).2)) *
          (∏ e ∈ S', W.pairFun (x (Quot.out e).1, x (Quot.out e).2)) := by
        rw [Finset.prod_union (Finset.disjoint_of_subset_right (Finset.subset_insert _ _) hRS)]
        congr 1
        · apply Finset.prod_congr rfl
          intro e he
          simp only [hf''_def]
          have : e ∉ S' := Finset.disjoint_left.mp
            (Finset.disjoint_of_subset_right (Finset.subset_insert _ _) hRS) he
          simp [this]
        · apply Finset.prod_congr rfl
          intro e he; simp only [hf''_def, if_pos he]
      rw [hR'_prod, hRS'_prod, Finset.prod_insert he₀, Finset.prod_insert he₀]
      ring
    -- Integrability of both terms
    have h_int1 : Integrable (fun x : V → α =>
        (∏ e ∈ R', (f' e).pairFun (x (Quot.out e).1, x (Quot.out e).2)) *
        (∏ e ∈ S', U.pairFun (x (Quot.out e).1, x (Quot.out e).2) -
         ∏ e ∈ S', W.pairFun (x (Quot.out e).1, x (Quot.out e).2)))
        (Measure.pi (fun _ => μ)) :=
      kernel_counting_integrable_term (μ := μ) U W S' R' f'
    have h_int2 : Integrable (fun x : V → α =>
        (∏ e ∈ R ∪ S', (f'' e).pairFun (x (Quot.out e).1, x (Quot.out e).2)) *
        (U.pairFun (x (Quot.out e₀).1, x (Quot.out e₀).2) -
         W.pairFun (x (Quot.out e₀).1, x (Quot.out e₀).2)))
        (Measure.pi (fun _ => μ)) := by
      -- The integrand is bounded a.e. by 2 (product of [0,1] times [-1,1])
      -- on a probability space, so it is integrable.
      have h_aux := kernel_counting_integrable_term (μ := μ) U W {e₀} (R ∪ S') f''
      -- Convert ∏ e ∈ {e₀}, G_e(x) to G_{e₀}(x) via Finset.prod_singleton
      simp only [Finset.prod_singleton] at h_aux
      exact h_aux
    -- Rewrite using the algebraic identity
    simp_rw [h_eq]
    rw [integral_add h_int1 h_int2]
    -- Triangle inequality + bounds
    have hR'S'_disj : Disjoint R' S' := by
      rw [hR'_def]
      exact Finset.disjoint_insert_left.mpr ⟨he₀, hRS.mono_right (Finset.subset_insert _ _)⟩
    have he₀_not_RS' : e₀ ∉ R ∪ S' := by
      rw [Finset.mem_union, not_or]; exact ⟨he₀R, he₀⟩
    calc |∫ x, _ ∂_ + ∫ x, _ ∂_|
        ≤ |∫ x : V → α,
            (∏ e ∈ R', (f' e).pairFun (x (Quot.out e).1, x (Quot.out e).2)) *
            (∏ e ∈ S', U.pairFun (x (Quot.out e).1, x (Quot.out e).2) -
             ∏ e ∈ S', W.pairFun (x (Quot.out e).1, x (Quot.out e).2))
            ∂Measure.pi (fun _ => μ)| +
          |∫ x : V → α,
            (∏ e ∈ R ∪ S', (f'' e).pairFun (x (Quot.out e).1, x (Quot.out e).2)) *
            (U.pairFun (x (Quot.out e₀).1, x (Quot.out e₀).2) -
             W.pairFun (x (Quot.out e₀).1, x (Quot.out e₀).2))
            ∂Measure.pi (fun _ => μ)| := abs_add_le _ _
      _ ≤ S'.card * kernelCutDistance μ U W + kernelCutDistance μ U W :=
          add_le_add (ih R' f' hR'S'_disj hS'_edges)
            (weighted_prod_kernel_diff_le U W (R ∪ S') e₀ he₀_not_RS' f''
              he₀_edge)
      _ = (insert e₀ S').card * kernelCutDistance μ U W := by
          rw [Finset.card_insert_of_notMem he₀]; push_cast; ring


/-- A symmetric kernel whose diagonal realizes the given vertex weight. -/
noncomputable def minVertexKernel (g : α → ℝ) (hg : Measurable g)
    (hb : ∀ x, g x ∈ Icc (0:ℝ) 1) : Kernel α where
  toFun x y := min (g x) (g y)
  measurable_uncurry := (hg.comp measurable_fst).min (hg.comp measurable_snd)
  symmetric x y := min_comm _ _
  nonneg x y := le_min (hb x).1 (hb y).1
  le_one x y := (min_le_left _ _).trans (hb x).2

/-- The counting estimate with arbitrary measurable vertex weights. The
constant is uniform over those weights, including weights that vary with
the kernels in a convergence argument. -/
theorem vertex_weighted_kernel_product_sub_le (U W : Kernel α)
    (S : Finset (Sym2 V))
    (hS : ∀ e ∈ S, (Quot.out e).1 ≠ (Quot.out e).2)
    (g : V → α → ℝ) (hg : ∀ i, Measurable (g i))
    (hb : ∀ i x, g i x ∈ Icc (0:ℝ) 1) :
    |∫ x : V → α, (∏ i, g i (x i))*
      ((∏ e ∈ S, U.pairFun (x (Quot.out e).1,x (Quot.out e).2))-
       ∏ e ∈ S, W.pairFun (x (Quot.out e).1,x (Quot.out e).2))
      ∂Measure.pi (fun _ => μ)| ≤ S.card*kernelCutDistance μ U W := by
  let R : Finset (Sym2 V) := Finset.univ.image Sym2.diag
  let f : Sym2 V → Kernel α := fun e =>
    minVertexKernel (g (Quot.out e).1) (hg _) (hb _)
  have hRS : Disjoint R S := by
    apply Finset.disjoint_left.mpr
    intro e he heS
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
    have hn := hS _ heS
    simp only [Sym2.diag,Sym2.fst_out_mk_self,Sym2.snd_out_mk_self,ne_eq,not_true_eq_false] at hn
  have hp (x : V → α) :
      (∏ e ∈ R, (f e).pairFun (x (Quot.out e).1,x (Quot.out e).2)) =
        ∏ i, g i (x i) := by
    dsimp only [R]
    rw [Finset.prod_image]
    · apply Finset.prod_congr rfl
      intro i _
      simp [f,Sym2.diag,minVertexKernel,Kernel.pairFun]
    · intro i _ j _ hij
      exact Sym2.diag_injective hij
  have h := weighted_kernel_product_sub_le (μ := μ) U W S R f hRS hS
  simpa only [hp] using h

end DensityHS.Graphon
