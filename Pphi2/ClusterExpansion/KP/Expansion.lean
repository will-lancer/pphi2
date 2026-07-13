/-
Mirrored from GibbsMeasure `Ch6Subtree/AppendixProofs/Cluster/Expansion.lean`
@ origin/feat/Ch6InfVolume (030b2fafc18db5c26deb3ffbcf44223304534cfe), 2026-07-13.
Generic Kotecký–Preiss engine (no spin/lattice dependence). Candidate for
standalone-library extraction (planning/keystone-18-campaign.md K18-0);
keep divergence minimal.
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Pphi2.ClusterExpansion.KP.KPBound

/-!
# The cluster expansion identity (FV Proposition 5.3 + §5.6)

For a hard-core polymer system satisfying the Kotecký–Preiss condition with a
finite total tilted activity, the polymer partition function equals the
exponential of the (absolutely convergent) cluster series:
`Ξ(w) = exp (T(w))`.
-/

open scoped BigOperators ENNReal

set_option linter.unusedSectionVars false

namespace PolymerKP

variable {P : Type*}

open Classical in
/-- The hard-core polymer partition function: the sum over finite pairwise
compatible families of polymers of the product of the activities. -/
noncomputable def Xi (bad : P → P → Prop) (w : P → ℝ) : ℝ :=
  ∑' T : Finset P,
    if (T : Set P).Pairwise (fun γ γ' => ¬ bad γ γ') then ∏ γ ∈ T, w γ else 0

/-- The signed cluster series: the sum over all tuple clusters of the Ursell
weight times the activity product (FV (5.6), tuple form). -/
noncomputable def clusterSeries (S : PolymerSystem P) (w : P → ℝ) : ℝ :=
  ∑' c : Σ n : ℕ, (Fin (n + 1) → P),
    (((c.1 + 1).factorial : ℝ))⁻¹ *
      connSum (Finset.univ : Finset (Fin (c.1 + 1))) (S.zetaEdge c.2) *
      ∏ j, w (c.2 j)

/-! ### Summability infrastructure -/

theorem summable_of_enorm_le {ι : Type*} {f : ι → ℝ} {G : ι → ℝ≥0∞}
    (hG : (∑' i, G i) ≠ ∞) (h : ∀ i, ‖f i‖ₑ ≤ G i) : Summable f := by
  have hGtop : ∀ i, G i ≠ ∞ := fun i =>
    ne_top_of_le_ne_top hG (ENNReal.le_tsum i)
  refine Summable.of_norm_bounded (g := fun i => (G i).toReal)
    (ENNReal.summable_toReal hG) fun i => ?_
  have h2 := ENNReal.toReal_mono (hGtop i) (h i)
  rwa [toReal_enorm] at h2

theorem tsum_enorm_le_of_le {ι : Type*} {f : ι → ℝ} {G : ι → ℝ≥0∞}
    (h : ∀ i, ‖f i‖ₑ ≤ G i) : (∑' i, ‖f i‖ₑ) ≤ ∑' i, G i :=
  ENNReal.tsum_le_tsum h

theorem summable_norm_of_enorm_le {ι : Type*} {f : ι → ℝ} {G : ι → ℝ≥0∞}
    (hG : (∑' i, G i) ≠ ∞) (h : ∀ i, ‖f i‖ₑ ≤ G i) :
    Summable fun i => ‖f i‖ := by
  have hGtop : ∀ i, G i ≠ ∞ := fun i =>
    ne_top_of_le_ne_top hG (ENNReal.le_tsum i)
  refine Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => ?_)
    (ENNReal.summable_toReal hG)
  have h2 := ENNReal.toReal_mono (hGtop i) (h i)
  rwa [toReal_enorm] at h2

/-- The sum over finite families of products of nonnegative activities is
controlled by the exponential of the total activity. -/
theorem tsum_finset_prod_le {f : P → ℝ≥0∞} {C : ℝ}
    (hC : 0 ≤ C) (hf : (∑' γ, f γ) ≤ ENNReal.ofReal C) :
    (∑' T : Finset P, ∏ γ ∈ T, f γ) ≤ ENNReal.ofReal (Real.exp C) := by
  classical
  have hftop : ∀ γ, f γ ≠ ∞ := by
    intro γ h
    have hle := le_trans (ENNReal.le_tsum γ) hf
    rw [h, top_le_iff] at hle
    exact ENNReal.ofReal_ne_top hle
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun 𝒯 => ?_
  set U := 𝒯.sup id with hU
  have hsub : 𝒯 ⊆ U.powerset := by
    intro T hT
    rw [Finset.mem_powerset]
    exact Finset.le_sup (f := id) hT
  calc (∑ T ∈ 𝒯, ∏ γ ∈ T, f γ)
      ≤ ∑ T ∈ U.powerset, ∏ γ ∈ T, f γ :=
        Finset.sum_le_sum_of_subset hsub
    _ = ∏ γ ∈ U, (1 + f γ) := (Finset.prod_one_add U).symm
    _ ≤ ∏ γ ∈ U, ENNReal.ofReal (Real.exp ((f γ).toReal)) := by
        refine Finset.prod_le_prod' fun γ _ => ?_
        have hval : f γ = ENNReal.ofReal ((f γ).toReal) :=
          (ENNReal.ofReal_toReal (hftop γ)).symm
        calc 1 + f γ = ENNReal.ofReal (1 + (f γ).toReal) := by
              rw [ENNReal.ofReal_add (by norm_num) ENNReal.toReal_nonneg,
                ENNReal.ofReal_one, ← hval]
          _ ≤ ENNReal.ofReal (Real.exp ((f γ).toReal)) :=
              ENNReal.ofReal_le_ofReal (by
                have := Real.add_one_le_exp ((f γ).toReal)
                linarith)
    _ = ENNReal.ofReal (Real.exp (∑ γ ∈ U, (f γ).toReal)) := by
        rw [Real.exp_sum]
        induction U using Finset.induction_on with
        | empty => simp
        | insert a s ha ih =>
            rw [Finset.prod_insert ha, Finset.prod_insert ha, ih,
              ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
    _ ≤ ENNReal.ofReal (Real.exp C) := by
        refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
        calc (∑ γ ∈ U, (f γ).toReal)
            = ((∑ γ ∈ U, f γ).toReal) := by
              rw [ENNReal.toReal_sum fun γ _ => hftop γ]
          _ ≤ ((∑' γ, f γ)).toReal := by
              refine ENNReal.toReal_mono (by
                intro h
                rw [h] at hf
                exact absurd (top_le_iff.1 hf) (by simp)) ?_
              exact ENNReal.sum_le_tsum U
          _ ≤ (ENNReal.ofReal C).toReal := by
              refine ENNReal.toReal_mono ENNReal.ofReal_ne_top hf
          _ = C := ENNReal.toReal_ofReal hC

/-! ### Real blockwise factorization -/

open Classical in
/-- Blockwise factorization of a real tuple sum along a partition of the
coordinates (the signed mirror of `tsum_prod_blocks`). -/
theorem tsum_prod_blocks_real {Q : Type*} {n : ℕ}
    {Pa : Finset (Finset (Fin n))}
    (hPa : Pa ∈ partitionsOn (Finset.univ : Finset (Fin n)))
    (H : (W : Finset (Fin n)) → (Fin W.card → Q) → ℝ)
    (hH : ∀ W ∈ Pa, Summable fun δ : Fin W.card → Q => ‖H W δ‖) :
    ∑' γ : Fin n → Q, ∏ W ∈ Pa, H W (γ ∘ (W.orderEmbOfFin rfl))
      = ∏ W ∈ Pa, ∑' δ : Fin W.card → Q, H W δ := by
  classical
  set k := Pa.card with hk
  set eP : {W // W ∈ Pa} ≃ Fin k := Pa.equivFin with heP
  set f : Fin n → Fin k := fun i => eP (blockOf hPa i) with hf
  have hfiber : ∀ (j : Fin k) (i : Fin n), f i = j ↔ i ∈ (eP.symm j).1 := by
    intro j i
    constructor
    · intro h
      have hbl : blockOf hPa i = eP.symm j := by
        rw [← h]
        exact (Equiv.symm_apply_apply eP _).symm
      rw [← hbl]
      exact mem_blockOf hPa i
    · intro h
      have hbl : blockOf hPa i = eP.symm j := by
        refine Subtype.ext ?_
        exact blockOf_eq hPa (eP.symm j).2 h
      show eP (blockOf hPa i) = j
      rw [hbl, Equiv.apply_symm_apply]
  set tEquiv : ∀ j : Fin k, Fin ((eP.symm j).1.card) ≃ {i : Fin n // f i = j} :=
    fun j => ((eP.symm j).1.orderIsoOfFin rfl).toEquiv.trans
      (Equiv.subtypeEquivRight fun i => (hfiber j i).symm) with htE
  have hprodconv : ∀ (g : Finset (Fin n) → ℝ),
      (∏ W ∈ Pa, g W) = ∏ j : Fin k, g (eP.symm j).1 := by
    intro g
    rw [← Finset.prod_attach Pa g]
    exact (Equiv.prod_comp eP.symm (fun w => g w.1)).symm
  have hsum : ∀ j : Fin k, Summable fun y : {i : Fin n // f i = j} → Q =>
      ‖H (eP.symm j).1 (fun u => y (tEquiv j u))‖ := by
    intro j
    have h1 := hH (eP.symm j).1 (eP.symm j).2
    have h2 : (fun y : {i : Fin n // f i = j} → Q =>
        ‖H (eP.symm j).1 (fun u => y (tEquiv j u))‖)
        = (fun δ : Fin ((eP.symm j).1.card) → Q => ‖H (eP.symm j).1 δ‖) ∘
          (((tEquiv j).arrowCongr (Equiv.refl Q)).symm) := by
      funext y
      simp only [Function.comp_apply]
      congr 1
    rw [h2]
    exact (((tEquiv j).arrowCongr (Equiv.refl Q)).symm.summable_iff).2 h1
  calc ∑' γ : Fin n → Q, ∏ W ∈ Pa, H W (γ ∘ (W.orderEmbOfFin rfl))
      = ∑' γ : Fin n → Q,
          ∏ j : Fin k, H (eP.symm j).1
            (γ ∘ ((eP.symm j).1.orderEmbOfFin rfl)) := by
        refine tsum_congr fun γ => ?_
        exact hprodconv fun W => H W (γ ∘ (W.orderEmbOfFin rfl))
    _ = ∑' x : ∀ j : Fin k, ({i : Fin n // f i = j} → Q),
          ∏ j : Fin k, H (eP.symm j).1
            (fun u => x j (tEquiv j u)) := by
        rw [← Equiv.tsum_eq (fiberPiEquiv f Q)]
        refine tsum_congr fun γ => ?_
        refine Finset.prod_congr rfl fun j _ => ?_
        congr 1
    _ = ∏ j : Fin k, ∑' y : {i : Fin n // f i = j} → Q,
          H (eP.symm j).1 (fun u => y (tEquiv j u)) := by
        exact tsum_pi_prod
          (A := fun j : Fin k => {i : Fin n // f i = j} → Q)
          (g := fun j y => H (eP.symm j).1 fun u => y (tEquiv j u)) hsum
    _ = ∏ j : Fin k, ∑' δ : Fin ((eP.symm j).1.card) → Q,
          H (eP.symm j).1 δ := by
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [← Equiv.tsum_eq ((tEquiv j).arrowCongr (Equiv.refl Q))
          (fun y => H (eP.symm j).1 fun u => y (tEquiv j u))]
        refine tsum_congr fun δ => ?_
        congr 1
        funext u
        simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply,
          id_eq, Equiv.symm_apply_apply]
    _ = ∏ W ∈ Pa, ∑' δ : Fin W.card → Q, H W δ :=
        (hprodconv fun W => ∑' δ : Fin W.card → Q, H W δ).symm

private theorem tsum_eq_tsum_fiber {β : Type*} {c : β → ℕ} {g : β → ℝ}
    (hg : Summable g) :
    (∑' b : β, g b) = ∑' n : ℕ, ∑' Sf : {b : β // c b = n}, g Sf.1 := by
  rw [← Equiv.tsum_eq (Equiv.sigmaFiberEquiv c) g]
  have hs : Summable fun p : Σ n : ℕ, {b : β // c b = n} =>
      g ((Equiv.sigmaFiberEquiv c) p) :=
    ((Equiv.sigmaFiberEquiv c).summable_iff).2 hg
  exact hs.tsum_sigma

/-! ### The interaction product -/

namespace PolymerSystem

variable (S : PolymerSystem P)

open Classical in
/-- The pairwise interaction product of a tuple (FV (5.4)). -/
noncomputable def deltaProd {n : ℕ} (γ : Fin n → P) : ℝ :=
  ∏ e ∈ pairsOn (Finset.univ : Finset (Fin n)), (1 + S.zetaEdge γ e)

open Classical in
theorem deltaProd_eq_indicator {n : ℕ} (γ : Fin n → P) :
    S.deltaProd γ
      = if ∀ i j : Fin n, i ≠ j → ¬ S.bad (γ i) (γ j) then 1 else 0 := by
  by_cases h : ∀ i j : Fin n, i ≠ j → ¬ S.bad (γ i) (γ j)
  · rw [if_pos h, deltaProd]
    rw [Finset.prod_congr rfl (g := fun _ => (1 : ℝ)) ?_, Finset.prod_const_one]
    intro e he
    induction e with
    | _ i j =>
        have hij := mk_mem_pairsOn_iff.1 he
        rw [S.zetaEdge_mk, if_neg (h i j hij.2), add_zero]
  · rw [if_neg h, deltaProd]
    push_neg at h
    obtain ⟨i, j, hij, hbad⟩ := h
    refine Finset.prod_eq_zero (i := s(i, j))
      (mk_mem_pairsOn_iff.2 ⟨⟨Finset.mem_univ i, Finset.mem_univ j⟩, hij⟩) ?_
    rw [S.zetaEdge_mk, if_pos hbad]
    ring

theorem abs_deltaProd_le_one {n : ℕ} (γ : Fin n → P) :
    |S.deltaProd γ| ≤ 1 := by
  rw [S.deltaProd_eq_indicator γ]
  split_ifs <;> simp

theorem deltaProd_eq_zero_of_not_injective {n : ℕ} {γ : Fin n → P}
    (h : ¬ Function.Injective γ) : S.deltaProd γ = 0 := by
  rw [S.deltaProd_eq_indicator γ, if_neg]
  intro hall
  refine h fun i j hij => ?_
  by_contra hne
  exact hall i j hne (hij ▸ S.bad_refl (γ i))

theorem deltaProd_comp_perm {n : ℕ} (γ : Fin n → P)
    (σ : Equiv.Perm (Fin n)) : S.deltaProd (γ ∘ σ) = S.deltaProd γ := by
  classical
  rw [S.deltaProd_eq_indicator, S.deltaProd_eq_indicator]
  have hiff : (∀ i j : Fin n, i ≠ j → ¬ S.bad ((γ ∘ σ) i) ((γ ∘ σ) j))
      ↔ (∀ i j : Fin n, i ≠ j → ¬ S.bad (γ i) (γ j)) := by
    constructor
    · intro h i j hij
      have := h (σ.symm i) (σ.symm j)
        (fun hc => hij
          (by rw [← σ.apply_symm_apply i, ← σ.apply_symm_apply j, hc]))
      simpa using this
    · intro h i j hij
      exact h (σ i) (σ j) fun hc => hij (σ.injective hc)
  rw [if_congr hiff rfl rfl]

/-- The graph expansion of the interaction product (the `+1−1` trick). -/
theorem deltaProd_eq_graphSum {n : ℕ} (γ : Fin n → P) :
    S.deltaProd γ = graphSum (Finset.univ : Finset (Fin n)) (S.zetaEdge γ) := by
  rw [deltaProd, graphSum]
  exact Finset.prod_one_add _

open Classical in
/-- FV (5.4): the polymer partition function as a sum over ordered tuples. -/
theorem Xi_eq_tuple_series [LinearOrder P] (w : P → ℝ)
    (hw : ∀ γ : P, ‖w γ‖ₑ ≤ S.W γ) (htot : (∑' γ : P, S.W γ) ≠ ∞) :
    Xi S.bad w
      = ∑' n : ℕ, ((n.factorial : ℝ))⁻¹ *
          ∑' γ : Fin n → P, S.deltaProd γ * ∏ j, w (γ j) := by
  classical
  set g : Finset P → ℝ := fun T =>
    if (T : Set P).Pairwise (fun γ γ' => ¬ S.bad γ γ') then
      ∏ γ ∈ T, w γ else 0 with hg
  have hg_enorm : ∀ T : Finset P, ‖g T‖ₑ ≤ ∏ γ ∈ T, S.W γ := by
    intro T
    rw [hg]
    by_cases h : (T : Set P).Pairwise fun γ γ' => ¬ S.bad γ γ'
    · simp only [if_pos h]
      rw [enorm_finset_prod]
      exact Finset.prod_le_prod' fun γ _ => hw γ
    · simp only [if_neg h]
      simp
  have hG_ne_top : (∑' T : Finset P, ∏ γ ∈ T, S.W γ) ≠ ∞ := by
    refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (tsum_finset_prod_le (f := fun γ => S.W γ)
        (C := (∑' γ : P, S.W γ).toReal) ENNReal.toReal_nonneg ?_)
    rw [ENNReal.ofReal_toReal htot]
  have hg_summable : Summable g :=
    summable_of_enorm_le hG_ne_top hg_enorm
  -- the per-`n` reindexing through the canonical enumeration
  have hn : ∀ n : ℕ,
      (∑' γ : Fin n → P, S.deltaProd γ * ∏ j, w (γ j))
        = (n.factorial : ℝ) *
            ∑' Sf : {T : Finset P // T.card = n}, g Sf.1 := by
    intro n
    have hmaj : ∀ γ : Fin n → P,
        ‖S.deltaProd γ * ∏ j, w (γ j)‖ₑ ≤ ∏ j, S.W (γ j) := by
      intro γ
      rw [enorm_mul]
      calc ‖S.deltaProd γ‖ₑ * ‖∏ j, w (γ j)‖ₑ
          ≤ 1 * ∏ j, S.W (γ j) := by
            refine mul_le_mul' ?_ ?_
            · rw [Real.enorm_eq_ofReal_abs]
              calc ENNReal.ofReal |S.deltaProd γ|
                  ≤ ENNReal.ofReal 1 :=
                    ENNReal.ofReal_le_ofReal (S.abs_deltaProd_le_one γ)
                _ = 1 := ENNReal.ofReal_one
            · rw [enorm_finset_prod]
              exact Finset.prod_le_prod' fun j _ => hw (γ j)
        _ = ∏ j, S.W (γ j) := one_mul _
    have hsummable : Summable fun γ : Fin n → P =>
        S.deltaProd γ * ∏ j, w (γ j) := by
      refine summable_of_enorm_le
        (G := fun γ : Fin n → P => ∏ j, S.W (γ j)) ?_ hmaj
      rw [← tsum_pow_eq_tsum_pi_ennreal (fun γ => S.W γ) n]
      exact ENNReal.pow_ne_top htot
    rw [tsum_eq_factorial_mul_tsum_finset
      (F := fun γ : Fin n → P => S.deltaProd γ * ∏ j, w (γ j)) hsummable
      (fun γ hγ => by
        dsimp only
        rw [S.deltaProd_eq_zero_of_not_injective hγ, zero_mul])
      (fun σ γ => by
        dsimp only
        rw [S.deltaProd_comp_perm γ σ]
        congr 1
        exact Equiv.prod_comp σ fun j => w (γ j))]
    congr 1
    refine tsum_congr fun Sf => ?_
    set enum : Fin n → P := fun i => ((Sf.1.orderIsoOfFin Sf.2) i : P)
      with henum
    have himage : Finset.univ.image enum = Sf.1 := by
      rw [← Finset.image_orderEmbOfFin_univ Sf.1 Sf.2]
      refine Finset.image_congr fun i _ => ?_
      rw [henum]
      exact Finset.coe_orderIsoOfFin_apply Sf.1 Sf.2 i
    have hinj : Function.Injective enum := by
      intro i j hij
      exact (Sf.1.orderIsoOfFin Sf.2).injective (Subtype.ext hij)
    have hmem : ∀ i : Fin n, enum i ∈ Sf.1 := by
      intro i
      rw [← himage]
      exact Finset.mem_image_of_mem enum (Finset.mem_univ i)
    have hdelta : S.deltaProd enum
        = if (Sf.1 : Set P).Pairwise (fun γ γ' => ¬ S.bad γ γ')
            then (1 : ℝ) else 0 := by
      rw [S.deltaProd_eq_indicator]
      refine if_congr ⟨fun h => ?_, fun h => ?_⟩ rfl rfl
      · intro x hx y hy hxy
        rw [Finset.mem_coe, ← himage] at hx hy
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hx
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hy
        exact h i j fun hc => hxy (by rw [hc])
      · intro i j hij
        exact h (Finset.mem_coe.2 (hmem i)) (Finset.mem_coe.2 (hmem j))
          fun hc => hij (hinj hc)
    have hprod : (∏ j, w (enum j)) = ∏ γ ∈ Sf.1, w γ := by
      rw [← himage, Finset.prod_image fun i _ j _ h => hinj h]
    rw [hdelta, hprod, hg]
    by_cases h : (Sf.1 : Set P).Pairwise fun γ γ' => ¬ S.bad γ γ'
    · simp only [if_pos h, one_mul]
    · simp only [if_neg h, zero_mul]
  -- regroup the finite-set sum by cardinality
  have hXi : Xi S.bad w = ∑' T : Finset P, g T := by
    -- Divergence from upstream: with the trimmed import set, `rw [Xi]` closes
    -- the goal directly (the `set`-abstraction of `g` makes it `rfl`), so the
    -- upstream continuation `refine tsum_congr …; rw [hg]; congr` is dead code.
    rw [Xi]
  rw [hXi, tsum_eq_tsum_fiber (c := Finset.card) hg_summable]
  refine tsum_congr fun n => ?_
  rw [hn n, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast n.factorial_pos.ne'),
    one_mul]

/-! ### Finiteness of the per-size cluster sums -/

theorem tsum_clusterF_ne_top (hKP : S.KPCondition) {eps : ℝ≥0∞}
    (heps : eps ≠ ∞)
    (htot : (∑' γ : P, S.W γ * ENNReal.ofReal (Real.exp (S.a γ))) ≤ eps) :
    ∀ m : ℕ, (∑' δ : Fin m → P, S.clusterF δ) ≠ ∞ := by
  intro m
  match m with
  | 0 =>
      have h1 : ∀ δ : Fin 0 → P, S.clusterF δ = 1 := by
        intro δ
        rw [PolymerSystem.clusterF]
        have : (Finset.univ : Finset (Fin 0)) = ∅ := rfl
        rw [this, connSum_empty]
        simp
      rw [tsum_congr h1]
      have hone : (∑' _ : Fin 0 → P, (1 : ℝ≥0∞)) = 1 := by
        rw [tsum_eq_single (fun i => i.elim0)]
        intro b' hb'
        exact absurd (funext fun i => i.elim0) hb'
      rw [hone]
      exact ENNReal.one_ne_top
  | m' + 1 =>
      have htotal := S.kp_total_bound hKP htot
      have hterm : (((m' + 1).factorial : ℝ≥0∞))⁻¹ *
          (∑' ρ : Fin (m' + 1) → P, S.clusterF ρ) ≤ eps := by
        refine le_trans ?_ htotal
        exact ENNReal.le_tsum m'
      intro hcon
      rw [hcon, ENNReal.mul_top (by
        simp only [ne_eq, ENNReal.inv_eq_zero]
        exact ENNReal.natCast_ne_top _)] at hterm
      exact heps (top_le_iff.1 hterm)

/-! ### The per-`n` partition identity (FV (5.5)–(5.7)) -/

open Classical in
/-- The signed per-block value. -/
noncomputable def blockT (w : P → ℝ) (m : ℕ) : ℝ :=
  ∑' δ : Fin m → P,
    connSum (Finset.univ : Finset (Fin m)) (S.zetaEdge δ) * ∏ j, w (δ j)

theorem enorm_blockT_summand_le (w : P → ℝ) (hw : ∀ γ : P, ‖w γ‖ₑ ≤ S.W γ)
    {m : ℕ} (δ : Fin m → P) :
    ‖connSum (Finset.univ : Finset (Fin m)) (S.zetaEdge δ) * ∏ j, w (δ j)‖ₑ
      ≤ S.clusterF δ := by
  rw [enorm_mul, PolymerSystem.clusterF]
  refine mul_le_mul' le_rfl ?_
  rw [enorm_finset_prod]
  exact Finset.prod_le_prod' fun j _ => hw (δ j)

theorem summable_blockT (w : P → ℝ) (hw : ∀ γ : P, ‖w γ‖ₑ ≤ S.W γ)
    (hKP : S.KPCondition) {eps : ℝ≥0∞} (heps : eps ≠ ∞)
    (htot : (∑' γ : P, S.W γ * ENNReal.ofReal (Real.exp (S.a γ))) ≤ eps)
    (m : ℕ) :
    Summable fun δ : Fin m → P =>
      connSum (Finset.univ : Finset (Fin m)) (S.zetaEdge δ) * ∏ j, w (δ j) :=
  summable_of_enorm_le (S.tsum_clusterF_ne_top hKP heps htot m)
    (fun δ => S.enorm_blockT_summand_le w hw δ)

open Classical in
/-- FV (5.5)–(5.7): the tuple term factorizes over coordinate partitions into
per-block cluster values. -/
theorem tuple_term_eq_partitions (w : P → ℝ)
    (hw : ∀ γ : P, ‖w γ‖ₑ ≤ S.W γ) (hKP : S.KPCondition) {eps : ℝ≥0∞}
    (heps : eps ≠ ∞)
    (htot : (∑' γ : P, S.W γ * ENNReal.ofReal (Real.exp (S.a γ))) ≤ eps)
    (n : ℕ) :
    (∑' γ : Fin n → P, S.deltaProd γ * ∏ j, w (γ j))
      = ∑ Pa ∈ partitionsOn (Finset.univ : Finset (Fin n)),
          ∏ W ∈ Pa, S.blockT w W.card := by
  classical
  -- blockified form of the per-partition summand
  have hblockify : ∀ (Pa : Finset (Finset (Fin n))),
      Pa ∈ partitionsOn (Finset.univ : Finset (Fin n)) →
      ∀ γ : Fin n → P,
      (∏ W ∈ Pa, connSum W (S.zetaEdge γ)) * ∏ j, w (γ j)
        = ∏ W ∈ Pa,
            (connSum (Finset.univ : Finset (Fin W.card))
              (S.zetaEdge (γ ∘ (W.orderEmbOfFin rfl))) *
              ∏ j, w ((γ ∘ (W.orderEmbOfFin rfl)) j)) := by
    intro Pa hPa γ
    rw [prod_partition hPa (fun j => w (γ j)), ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun W _ => ?_
    congr 1
    · have hW : W = (Finset.univ : Finset (Fin W.card)).map
          (W.orderEmbOfFin rfl).toEmbedding :=
        (Finset.map_orderEmbOfFin_univ W rfl).symm
      conv_lhs => rw [hW]
      rw [S.connSum_zeta_comp_emb γ (W.orderEmbOfFin rfl).toEmbedding]
      rfl
    · have hW : W = (Finset.univ : Finset (Fin W.card)).map
          (W.orderEmbOfFin rfl).toEmbedding :=
        (Finset.map_orderEmbOfFin_univ W rfl).symm
      conv_lhs => rw [hW]
      rw [Finset.prod_map]
      rfl
  -- expand the interaction product into graphs and components
  calc (∑' γ : Fin n → P, S.deltaProd γ * ∏ j, w (γ j))
      = ∑' γ : Fin n → P,
          ∑ Pa ∈ partitionsOn (Finset.univ : Finset (Fin n)),
            (∏ W ∈ Pa, connSum W (S.zetaEdge γ)) * ∏ j, w (γ j) := by
        refine tsum_congr fun γ => ?_
        rw [S.deltaProd_eq_graphSum, graphSum_eq_sum_partitions,
          Finset.sum_mul]
    _ = ∑ Pa ∈ partitionsOn (Finset.univ : Finset (Fin n)),
          ∑' γ : Fin n → P,
            (∏ W ∈ Pa, connSum W (S.zetaEdge γ)) * ∏ j, w (γ j) := by
        refine Summable.tsum_finsetSum fun Pa hPa => ?_
        -- summability from the ENNReal blockwise factorization
        refine summable_of_enorm_le
          (G := fun γ : Fin n → P =>
            ∏ W ∈ Pa, S.clusterF (γ ∘ (W.orderEmbOfFin rfl))) ?_ ?_
        · rw [tsum_prod_blocks hPa fun W δ => S.clusterF δ]
          exact (ENNReal.prod_lt_top fun W _ =>
            (S.tsum_clusterF_ne_top hKP heps htot W.card).lt_top).ne
        · intro γ
          rw [hblockify Pa hPa γ]
          rw [enorm_finset_prod]
          refine Finset.prod_le_prod' fun W _ => ?_
          exact S.enorm_blockT_summand_le w hw _
    _ = ∑ Pa ∈ partitionsOn (Finset.univ : Finset (Fin n)),
          ∏ W ∈ Pa, S.blockT w W.card := by
        refine Finset.sum_congr rfl fun Pa hPa => ?_
        rw [tsum_congr (hblockify Pa hPa)]
        exact tsum_prod_blocks_real hPa
          (H := fun W δ =>
            connSum (Finset.univ : Finset (Fin W.card)) (S.zetaEdge δ) *
              ∏ j, w (δ j))
          (fun W _ => (S.summable_blockT w hw hKP heps htot W.card).norm)

end PolymerSystem

/-! ### Regrouping by block sizes -/

open Classical in
/-- Grouping the surjective-fiber sum by the vector of fiber sizes. -/
private theorem sum_filter_pi_prod_fiber_card (n k : ℕ) (v : ℕ → ℝ) :
    (∑ f ∈ (Finset.univ : Finset (Fin n → Fin k)).filter
        (fun f => ∀ j, (Finset.univ.filter (fun i => f i = j)).Nonempty),
      ∏ j : Fin k, v ((Finset.univ.filter (fun i => f i = j)).card))
      = ∑ mvec ∈ (Finset.piAntidiag (Finset.univ : Finset (Fin k)) n).filter
          (fun m => ∀ j, 1 ≤ m j),
          (((Finset.univ : Finset (Fin n → Fin k)).filter
            (fun f => ∀ j, (Finset.univ.filter
              (fun i => f i = j)).card = mvec j)).card : ℝ)
            * ∏ j, v (mvec j) := by
  classical
  have hmaps : ∀ f ∈ (Finset.univ : Finset (Fin n → Fin k)).filter
      (fun f => ∀ j, (Finset.univ.filter (fun i => f i = j)).Nonempty),
      (fun j => (Finset.univ.filter (fun i => f i = j)).card)
        ∈ (Finset.piAntidiag (Finset.univ : Finset (Fin k)) n).filter
          (fun m => ∀ j, 1 ≤ m j) := by
    intro f hf
    rw [Finset.mem_filter] at hf ⊢
    constructor
    · rw [Finset.mem_piAntidiag]
      constructor
      · have hcards := Finset.card_eq_sum_card_fiberwise
          (s := (Finset.univ : Finset (Fin n))) (t := Finset.univ)
          (f := f) (fun i _ => Finset.mem_univ (f i))
        rw [Finset.card_univ, Fintype.card_fin] at hcards
        exact hcards.symm
      · intro j _
        exact Finset.mem_univ j
    · intro j
      exact Finset.card_pos.2 (hf.2 j)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun f => ∏ j : Fin k, v ((Finset.univ.filter (fun i => f i = j)).card))]
  refine Finset.sum_congr rfl fun mvec hm => ?_
  rw [Finset.mem_filter] at hm
  have hfibereq : ((Finset.univ : Finset (Fin n → Fin k)).filter
      (fun f => ∀ j, (Finset.univ.filter (fun i => f i = j)).Nonempty)).filter
      (fun f => (fun j => (Finset.univ.filter (fun i => f i = j)).card) = mvec)
      = (Finset.univ : Finset (Fin n → Fin k)).filter
        (fun f => ∀ j, (Finset.univ.filter
          (fun i => f i = j)).card = mvec j) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, heq⟩
      intro j
      exact congrFun heq j
    · intro h
      refine ⟨fun j => ?_, funext h⟩
      rw [← Finset.card_pos, h j]
      exact hm.2 j
  rw [hfibereq]
  have hconst : ∀ f ∈ (Finset.univ : Finset (Fin n → Fin k)).filter
      (fun f => ∀ j, (Finset.univ.filter
        (fun i => f i = j)).card = mvec j),
      (∏ j : Fin k, v ((Finset.univ.filter (fun i => f i = j)).card))
        = ∏ j, v (mvec j) := by
    intro f hf
    rw [Finset.mem_filter] at hf
    exact Finset.prod_congr rfl fun j _ => by rw [hf.2 j]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]

/-- Casting the multinomial count. -/
private theorem inv_factorial_mul_card_eq {n k : ℕ} {mvec : Fin k → ℕ}
    (hsum : (∑ j, mvec j) = n) :
    ((n.factorial : ℝ))⁻¹ *
      (((Finset.univ : Finset (Fin n → Fin k)).filter
        (fun f => ∀ j, (Finset.univ.filter
          (fun i => f i = j)).card = mvec j)).card : ℝ)
      = ∏ j, (((mvec j).factorial : ℝ))⁻¹ := by
  classical
  have hnat := card_fiber_sizes_mul_factorials (m := mvec) hsum
  have hcast : (((Finset.univ : Finset (Fin n → Fin k)).filter
      (fun f => ∀ j, (Finset.univ.filter
        (fun i => f i = j)).card = mvec j)).card : ℝ) *
      ∏ j, ((mvec j).factorial : ℝ) = (n.factorial : ℝ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hnat
  have hprodpos : (0 : ℝ) < ∏ j, ((mvec j).factorial : ℝ) :=
    Finset.prod_pos fun j _ => by exact_mod_cast (mvec j).factorial_pos
  have hcardposNat : 0 < ((Finset.univ : Finset (Fin n → Fin k)).filter
      (fun f => ∀ j, (Finset.univ.filter
        (fun i => f i = j)).card = mvec j)).card := by
    rcases Nat.eq_zero_or_pos ((Finset.univ : Finset (Fin n → Fin k)).filter
      (fun f => ∀ j, (Finset.univ.filter
        (fun i => f i = j)).card = mvec j)).card with h0 | h
    · exfalso
      rw [h0, zero_mul] at hnat
      exact (Nat.factorial_pos n).ne' hnat.symm
    · exact h
  have hcardpos : (0 : ℝ) < (((Finset.univ : Finset (Fin n → Fin k)).filter
      (fun f => ∀ j, (Finset.univ.filter
        (fun i => f i = j)).card = mvec j)).card : ℝ) := by
    exact_mod_cast hcardposNat
  rw [← hcast, mul_inv, Finset.prod_inv_distrib]
  field_simp

/-! ### The shift reindexing between compositions and free size vectors -/

private def shiftEquiv (k n : ℕ) :
    {mv : Fin k → ℕ // (∑ j, (mv j + 1)) = n}
      ≃ {m : Fin k → ℕ //
          m ∈ (Finset.piAntidiag (Finset.univ : Finset (Fin k)) n).filter
            (fun m => ∀ j, 1 ≤ m j)} where
  toFun mv := ⟨fun j => mv.1 j + 1, by
    rw [Finset.mem_filter, Finset.mem_piAntidiag]
    exact ⟨⟨mv.2, fun j _ => Finset.mem_univ j⟩,
      fun j => Nat.le_add_left 1 _⟩⟩
  invFun m := ⟨fun j => m.1 j - 1, by
    have hm := m.2
    rw [Finset.mem_filter, Finset.mem_piAntidiag] at hm
    have hsum := hm.1.1
    have hpos := hm.2
    have heq : (∑ j, ((fun j => m.1 j - 1) j + 1)) = ∑ j, m.1 j := by
      refine Finset.sum_congr rfl fun j _ => ?_
      have := hpos j
      dsimp only
      omega
    rw [heq, hsum]⟩
  left_inv mv := by
    refine Subtype.ext (funext fun j => ?_)
    simp
  right_inv m := by
    have hm := m.2
    rw [Finset.mem_filter] at hm
    refine Subtype.ext (funext fun j => ?_)
    have := hm.2 j
    simp only
    omega

private theorem tsum_eq_tsum_fiber_ennreal {β : Type*} {c : β → ℕ}
    (g : β → ℝ≥0∞) :
    (∑' b : β, g b) = ∑' n : ℕ, ∑' Sf : {b : β // c b = n}, g Sf.1 := by
  rw [← Equiv.tsum_eq (Equiv.sigmaFiberEquiv c) g, ENNReal.tsum_sigma']
  rfl

private theorem tsum_shift_eq_ennreal {k : ℕ} (τ : ℕ → ℝ≥0∞) :
    (∑' mv : Fin k → ℕ, ∏ j, τ (mv j + 1))
      = ∑' n : ℕ,
          ∑ mvec ∈ (Finset.piAntidiag
            (Finset.univ : Finset (Fin k)) n).filter (fun m => ∀ j, 1 ≤ m j),
            ∏ j, τ (mvec j) := by
  rw [tsum_eq_tsum_fiber_ennreal (c := fun mv : Fin k → ℕ => ∑ j, (mv j + 1))]
  refine tsum_congr fun n => ?_
  rw [← Finset.tsum_subtype
    ((Finset.piAntidiag (Finset.univ : Finset (Fin k)) n).filter
      (fun m => ∀ j, 1 ≤ m j)) (fun mvec => ∏ j, τ (mvec j)),
    ← Equiv.tsum_eq (shiftEquiv k n)
      (fun m : {m : Fin k → ℕ //
        m ∈ (Finset.piAntidiag (Finset.univ : Finset (Fin k)) n).filter
          (fun m => ∀ j, 1 ≤ m j)} => ∏ j, τ (m.1 j))]
  rfl

private theorem tsum_shift_eq_real {k : ℕ} {t : ℕ → ℝ}
    (hsum : Summable fun mv : Fin k → ℕ => ∏ j, t (mv j + 1)) :
    (∑' mv : Fin k → ℕ, ∏ j, t (mv j + 1))
      = ∑' n : ℕ,
          ∑ mvec ∈ (Finset.piAntidiag
            (Finset.univ : Finset (Fin k)) n).filter (fun m => ∀ j, 1 ≤ m j),
            ∏ j, t (mvec j) := by
  rw [tsum_eq_tsum_fiber (c := fun mv : Fin k → ℕ => ∑ j, (mv j + 1)) hsum]
  refine tsum_congr fun n => ?_
  rw [← Finset.tsum_subtype
    ((Finset.piAntidiag (Finset.univ : Finset (Fin k)) n).filter
      (fun m => ∀ j, 1 ≤ m j)) (fun mvec => ∏ j, t (mvec j)),
    ← Equiv.tsum_eq (shiftEquiv k n)
      (fun m : {m : Fin k → ℕ //
        m ∈ (Finset.piAntidiag (Finset.univ : Finset (Fin k)) n).filter
          (fun m => ∀ j, 1 ≤ m j)} => ∏ j, t (m.1 j))]
  rfl

namespace PolymerSystem

variable (S : PolymerSystem P)

open Classical in
/-- FV (5.7)–(5.8), one fixed size: the tuple term regrouped over the number
of blocks and their sizes. -/
theorem tuple_term_regrouped [LinearOrder P] (w : P → ℝ)
    (hw : ∀ γ : P, ‖w γ‖ₑ ≤ S.W γ) (hKP : S.KPCondition) {eps : ℝ≥0∞}
    (heps : eps ≠ ∞)
    (htot : (∑' γ : P, S.W γ * ENNReal.ofReal (Real.exp (S.a γ))) ≤ eps)
    (n : ℕ) :
    ((n.factorial : ℝ))⁻¹ *
        (∑' γ : Fin n → P, S.deltaProd γ * ∏ j, w (γ j))
      = ∑ k ∈ Finset.range (n + 1), ((k.factorial : ℝ))⁻¹ *
          ∑ mvec ∈ (Finset.piAntidiag
            (Finset.univ : Finset (Fin k)) n).filter (fun m => ∀ j, 1 ≤ m j),
            ∏ j, (((mvec j).factorial : ℝ))⁻¹ * S.blockT w (mvec j) := by
  classical
  rw [S.tuple_term_eq_partitions w hw hKP heps htot n,
    ← Finset.sum_fiberwise_of_maps_to
      (g := fun Pa => Pa.card)
      (fun Pa hPa => Finset.mem_range.2
        (Nat.lt_succ_of_le (partition_card_le hPa)))
      (fun Pa => ∏ W ∈ Pa, S.blockT w W.card),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  -- C1-eq
  have hC1 := factorial_mul_sum_partitions_card (ι := Fin n) (M := ℝ)
    (u := fun W => S.blockT w W.card) k
  have hkfac : ((k.factorial : ℝ)) ≠ 0 := by
    exact_mod_cast k.factorial_pos.ne'
  have hPa_eq : (∑ Pa ∈ (partitionsOn (Finset.univ : Finset (Fin n))).filter
      (fun Pa => Pa.card = k), ∏ W ∈ Pa, S.blockT w W.card)
      = ((k.factorial : ℝ))⁻¹ *
          ∑ f ∈ (Finset.univ : Finset (Fin n → Fin k)).filter
            (fun f => ∀ j, (Finset.univ.filter (fun i => f i = j)).Nonempty),
            ∏ j : Fin k, S.blockT w
              ((Finset.univ.filter (fun i => f i = j)).card) := by
    rw [← hC1, ← mul_assoc, inv_mul_cancel₀ hkfac, one_mul]
  rw [hPa_eq, sum_filter_pi_prod_fiber_card n k (fun m => S.blockT w m),
    ← mul_assoc, mul_comm ((n.factorial : ℝ))⁻¹ ((k.factorial : ℝ))⁻¹,
    mul_assoc, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun mvec hm => ?_
  rw [Finset.mem_filter, Finset.mem_piAntidiag] at hm
  rw [← mul_assoc, inv_factorial_mul_card_eq hm.1.1,
    ← Finset.prod_mul_distrib]

open Classical in
theorem enorm_tfun_le (w : P → ℝ) (hw : ∀ γ : P, ‖w γ‖ₑ ≤ S.W γ) (m : ℕ) :
    ‖((m.factorial : ℝ))⁻¹ * S.blockT w m‖ₑ
      ≤ ((m.factorial : ℝ≥0∞))⁻¹ * ∑' δ : Fin m → P, S.clusterF δ := by
  rw [enorm_mul]
  refine mul_le_mul' ?_ ?_
  · rw [Real.enorm_eq_ofReal_abs, abs_inv, abs_of_nonneg (by positivity),
      ENNReal.ofReal_inv_of_pos (by exact_mod_cast m.factorial_pos)]
    rw [ENNReal.ofReal_natCast]
  · rw [PolymerSystem.blockT]
    by_cases hs : Summable fun δ : Fin m → P =>
      connSum (Finset.univ : Finset (Fin m)) (S.zetaEdge δ) * ∏ j, w (δ j)
    · have h1 : ‖∑' δ : Fin m → P,
          connSum (Finset.univ : Finset (Fin m)) (S.zetaEdge δ) *
            ∏ j, w (δ j)‖
          ≤ ∑' δ : Fin m → P,
              ‖connSum (Finset.univ : Finset (Fin m)) (S.zetaEdge δ) *
                ∏ j, w (δ j)‖ := norm_tsum_le_tsum_norm hs.norm
      calc ‖∑' δ : Fin m → P, _ * _‖ₑ
          = ENNReal.ofReal ‖∑' δ : Fin m → P,
              connSum (Finset.univ : Finset (Fin m)) (S.zetaEdge δ) *
                ∏ j, w (δ j)‖ := by
            rw [Real.enorm_eq_ofReal_abs, Real.norm_eq_abs]
        _ ≤ ENNReal.ofReal (∑' δ : Fin m → P,
              ‖connSum (Finset.univ : Finset (Fin m)) (S.zetaEdge δ) *
                ∏ j, w (δ j)‖) := ENNReal.ofReal_le_ofReal h1
        _ ≤ ∑' δ : Fin m → P,
              ‖connSum (Finset.univ : Finset (Fin m)) (S.zetaEdge δ) *
                ∏ j, w (δ j)‖ₑ := by
            rw [ENNReal.ofReal_tsum_of_nonneg (fun δ => norm_nonneg _)
              hs.norm]
            refine ENNReal.tsum_le_tsum fun δ => ?_
            rw [Real.enorm_eq_ofReal_abs, Real.norm_eq_abs]
        _ ≤ ∑' δ : Fin m → P, S.clusterF δ :=
            ENNReal.tsum_le_tsum fun δ => S.enorm_blockT_summand_le w hw δ
    · rw [tsum_eq_zero_of_not_summable hs]
      simp

end PolymerSystem

private theorem tsum_comm_nat {u : ℕ → ℕ → ℝ}
    (h : Summable fun p : ℕ × ℕ => u p.1 p.2) :
    (∑' n : ℕ, ∑' k : ℕ, u k n) = ∑' k : ℕ, ∑' n : ℕ, u k n :=
  Summable.tsum_comm h

private theorem tsum_eq_range_sum {g : ℕ → ℝ} {n : ℕ}
    (h : ∀ k, n < k → g k = 0) :
    (∑' k : ℕ, g k) = ∑ k ∈ Finset.range (n + 1), g k :=
  tsum_eq_sum fun k hk => h k (by simpa [Finset.mem_range] using hk)

private theorem tsum_const_mul_nat {c : ℝ} {g : ℕ → ℝ} :
    (∑' n : ℕ, c * g n) = c * ∑' n : ℕ, g n := tsum_mul_left

namespace PolymerSystem

variable (S : PolymerSystem P)

set_option maxHeartbeats 2000000 in
open Classical in
/-- FV Proposition 5.3 + §5.6, the cluster expansion identity: under the
Kotecký–Preiss condition with finite total tilted activity, the polymer
partition function is the exponential of the cluster series. -/
theorem Xi_eq_exp_clusterSeries [LinearOrder P] (w : P → ℝ)
    (hw : ∀ γ : P, ‖w γ‖ₑ ≤ S.W γ) (hKP : S.KPCondition) {eps : ℝ≥0∞}
    (heps : eps ≠ ∞)
    (htot : (∑' γ : P, S.W γ * ENNReal.ofReal (Real.exp (S.a γ))) ≤ eps) :
    Xi S.bad w = Real.exp (clusterSeries S w) := by
  classical
  have hWtot : (∑' γ : P, S.W γ) ≠ ∞ := by
    refine ne_top_of_le_ne_top heps
      (le_trans (ENNReal.tsum_le_tsum fun γ => ?_) htot)
    conv_lhs => rw [← mul_one (S.W γ)]
    refine mul_le_mul' le_rfl ?_
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (S.a_nonneg γ))
  set t : ℕ → ℝ := fun m => ((m.factorial : ℝ))⁻¹ * S.blockT w m with ht
  have htG : ∀ m, ‖t m‖ₑ
      ≤ ((m.factorial : ℝ≥0∞))⁻¹ * ∑' δ : Fin m → P, S.clusterF δ :=
    fun m => S.enorm_tfun_le w hw m
  have hGsum : (∑' m : ℕ, (((m + 1).factorial : ℝ≥0∞))⁻¹ *
      ∑' δ : Fin (m + 1) → P, S.clusterF δ) ≤ eps :=
    S.kp_total_bound hKP htot
  have hGsum_ne_top : (∑' m : ℕ, (((m + 1).factorial : ℝ≥0∞))⁻¹ *
      ∑' δ : Fin (m + 1) → P, S.clusterF δ) ≠ ∞ :=
    ne_top_of_le_ne_top heps hGsum
  have ht_summable : Summable fun m : ℕ => t (m + 1) :=
    summable_of_enorm_le hGsum_ne_top fun m => htG (m + 1)
  have ht_norm_summable : Summable fun m : ℕ => ‖t (m + 1)‖ :=
    summable_norm_of_enorm_le hGsum_ne_top fun m => htG (m + 1)
  have ht_enorm_le : (∑' m : ℕ, ‖t (m + 1)‖ₑ) ≤ eps :=
    le_trans (ENNReal.tsum_le_tsum fun m => htG (m + 1)) hGsum
  -- the cluster series in one-dimensional form
  have hcs : clusterSeries S w = ∑' m : ℕ, t (m + 1) := by
    have hsig_enorm : ∀ c : Σ n : ℕ, (Fin (n + 1) → P),
        ‖(((c.1 + 1).factorial : ℝ))⁻¹ *
          connSum (Finset.univ : Finset (Fin (c.1 + 1))) (S.zetaEdge c.2) *
          ∏ j, w (c.2 j)‖ₑ
          ≤ (((c.1 + 1).factorial : ℝ≥0∞))⁻¹ * S.clusterF c.2 := by
      intro c
      rw [mul_assoc, enorm_mul]
      refine mul_le_mul' ?_ (S.enorm_blockT_summand_le w hw c.2)
      rw [Real.enorm_eq_ofReal_abs, abs_inv,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ ((c.1 + 1).factorial : ℝ)),
        ENNReal.ofReal_inv_of_pos
          (by exact_mod_cast (c.1 + 1).factorial_pos),
        ENNReal.ofReal_natCast]
    have hsig_G : (∑' c : Σ n : ℕ, (Fin (n + 1) → P),
        (((c.1 + 1).factorial : ℝ≥0∞))⁻¹ * S.clusterF c.2) ≠ ∞ := by
      refine ne_top_of_le_ne_top hGsum_ne_top (le_of_eq ?_)
      rw [ENNReal.tsum_sigma']
      refine tsum_congr fun n => ?_
      dsimp only
      exact ENNReal.tsum_mul_left
    have hsig_summable : Summable
        (fun c : Σ n : ℕ, (Fin (n + 1) → P) =>
          (((c.1 + 1).factorial : ℝ))⁻¹ *
            connSum (Finset.univ : Finset (Fin (c.1 + 1)))
              (S.zetaEdge c.2) * ∏ j, w (c.2 j)) :=
      summable_of_enorm_le hsig_G hsig_enorm
    rw [clusterSeries, hsig_summable.tsum_sigma]
    refine tsum_congr fun n => ?_
    rw [ht]
    dsimp only
    rw [PolymerSystem.blockT, ← tsum_mul_left]
    exact tsum_congr fun δ => by rw [mul_assoc]
  -- power expansion
  have hpow : ∀ k : ℕ, (clusterSeries S w) ^ k
      = ∑' mv : Fin k → ℕ, ∏ j, t (mv j + 1) := by
    intro k
    rw [hcs]
    exact tsum_pow_eq_tsum_pi (fun m => t (m + 1)) ht_norm_summable k
  have hprod_summable : ∀ k : ℕ,
      Summable fun mv : Fin k → ℕ => ∏ j, t (mv j + 1) := by
    intro k
    refine summable_of_enorm_le
      (G := fun mv : Fin k → ℕ => ∏ j, ‖t (mv j + 1)‖ₑ) ?_ ?_
    · rw [← tsum_pow_eq_tsum_pi_ennreal (fun m => ‖t (m + 1)‖ₑ) k]
      exact ENNReal.pow_ne_top (ne_top_of_le_ne_top heps ht_enorm_le)
    · intro mv
      rw [enorm_finset_prod]
  -- joint summability of the regrouped double series
  have hU_ne_top : (∑' p : ℕ × ℕ,
      (((p.1.factorial : ℝ≥0∞))⁻¹ *
        ∑ mvec ∈ (Finset.piAntidiag
          (Finset.univ : Finset (Fin p.1)) p.2).filter (fun m => ∀ j, 1 ≤ m j),
          ∏ j, ‖t (mvec j)‖ₑ)) ≠ ∞ := by
    rw [ENNReal.tsum_prod']
    have hperk : ∀ k : ℕ, (∑' n : ℕ, (((k.factorial : ℝ≥0∞))⁻¹ *
        ∑ mvec ∈ (Finset.piAntidiag
          (Finset.univ : Finset (Fin k)) n).filter (fun m => ∀ j, 1 ≤ m j),
          ∏ j, ‖t (mvec j)‖ₑ))
        = ((k.factorial : ℝ≥0∞))⁻¹ * (∑' m : ℕ, ‖t (m + 1)‖ₑ) ^ k := by
      intro k
      rw [ENNReal.tsum_mul_left, ← tsum_shift_eq_ennreal (fun m => ‖t m‖ₑ),
        ← tsum_pow_eq_tsum_pi_ennreal (fun m => ‖t (m + 1)‖ₑ) k]
    rw [tsum_congr hperk]
    have hbound : (∑' k : ℕ, ((k.factorial : ℝ≥0∞))⁻¹ *
        (∑' m : ℕ, ‖t (m + 1)‖ₑ) ^ k)
        ≤ ∑' k : ℕ, ((k.factorial : ℝ≥0∞))⁻¹ *
            ENNReal.ofReal (eps.toReal) ^ k := by
      refine ENNReal.tsum_le_tsum fun k => ?_
      refine mul_le_mul' le_rfl (pow_le_pow_left' ?_ k)
      rw [ENNReal.ofReal_toReal heps]
      exact ht_enorm_le
    refine ne_top_of_le_ne_top ?_ hbound
    rw [← ofReal_exp_eq_tsum ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_ne_top
  have hu_summable : Summable (fun p : ℕ × ℕ =>
      ((p.1.factorial : ℝ))⁻¹ *
        ∑ mvec ∈ (Finset.piAntidiag
          (Finset.univ : Finset (Fin p.1)) p.2).filter (fun m => ∀ j, 1 ≤ m j),
          ∏ j, t (mvec j)) := by
    refine summable_of_enorm_le hU_ne_top fun p => ?_
    rw [enorm_mul]
    refine mul_le_mul' ?_ ?_
    · rw [Real.enorm_eq_ofReal_abs, abs_inv,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ (p.1.factorial : ℝ)),
        ENNReal.ofReal_inv_of_pos (by exact_mod_cast p.1.factorial_pos),
        ENNReal.ofReal_natCast]
    · refine le_trans (enorm_sum_le _ _) (Finset.sum_le_sum fun mvec _ => ?_)
      rw [enorm_finset_prod]
  -- assemble
  have hexp : Real.exp (clusterSeries S w)
      = ∑' k : ℕ, (clusterSeries S w) ^ k / (k.factorial : ℝ) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  calc Xi S.bad w
      = ∑' n : ℕ, ((n.factorial : ℝ))⁻¹ *
          ∑' γ : Fin n → P, S.deltaProd γ * ∏ j, w (γ j) :=
        S.Xi_eq_tuple_series w hw hWtot
    _ = ∑' n : ℕ, ∑ k ∈ Finset.range (n + 1),
          ((k.factorial : ℝ))⁻¹ *
            ∑ mvec ∈ (Finset.piAntidiag
              (Finset.univ : Finset (Fin k)) n).filter
              (fun m => ∀ j, 1 ≤ m j),
              ∏ j, t (mvec j) := by
        refine tsum_congr fun n => ?_
        rw [S.tuple_term_regrouped w hw hKP heps htot n]
    _ = ∑' n : ℕ, ∑' k : ℕ,
          ((k.factorial : ℝ))⁻¹ *
            ∑ mvec ∈ (Finset.piAntidiag
              (Finset.univ : Finset (Fin k)) n).filter
              (fun m => ∀ j, 1 ≤ m j),
              ∏ j, t (mvec j) := by
        refine tsum_congr fun n => ?_
        refine (tsum_eq_range_sum fun k hk => ?_).symm
        have hempty : (Finset.piAntidiag
            (Finset.univ : Finset (Fin k)) n).filter
            (fun m => ∀ j, 1 ≤ m j) = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro mvec hm
          rw [Finset.mem_filter, Finset.mem_piAntidiag] at hm
          have h1 : k ≤ ∑ j, mvec j := by
            calc k = ∑ _j : Fin k, 1 := by simp
              _ ≤ ∑ j, mvec j := Finset.sum_le_sum fun j _ => hm.2 j
          rw [hm.1.1] at h1
          omega
        rw [hempty, Finset.sum_empty, mul_zero]

    _ = ∑' k : ℕ, ∑' n : ℕ,
          ((k.factorial : ℝ))⁻¹ *
            ∑ mvec ∈ (Finset.piAntidiag
              (Finset.univ : Finset (Fin k)) n).filter
              (fun m => ∀ j, 1 ≤ m j),
              ∏ j, t (mvec j) := tsum_comm_nat hu_summable
    _ = ∑' k : ℕ, (clusterSeries S w) ^ k / (k.factorial : ℝ) := by
        refine tsum_congr fun k => ?_
        rw [tsum_const_mul_nat, ← tsum_shift_eq_real (hprod_summable k),
          ← hpow k, div_eq_mul_inv, mul_comm]
    _ = Real.exp (clusterSeries S w) := hexp.symm

end PolymerSystem

end PolymerKP
