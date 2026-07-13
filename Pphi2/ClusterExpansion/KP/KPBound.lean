/-
Mirrored from GibbsMeasure `Ch6Subtree/AppendixProofs/Cluster/KPBound.lean`
@ origin/feat/Ch6InfVolume (030b2fafc18db5c26deb3ffbcf44223304534cfe), 2026-07-13.
Generic Kotecký–Preiss engine (no spin/lattice dependence). Candidate for
standalone-library extraction (planning/keystone-18-campaign.md K18-0);
keep divergence minimal.
-/
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Pphi2.ClusterExpansion.KP.Graphs
import Pphi2.ClusterExpansion.KP.Counting
import Pphi2.ClusterExpansion.KP.TsumFacts

/-!
# The Kotecký–Preiss convergence bound (FV Theorem 5.4)

Abstract polymer systems with hard-core incompatibility, the Kotecký–Preiss
condition (FV (5.10)), and the rooted cluster bound: the sum over all clusters
rooted at a polymer `γ₀`, weighted by absolute Ursell factors and absolute
activities, is at most `exp (a γ₀)`.

All series here are `ℝ≥0∞`-valued: tsums are unconditionally defined, Fubini
and monotone rearrangements are free, and the final bound transfers to real
summability downstream.
-/

open scoped BigOperators ENNReal

set_option linter.unusedSectionVars false

namespace PolymerKP

/-- An abstract polymer system: `ℝ≥0∞`-valued absolute activities `W`, a
symmetric reflexive incompatibility relation `bad`, and a positive size
function `a` for the Kotecký–Preiss condition. -/
structure PolymerSystem (P : Type*) where
  W : P → ℝ≥0∞
  bad : P → P → Prop
  bad_symm : ∀ γ γ', bad γ γ' → bad γ' γ
  bad_refl : ∀ γ, bad γ γ
  a : P → ℝ
  a_nonneg : ∀ γ, 0 ≤ a γ

namespace PolymerSystem

variable {P : Type*} (S : PolymerSystem P)

open Classical in
/-- The hard-core `ζ` edge weight of a tuple of polymers: `-1` on incompatible
pairs, `0` on compatible ones. -/
noncomputable def zetaEdge {n : ℕ} (γ : Fin n → P) : Sym2 (Fin n) → ℝ :=
  Sym2.lift
    ⟨fun i j => if S.bad (γ i) (γ j) then -1 else 0, by
      intro i j
      dsimp only
      by_cases h : S.bad (γ i) (γ j)
      · rw [if_pos h, if_pos (S.bad_symm _ _ h)]
      · rw [if_neg h, if_neg fun h' => h (S.bad_symm _ _ h')]⟩

open Classical in
theorem zetaEdge_mk {n : ℕ} (γ : Fin n → P) (i j : Fin n) :
    S.zetaEdge γ s(i, j) = if S.bad (γ i) (γ j) then -1 else 0 :=
  rfl

/-- `ζ` composed with a coordinate relabeling is `ζ` of the relabeled tuple. -/
theorem zetaEdge_comp {n m : ℕ} (γ : Fin n → P) (σ : Fin m → Fin n)
    (e : Sym2 (Fin m)) :
    S.zetaEdge γ (Sym2.map σ e) = S.zetaEdge (γ ∘ σ) e := by
  induction e with
  | _ i j => rfl

theorem neg_one_le_zetaEdge {n : ℕ} (γ : Fin n → P) (e : Sym2 (Fin n)) :
    -1 ≤ S.zetaEdge γ e := by
  induction e with
  | _ i j =>
      rw [zetaEdge_mk]
      split_ifs <;> norm_num

theorem zetaEdge_nonpos {n : ℕ} (γ : Fin n → P) (e : Sym2 (Fin n)) :
    S.zetaEdge γ e ≤ 0 := by
  induction e with
  | _ i j =>
      rw [zetaEdge_mk]
      split_ifs <;> norm_num

open Classical in
theorem enorm_zetaEdge_mk {n : ℕ} (γ : Fin n → P) (i j : Fin n) :
    ‖S.zetaEdge γ s(i, j)‖ₑ = if S.bad (γ i) (γ j) then 1 else 0 := by
  rw [zetaEdge_mk]
  split_ifs
  · rw [show ‖(-1 : ℝ)‖ₑ = 1 by simp]
  · simp

open Classical in
/-- The Kotecký–Preiss condition (FV (5.10)): the incompatibility-weighted,
exponentially tilted activity sum in each row is dominated by the size
function. -/
noncomputable def KPCondition : Prop :=
  ∀ γ₀ : P,
    (∑' γ : P, if S.bad γ γ₀
        then S.W γ * ENNReal.ofReal (Real.exp (S.a γ)) else 0)
      ≤ ENNReal.ofReal (S.a γ₀)

/-- The absolute rooted cluster value at tuple length `n + 1`: the root `γ₀`
is prepended as coordinate `0`, and the remaining `n` polymer coordinates are
summed with absolute Ursell weight and absolute activities.  (FV: the terms of
the series (5.11).) -/
noncomputable def rootedVal (n : ℕ) (γ₀ : P) : ℝ≥0∞ :=
  ((n.factorial : ℝ≥0∞))⁻¹ *
    ∑' γ : Fin n → P,
      ‖connSum (Finset.univ : Finset (Fin (n + 1)))
        (S.zetaEdge (Fin.cons γ₀ γ))‖ₑ * ∏ j, S.W (γ j)

theorem connSum_univ_fin_one (z : Sym2 (Fin 1) → ℝ) :
    connSum (Finset.univ : Finset (Fin 1)) z = 1 := by
  have : (Finset.univ : Finset (Fin 1)) = {0} := rfl
  rw [this, connSum_singleton]

theorem rootedVal_zero (γ₀ : P) : S.rootedVal 0 γ₀ = 1 := by
  rw [rootedVal]
  have h : ∀ γ : Fin 0 → P,
      ‖connSum (Finset.univ : Finset (Fin 1))
        (S.zetaEdge (Fin.cons γ₀ γ))‖ₑ * ∏ j, S.W (γ j) = 1 := by
    intro γ
    rw [connSum_univ_fin_one]
    simp
  rw [tsum_congr h]
  have hone : (∑' _ : Fin 0 → P, (1 : ℝ≥0∞)) = 1 := by
    rw [tsum_eq_single (fun i => i.elim0)]
    intro b' hb'
    exact absurd (funext fun i => i.elim0) hb'
  rw [hone]
  simp

end PolymerSystem

/-! ### Elementary bounds for the star factors -/

theorem prod_one_add_nonneg_le_one {ι : Type*} {s : Finset ι} {y : ι → ℝ}
    (h : ∀ u ∈ s, -1 ≤ y u ∧ y u ≤ 0) :
    0 ≤ ∏ u ∈ s, (1 + y u) ∧ ∏ u ∈ s, (1 + y u) ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      obtain ⟨h1, h2⟩ := ih fun u hu => h u (Finset.mem_insert_of_mem hu)
      obtain ⟨ha1, ha2⟩ := h a (Finset.mem_insert_self a s)
      refine ⟨mul_nonneg (by linarith) h1, ?_⟩
      calc (1 + y a) * ∏ u ∈ s, (1 + y u) ≤ 1 * 1 :=
            mul_le_mul (by linarith) h2 h1 (by norm_num)
      _ = 1 := one_mul 1

/-- FV Exercise 5.2: `|∏ (1 + y) - 1| ≤ ∑ |y|` for `y`-values in `[-1, 0]`. -/
theorem abs_prod_one_add_sub_one_le {ι : Type*} {s : Finset ι} {y : ι → ℝ}
    (h : ∀ u ∈ s, -1 ≤ y u ∧ y u ≤ 0) :
    |(∏ u ∈ s, (1 + y u)) - 1| ≤ ∑ u ∈ s, |y u| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      obtain ⟨hQ0, hQ1⟩ :=
        prod_one_add_nonneg_le_one fun u hu => h u (Finset.mem_insert_of_mem hu)
      obtain ⟨ha1, ha2⟩ := h a (Finset.mem_insert_self a s)
      have ih' := ih fun u hu => h u (Finset.mem_insert_of_mem hu)
      have hsplit : (1 + y a) * (∏ u ∈ s, (1 + y u)) - 1
          = y a * (∏ u ∈ s, (1 + y u)) + ((∏ u ∈ s, (1 + y u)) - 1) := by
        ring
      rw [hsplit]
      calc |y a * (∏ u ∈ s, (1 + y u)) + ((∏ u ∈ s, (1 + y u)) - 1)|
          ≤ |y a * ∏ u ∈ s, (1 + y u)| + |(∏ u ∈ s, (1 + y u)) - 1| :=
            abs_add_le _ _
        _ ≤ |y a| + ∑ u ∈ s, |y u| := by
            refine add_le_add ?_ ih'
            rw [abs_mul]
            calc |y a| * |∏ u ∈ s, (1 + y u)| ≤ |y a| * 1 := by
                  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
                  rw [abs_of_nonneg hQ0]
                  exact hQ1
            _ = |y a| := mul_one _

theorem enorm_finset_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ‖∏ i ∈ s, f i‖ₑ = ∏ i ∈ s, ‖f i‖ₑ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, enorm_mul, ih]

theorem enorm_prod_one_add_sub_one_le {ι : Type*} {s : Finset ι} {y : ι → ℝ}
    (h : ∀ u ∈ s, -1 ≤ y u ∧ y u ≤ 0) :
    ‖(∏ u ∈ s, (1 + y u)) - 1‖ₑ ≤ ∑ u ∈ s, ‖y u‖ₑ := by
  rw [Real.enorm_eq_ofReal_abs]
  calc ENNReal.ofReal |(∏ u ∈ s, (1 + y u)) - 1|
      ≤ ENNReal.ofReal (∑ u ∈ s, |y u|) :=
        ENNReal.ofReal_le_ofReal (abs_prod_one_add_sub_one_le h)
    _ = ∑ u ∈ s, ENNReal.ofReal |y u| :=
        ENNReal.ofReal_sum_of_nonneg fun u _ => abs_nonneg (y u)
    _ = ∑ u ∈ s, ‖y u‖ₑ := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Real.enorm_eq_ofReal_abs]

/-- Products over the blocks of a partition recover the product over the
ground set. -/
theorem prod_partition {ι M : Type*} [DecidableEq ι] [CommMonoid M]
    {V : Finset ι} {Pa : Finset (Finset ι)} (hPa : Pa ∈ partitionsOn V)
    (g : ι → M) : ∏ i ∈ V, g i = ∏ W ∈ Pa, ∏ i ∈ W, g i := by
  obtain ⟨_, hdisj, hsup⟩ := mem_partitionsOn.1 hPa
  have hbi : V = Pa.biUnion id := by
    rw [← Finset.sup_eq_biUnion, hsup]
  rw [hbi]
  exact Finset.prod_biUnion hdisj

namespace PolymerSystem

variable {P : Type*} (S : PolymerSystem P)

/-! ### The star decomposition estimate -/

theorem univ_succ_eq (n : ℕ) :
    (Finset.univ : Finset (Fin (n + 1)))
      = insert 0 ((Finset.univ : Finset (Fin n)).map (Fin.succEmb n)) := by
  ext x
  constructor
  · intro _
    cases x using Fin.cases with
    | zero => exact Finset.mem_insert_self 0 _
    | succ i =>
        exact Finset.mem_insert_of_mem
          (Finset.mem_map_of_mem _ (Finset.mem_univ i))
  · intro _
    exact Finset.mem_univ x

theorem zero_notMem_map_succEmb (n : ℕ) :
    (0 : Fin (n + 1)) ∉ (Finset.univ : Finset (Fin n)).map (Fin.succEmb n) := by
  intro h
  obtain ⟨i, _, hi⟩ := Finset.mem_map.1 h
  exact Fin.succ_ne_zero i hi

open Classical in
/-- The absolute per-block value in the star decomposition: absolute connected
sum over the block, count of star links to the root `γ₀`, and the block's
activities. -/
noncomputable def blockVal (γ₀ : P) {n : ℕ} (γ : Fin n → P)
    (W : Finset (Fin n)) : ℝ≥0∞ :=
  ‖connSum W (S.zetaEdge γ)‖ₑ *
    (∑ w ∈ W, if S.bad γ₀ (γ w) then 1 else 0) *
    ∏ w ∈ W, S.W (γ w)

open Classical in
/-- The star-decomposition estimate: the absolute rooted Ursell weight is
dominated by the product of block values over partitions (FV, proof of
Theorem 5.4, display (5.16) before summation). -/
theorem enorm_connSum_cons_le (n : ℕ) (γ₀ : P) (γ : Fin n → P) :
    ‖connSum (Finset.univ : Finset (Fin (n + 1)))
        (S.zetaEdge (Fin.cons γ₀ γ))‖ₑ * ∏ j, S.W (γ j)
      ≤ ∑ Pa ∈ partitionsOn (Finset.univ : Finset (Fin n)),
          ∏ W ∈ Pa, S.blockVal γ₀ γ W := by
  classical
  set ρ : Fin (n + 1) → P := Fin.cons γ₀ γ with hρ
  -- star decomposition of the connected sum
  rw [univ_succ_eq n, connSum_insert _ (zero_notMem_map_succEmb n)]
  -- triangle inequality
  have htri : ‖∑ Pa ∈ partitionsOn
        ((Finset.univ : Finset (Fin n)).map (Fin.succEmb n)),
        (∏ W ∈ Pa, connSum W (S.zetaEdge ρ)) *
          ∏ W ∈ Pa, ((∏ u ∈ W, (1 + S.zetaEdge ρ s(0, u))) - 1)‖ₑ
      ≤ ∑ Pa ∈ partitionsOn
          ((Finset.univ : Finset (Fin n)).map (Fin.succEmb n)),
          (∏ W ∈ Pa, ‖connSum W (S.zetaEdge ρ)‖ₑ) *
            ∏ W ∈ Pa, ∑ u ∈ W, ‖S.zetaEdge ρ s(0, u)‖ₑ := by
    refine le_trans (enorm_sum_le _ _) (Finset.sum_le_sum fun Pa _ => ?_)
    rw [enorm_mul, enorm_finset_prod, enorm_finset_prod]
    refine mul_le_mul_left' (Finset.prod_le_prod' fun W _ => ?_) _
    exact enorm_prod_one_add_sub_one_le fun u _ =>
      ⟨S.neg_one_le_zetaEdge ρ _, S.zetaEdge_nonpos ρ _⟩
  refine le_trans (mul_le_mul_right' htri _) ?_
  -- transport to partitions of `Fin n` and identify block values
  rw [Finset.sum_mul,
    sum_partitionsOn_map (Fin.succEmb n) (Finset.univ : Finset (Fin n))]
  refine Finset.sum_le_sum fun Pa hPa => ?_
  -- per-partition identification
  have hconn : ∀ W : Finset (Fin n),
      ‖connSum (W.map (Fin.succEmb n)) (S.zetaEdge ρ)‖ₑ
        = ‖connSum W (S.zetaEdge γ)‖ₑ := by
    intro W
    rw [connSum_map]
    have hcomp : ρ ∘ (Fin.succEmb n) = γ := by
      funext i
      simp [hρ, Fin.succEmb]
    congr 1
    refine connSum_congr fun e _ => ?_
    rw [S.zetaEdge_comp, hcomp]
  have hstar : ∀ W : Finset (Fin n),
      (∑ u ∈ W.map (Fin.succEmb n), ‖S.zetaEdge ρ s(0, u)‖ₑ)
        = ∑ w ∈ W, if S.bad γ₀ (γ w) then 1 else 0 := by
    intro W
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [show ((Fin.succEmb n) w) = Fin.succ w from rfl, S.enorm_zetaEdge_mk]
    simp [hρ]
  have hweights : (∏ j, S.W (γ j))
      = ∏ W ∈ Pa, ∏ w ∈ W, S.W (γ w) :=
    prod_partition hPa fun j => S.W (γ j)
  refine le_of_eq ?_
  calc (∏ W ∈ Pa.image (fun W => W.map (Fin.succEmb n)),
          ‖connSum W (S.zetaEdge ρ)‖ₑ) *
        (∏ W ∈ Pa.image (fun W => W.map (Fin.succEmb n)),
          ∑ u ∈ W, ‖S.zetaEdge ρ s(0, u)‖ₑ) * ∏ j, S.W (γ j)
      = (∏ W ∈ Pa, ‖connSum W (S.zetaEdge γ)‖ₑ) *
          (∏ W ∈ Pa, ∑ w ∈ W, if S.bad γ₀ (γ w) then 1 else 0) *
          ∏ W ∈ Pa, ∏ w ∈ W, S.W (γ w) := by
        have hinj : ∀ x ∈ Pa, ∀ y ∈ Pa,
            x.map (Fin.succEmb n) = y.map (Fin.succEmb n) → x = y := by
          intro x _ y _ hxy
          exact Finset.map_injective _ hxy
        rw [Finset.prod_image hinj, Finset.prod_image hinj, hweights,
          Finset.prod_congr rfl fun W _ => hconn W,
          Finset.prod_congr rfl fun W _ => hstar W]
    _ = ∏ W ∈ Pa, S.blockVal γ₀ γ W := by
        simp only [blockVal]
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]

end PolymerSystem

/-! ### Blockwise factorization of tuple sums along a partition -/

section BlockFactorization

variable {Q : Type*} {n : ℕ}

open Classical in
/-- The block of a partition containing a given coordinate. -/
noncomputable def blockOf {Pa : Finset (Finset (Fin n))}
    (hPa : Pa ∈ partitionsOn (Finset.univ : Finset (Fin n))) (i : Fin n) :
    {W // W ∈ Pa} :=
  ⟨(exists_unique_block hPa (Finset.mem_univ i)).exists.choose,
    (exists_unique_block hPa (Finset.mem_univ i)).exists.choose_spec.1⟩

theorem mem_blockOf {Pa : Finset (Finset (Fin n))}
    (hPa : Pa ∈ partitionsOn (Finset.univ : Finset (Fin n))) (i : Fin n) :
    i ∈ (blockOf hPa i).1 :=
  (exists_unique_block hPa (Finset.mem_univ i)).exists.choose_spec.2

theorem blockOf_eq {Pa : Finset (Finset (Fin n))}
    (hPa : Pa ∈ partitionsOn (Finset.univ : Finset (Fin n))) {i : Fin n}
    {W : Finset (Fin n)} (hW : W ∈ Pa) (hiW : i ∈ W) :
    (blockOf hPa i).1 = W := by
  obtain ⟨V, hV, huniq⟩ := exists_unique_block hPa (Finset.mem_univ i)
  have h1 := huniq (blockOf hPa i).1 ⟨(blockOf hPa i).2, mem_blockOf hPa i⟩
  have h2 := huniq W ⟨hW, hiW⟩
  rw [h1, h2]

open Classical in
/-- Blockwise factorization: a tsum over coordinate tuples of a product of
per-block values factorizes into a product of per-block tsums. -/
theorem tsum_prod_blocks {Pa : Finset (Finset (Fin n))}
    (hPa : Pa ∈ partitionsOn (Finset.univ : Finset (Fin n)))
    (H : (W : Finset (Fin n)) → (Fin W.card → Q) → ℝ≥0∞) :
    ∑' γ : Fin n → Q, ∏ W ∈ Pa, H W (γ ∘ (W.orderEmbOfFin rfl))
      = ∏ W ∈ Pa, ∑' δ : Fin W.card → Q, H W δ := by
  classical
  set k := Pa.card with hk
  set eP : {W // W ∈ Pa} ≃ Fin k := Pa.equivFin with heP
  set f : Fin n → Fin k := fun i => eP (blockOf hPa i) with hf
  -- the fiber of `f` over `j` is the block `(eP.symm j).1`
  have hfiber : ∀ (j : Fin k) (i : Fin n), f i = j ↔ i ∈ (eP.symm j).1 := by
    intro j i
    constructor
    · intro h
      have : blockOf hPa i = eP.symm j := by
        rw [← h]
        exact (Equiv.symm_apply_apply eP _).symm
      rw [← this]
      exact mem_blockOf hPa i
    · intro h
      have hbl : blockOf hPa i = eP.symm j := by
        refine Subtype.ext ?_
        exact blockOf_eq hPa (eP.symm j).2 h
      show eP (blockOf hPa i) = j
      rw [hbl, Equiv.apply_symm_apply]
  -- the per-fiber transport equivalence
  set tEquiv : ∀ j : Fin k, Fin ((eP.symm j).1.card) ≃ {i : Fin n // f i = j} :=
    fun j => ((eP.symm j).1.orderIsoOfFin rfl).toEquiv.trans
      (Equiv.subtypeEquivRight fun i => (hfiber j i).symm) with htE
  have htEquiv : ∀ (j : Fin k) (u : Fin ((eP.symm j).1.card)),
      ((tEquiv j u : {i : Fin n // f i = j}) : Fin n)
        = (eP.symm j).1.orderEmbOfFin rfl u := by
    intro j u
    rw [htE]
    simp only [Equiv.trans_apply, Equiv.subtypeEquivRight_apply,
      RelIso.coe_fn_toEquiv]
    exact Finset.coe_orderIsoOfFin_apply (eP.symm j).1 rfl u
  -- pass to the product over `Fin k`
  have hprodconv : ∀ (g : Finset (Fin n) → ℝ≥0∞),
      (∏ W ∈ Pa, g W) = ∏ j : Fin k, g (eP.symm j).1 := by
    intro g
    rw [← Finset.prod_attach Pa g]
    exact (Equiv.prod_comp eP.symm (fun w => g w.1)).symm
  calc ∑' γ : Fin n → Q, ∏ W ∈ Pa, H W (γ ∘ (W.orderEmbOfFin rfl))
      = ∑' γ : Fin n → Q,
          ∏ j : Fin k, H (eP.symm j).1 (γ ∘ ((eP.symm j).1.orderEmbOfFin rfl)) := by
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
        exact tsum_pi_prod_ennreal
          (A := fun j : Fin k => {i : Fin n // f i = j} → Q)
          (g := fun j y => H (eP.symm j).1 fun u => y (tEquiv j u))
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
    _ = ∏ W ∈ Pa, ∑' δ : Fin W.card → Q, H W δ := by
        exact (hprodconv fun W => ∑' δ : Fin W.card → Q, H W δ).symm

end BlockFactorization

/-! ### Elementary series identities in `ℝ≥0∞` -/

theorem ofReal_exp_eq_tsum {t : ℝ} (ht : 0 ≤ t) :
    ENNReal.ofReal (Real.exp t)
      = ∑' k : ℕ, ((k.factorial : ℝ≥0∞))⁻¹ * ENNReal.ofReal t ^ k := by
  have hexp : Real.exp t = ∑' k : ℕ, t ^ k / k.factorial := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  rw [hexp, ENNReal.ofReal_tsum_of_nonneg]
  · refine tsum_congr fun k => ?_
    rw [div_eq_mul_inv, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow ht, ENNReal.ofReal_inv_of_pos
        (by exact_mod_cast k.factorial_pos), mul_comm]
    congr 2
    exact_mod_cast rfl
  · intro k
    positivity
  · exact Real.summable_pow_div_factorial t

/-- Splitting the tsum over `(m+1)`-tuples into the head and the tail. -/
theorem tsum_cons_split {P : Type*} {m : ℕ} (G : (Fin (m + 1) → P) → ℝ≥0∞) :
    ∑' ρ : Fin (m + 1) → P, G ρ
      = ∑' δ₀ : P, ∑' δ : Fin m → P, G (Fin.cons δ₀ δ) := by
  rw [← Equiv.tsum_eq (Fin.consEquiv fun _ : Fin (m + 1) => P) G,
    ← ENNReal.tsum_prod]
  rfl

/-! ### Relabeling invariance of the cluster values -/

namespace PolymerSystem

variable {P : Type*} (S : PolymerSystem P)

/-- The absolute cluster value of a tuple: absolute connected sum times the
product of the activities. -/
noncomputable def clusterF {m : ℕ} (ρ : Fin m → P) : ℝ≥0∞ :=
  ‖connSum (Finset.univ : Finset (Fin m)) (S.zetaEdge ρ)‖ₑ * ∏ j, S.W (ρ j)

theorem connSum_zeta_comp_emb {n m : ℕ} (γ : Fin n → P) (σ : Fin m ↪ Fin n) :
    connSum ((Finset.univ : Finset (Fin m)).map σ) (S.zetaEdge γ)
      = connSum (Finset.univ : Finset (Fin m)) (S.zetaEdge (γ ∘ σ)) := by
  rw [connSum_map]
  exact connSum_congr fun e _ => S.zetaEdge_comp γ σ e

theorem connSum_zeta_perm {m : ℕ} (δ : Fin m → P) (σ : Equiv.Perm (Fin m)) :
    connSum (Finset.univ : Finset (Fin m)) (S.zetaEdge (δ ∘ σ))
      = connSum (Finset.univ : Finset (Fin m)) (S.zetaEdge δ) := by
  conv_rhs => rw [← Finset.map_univ_equiv σ]
  exact (S.connSum_zeta_comp_emb δ σ.toEmbedding).symm

theorem clusterF_comp_perm {m : ℕ} (δ : Fin m → P) (σ : Equiv.Perm (Fin m)) :
    S.clusterF (δ ∘ σ) = S.clusterF δ := by
  rw [clusterF, clusterF, S.connSum_zeta_perm δ σ]
  congr 1
  exact Equiv.prod_comp σ fun u => S.W (δ u)

open Classical in
/-- The relabeled per-block value in the star decomposition. -/
noncomputable def blockH (γ₀ : P) (m : ℕ) (δ : Fin m → P) : ℝ≥0∞ :=
  ‖connSum (Finset.univ : Finset (Fin m)) (S.zetaEdge δ)‖ₑ *
    (∑ u : Fin m, if S.bad γ₀ (δ u) then 1 else 0) *
    ∏ u, S.W (δ u)

open Classical in
theorem blockVal_eq_blockH (γ₀ : P) {n : ℕ} (γ : Fin n → P)
    (W : Finset (Fin n)) :
    S.blockVal γ₀ γ W = S.blockH γ₀ W.card (γ ∘ (W.orderEmbOfFin rfl)) := by
  classical
  rw [blockVal, blockH]
  have hW : W = (Finset.univ : Finset (Fin W.card)).map
      (W.orderEmbOfFin rfl).toEmbedding :=
    (Finset.map_orderEmbOfFin_univ W rfl).symm
  have hconn : ‖connSum W (S.zetaEdge γ)‖ₑ
      = ‖connSum (Finset.univ : Finset (Fin W.card))
          (S.zetaEdge (γ ∘ (W.orderEmbOfFin rfl)))‖ₑ := by
    conv_lhs => rw [hW]
    rw [S.connSum_zeta_comp_emb γ (W.orderEmbOfFin rfl).toEmbedding]
    rfl
  have hstar : (∑ w ∈ W, if S.bad γ₀ (γ w) then (1 : ℝ≥0∞) else 0)
      = ∑ u : Fin W.card,
          if S.bad γ₀ ((γ ∘ (W.orderEmbOfFin rfl)) u) then 1 else 0 := by
    conv_lhs => rw [hW]
    rw [Finset.sum_map]
    rfl
  have hwt : (∏ w ∈ W, S.W (γ w))
      = ∏ u : Fin W.card, S.W ((γ ∘ (W.orderEmbOfFin rfl)) u) := by
    conv_lhs => rw [hW]
    rw [Finset.prod_map]
    rfl
  rw [hconn, hstar, hwt]

open Classical in
theorem blockH_zero (γ₀ : P) (δ : Fin 0 → P) : S.blockH γ₀ 0 δ = 0 := by
  rw [blockH]
  simp

open Classical in
/-- The per-block value resums into an incompatibility-restricted activity sum
against smaller rooted cluster values. -/
theorem inv_factorial_mul_blockH_tsum (γ₀ : P) (m : ℕ) :
    (((m + 1).factorial : ℝ≥0∞))⁻¹ *
        ∑' δ : Fin (m + 1) → P, S.blockH γ₀ (m + 1) δ
      = ∑' δ₀ : P,
          if S.bad γ₀ δ₀ then S.W δ₀ * S.rootedVal m δ₀ else 0 := by
  classical
  -- pin the star link at coordinate `0`
  have hpin : (∑' δ : Fin (m + 1) → P, S.blockH γ₀ (m + 1) δ)
      = (m + 1) * ∑' δ : Fin (m + 1) → P,
          (if S.bad γ₀ (δ 0) then S.clusterF δ else 0) := by
    have hform : ∀ δ : Fin (m + 1) → P,
        S.blockH γ₀ (m + 1) δ
          = S.clusterF δ * ∑ u : Fin (m + 1),
              if S.bad γ₀ (δ u) then 1 else 0 := by
      intro δ
      rw [blockH, clusterF]
      ring
    rw [tsum_congr hform]
    have hT5 := tsum_sum_pin_eq_card_mul_pinned (P := P) (n := m)
      (F := fun δ => S.clusterF δ)
      (fun σ δ => S.clusterF_comp_perm δ σ) (r := fun x => S.bad γ₀ x)
    rw [hT5]
  -- split off the head coordinate
  have hsplit : (∑' δ : Fin (m + 1) → P,
        (if S.bad γ₀ (δ 0) then S.clusterF δ else 0))
      = ∑' δ₀ : P, if S.bad γ₀ δ₀ then
          S.W δ₀ * ((m.factorial : ℝ≥0∞) * S.rootedVal m δ₀) else 0 := by
    rw [tsum_cons_split fun δ => if S.bad γ₀ (δ 0) then S.clusterF δ else 0]
    refine tsum_congr fun δ₀ => ?_
    by_cases h : S.bad γ₀ δ₀
    · rw [if_pos h]
      have hval : ∀ δ : Fin m → P,
          (if S.bad γ₀ ((Fin.cons δ₀ δ : Fin (m + 1) → P) 0) then
            S.clusterF (Fin.cons δ₀ δ) else 0)
            = S.W δ₀ * (‖connSum (Finset.univ : Finset (Fin (m + 1)))
                (S.zetaEdge (Fin.cons δ₀ δ))‖ₑ * ∏ j : Fin m, S.W (δ j)) := by
        intro δ
        rw [Fin.cons_zero, if_pos h, clusterF]
        rw [Fin.prod_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        ring
      rw [tsum_congr hval, ENNReal.tsum_mul_left]
      congr 1
      rw [rootedVal, ← mul_assoc,
        ENNReal.mul_inv_cancel (by exact_mod_cast m.factorial_pos.ne')
          (by exact_mod_cast (ENNReal.natCast_ne_top m.factorial)),
        one_mul]
    · rw [if_neg h]
      have hval : ∀ δ : Fin m → P,
          (if S.bad γ₀ ((Fin.cons δ₀ δ : Fin (m + 1) → P) 0) then
            S.clusterF (Fin.cons δ₀ δ) else 0) = 0 := by
        intro δ
        rw [Fin.cons_zero, if_neg h]
      rw [tsum_congr hval, tsum_zero]
  have hpull : ∀ δ₀ : P,
      (if S.bad γ₀ δ₀ then
        S.W δ₀ * ((m.factorial : ℝ≥0∞) * S.rootedVal m δ₀) else 0)
        = (m.factorial : ℝ≥0∞) *
            (if S.bad γ₀ δ₀ then S.W δ₀ * S.rootedVal m δ₀ else 0) := by
    intro δ₀
    by_cases h : S.bad γ₀ δ₀
    · rw [if_pos h, if_pos h]
      ring
    · rw [if_neg h, if_neg h, mul_zero]
  have hfac : (((m + 1).factorial : ℝ≥0∞))⁻¹ *
      (((m : ℝ≥0∞) + 1) * (m.factorial : ℝ≥0∞)) = 1 := by
    have h1 : ((m + 1).factorial : ℝ≥0∞)
        = ((m : ℝ≥0∞) + 1) * (m.factorial : ℝ≥0∞) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    rw [← h1]
    refine ENNReal.inv_mul_cancel ?_ ?_
    · exact_mod_cast (m + 1).factorial_pos.ne'
    · exact ENNReal.natCast_ne_top _
  calc (((m + 1).factorial : ℝ≥0∞))⁻¹ *
        ∑' δ : Fin (m + 1) → P, S.blockH γ₀ (m + 1) δ
      = (((m + 1).factorial : ℝ≥0∞))⁻¹ * (((m : ℝ≥0∞) + 1) *
          ((m.factorial : ℝ≥0∞) *
            ∑' δ₀ : P,
              if S.bad γ₀ δ₀ then S.W δ₀ * S.rootedVal m δ₀ else 0)) := by
        rw [hpin, hsplit, tsum_congr hpull, ENNReal.tsum_mul_left]
    _ = ∑' δ₀ : P,
          if S.bad γ₀ δ₀ then S.W δ₀ * S.rootedVal m δ₀ else 0 := by
        rw [← mul_assoc (((m : ℝ≥0∞)) + 1), ← mul_assoc, hfac, one_mul]

end PolymerSystem

/-! ### Counting helpers for the induction -/

theorem partition_card_le {n : ℕ} {Pa : Finset (Finset (Fin n))}
    (hPa : Pa ∈ partitionsOn (Finset.univ : Finset (Fin n))) :
    Pa.card ≤ n := by
  classical
  obtain ⟨hne, hdisj, hsup⟩ := mem_partitionsOn.1 hPa
  have hcards : (∑ W ∈ Pa, W.card) = n := by
    have hbi : (Finset.univ : Finset (Fin n)) = Pa.biUnion id := by
      rw [← Finset.sup_eq_biUnion, hsup]
    have h := Finset.card_biUnion
      (fun W hW W' hW' hne' => hdisj hW hW' hne') (s := Pa) (t := id)
    rw [← hbi, Finset.card_univ, Fintype.card_fin] at h
    exact h.symm
  calc Pa.card = ∑ _W ∈ Pa, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one]
    _ ≤ ∑ W ∈ Pa, W.card :=
        Finset.sum_le_sum fun W hW => Nat.one_le_iff_ne_zero.2
          (Finset.card_ne_zero_of_mem ((hne W hW).choose_spec))
    _ = n := hcards

private theorem inv_prod_natCast {ι : Type*} (s : Finset ι) (g : ι → ℕ)
    (h : ∀ j ∈ s, g j ≠ 0) :
    ((∏ j ∈ s, (g j : ℝ≥0∞)))⁻¹ = ∏ j ∈ s, ((g j : ℝ≥0∞))⁻¹ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha,
        ENNReal.mul_inv
          (Or.inl (by exact_mod_cast h a (Finset.mem_insert_self a s)))
          (Or.inl (ENNReal.natCast_ne_top _)),
        ih fun j hj => h j (Finset.mem_insert_of_mem hj)]

namespace PolymerSystem

variable {P : Type*} (S : PolymerSystem P)

open Classical in
/-- The per-size estimate: the rooted cluster value at size `n + 1` is bounded
by a multinomial resummation of per-block values (FV (5.16)). -/
theorem rootedVal_succ_le (γ₀ : P) (n : ℕ) :
    S.rootedVal (n + 1) γ₀
      ≤ ∑' k : ℕ, ((k.factorial : ℝ≥0∞))⁻¹ *
          ∑ mvec ∈ Finset.piAntidiag (Finset.univ : Finset (Fin k)) (n + 1),
            ∏ j : Fin k, (((mvec j).factorial : ℝ≥0∞))⁻¹ *
              ∑' δ : Fin (mvec j) → P, S.blockH γ₀ (mvec j) δ := by
  classical
  set B : ℕ → ℝ≥0∞ := fun m => ∑' δ : Fin m → P, S.blockH γ₀ m δ with hB
  -- star-decomposition estimate and blockwise factorization
  have h1 : S.rootedVal (n + 1) γ₀
      ≤ (((n + 1).factorial : ℝ≥0∞))⁻¹ *
          ∑ Pa ∈ partitionsOn (Finset.univ : Finset (Fin (n + 1))),
            ∏ W ∈ Pa, B W.card := by
    rw [rootedVal]
    refine mul_le_mul_left' ?_ _
    calc (∑' γ : Fin (n + 1) → P,
          ‖connSum (Finset.univ : Finset (Fin (n + 1 + 1)))
            (S.zetaEdge (Fin.cons γ₀ γ))‖ₑ * ∏ j, S.W (γ j))
        ≤ ∑' γ : Fin (n + 1) → P,
            ∑ Pa ∈ partitionsOn (Finset.univ : Finset (Fin (n + 1))),
              ∏ W ∈ Pa, S.blockVal γ₀ γ W :=
          ENNReal.tsum_le_tsum fun γ => S.enorm_connSum_cons_le (n + 1) γ₀ γ
      _ = ∑ Pa ∈ partitionsOn (Finset.univ : Finset (Fin (n + 1))),
            ∑' γ : Fin (n + 1) → P, ∏ W ∈ Pa, S.blockVal γ₀ γ W :=
          Summable.tsum_finsetSum fun Pa _ => ENNReal.summable
      _ = ∑ Pa ∈ partitionsOn (Finset.univ : Finset (Fin (n + 1))),
            ∏ W ∈ Pa, B W.card := by
          refine Finset.sum_congr rfl fun Pa hPa => ?_
          rw [tsum_congr fun γ =>
            Finset.prod_congr rfl fun W _ => S.blockVal_eq_blockH γ₀ γ W]
          exact tsum_prod_blocks hPa fun W δ => S.blockH γ₀ W.card δ
  -- group by the number of blocks and apply the counting bounds
  have h2 : (∑ Pa ∈ partitionsOn (Finset.univ : Finset (Fin (n + 1))),
        ∏ W ∈ Pa, B W.card)
      ≤ ∑ k ∈ Finset.range (n + 2), ((k.factorial : ℝ≥0∞))⁻¹ *
          ∑ f : Fin (n + 1) → Fin k,
            ∏ j : Fin k, B ((Finset.univ.filter fun i => f i = j).card) := by
    rw [← Finset.sum_fiberwise_of_maps_to
      (g := fun Pa => Pa.card)
      (fun Pa hPa => Finset.mem_range.2
        (Nat.lt_succ_of_le (partition_card_le hPa)))
      (fun Pa => ∏ W ∈ Pa, B W.card)]
    exact Finset.sum_le_sum fun k _ => sum_partitions_card_le
      (u := fun W => B W.card) k
  -- convert to size-vector form
  have h3 : ∀ k : ℕ,
      (∑ f : Fin (n + 1) → Fin k,
        ∏ j : Fin k, B ((Finset.univ.filter fun i => f i = j).card))
      = ∑ mvec ∈ Finset.piAntidiag (Finset.univ : Finset (Fin k)) (n + 1),
          (((Finset.univ : Finset (Fin (n + 1) → Fin k)).filter
            (fun f => ∀ j, (Finset.univ.filter fun i => f i = j).card
              = mvec j)).card : ℝ≥0∞) * ∏ j : Fin k, B (mvec j) :=
    fun k => sum_pi_prod_fiber_card (n + 1) k B
  -- the multinomial cancellation
  have h4 : ∀ (k : ℕ),
      ∀ mvec ∈ Finset.piAntidiag (Finset.univ : Finset (Fin k)) (n + 1),
      (((n + 1).factorial : ℝ≥0∞))⁻¹ *
        ((((Finset.univ : Finset (Fin (n + 1) → Fin k)).filter
          (fun f => ∀ j, (Finset.univ.filter fun i => f i = j).card
            = mvec j)).card : ℝ≥0∞) * ∏ j : Fin k, B (mvec j))
      = ∏ j : Fin k, (((mvec j).factorial : ℝ≥0∞))⁻¹ * B (mvec j) := by
    intro k mvec hm
    have hsum : (∑ j, mvec j) = n + 1 := (Finset.mem_piAntidiag.1 hm).1
    have hnat := card_fiber_sizes_mul_factorials (m := mvec) hsum
    have hcast : ((((Finset.univ : Finset (Fin (n + 1) → Fin k)).filter
        (fun f => ∀ j, (Finset.univ.filter fun i => f i = j).card
          = mvec j)).card : ℝ≥0∞) *
          ∏ j : Fin k, (((mvec j).factorial : ℝ≥0∞)))
        = (((n + 1).factorial : ℝ≥0∞)) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℝ≥0∞) hnat
    have hPine : (∏ j : Fin k, (((mvec j).factorial : ℝ≥0∞))) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.2 fun j _ => ?_
      exact_mod_cast (mvec j).factorial_pos.ne'
    have hcardne : ((((Finset.univ : Finset (Fin (n + 1) → Fin k)).filter
        (fun f => ∀ j, (Finset.univ.filter fun i => f i = j).card
          = mvec j)).card : ℝ≥0∞)) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hcast
      exact (by exact_mod_cast (n + 1).factorial_pos.ne' :
        (((n + 1).factorial : ℝ≥0∞)) ≠ 0) hcast.symm
    rw [← hcast]
    rw [ENNReal.mul_inv (Or.inl hcardne) (Or.inl (ENNReal.natCast_ne_top _))]
    calc (((Finset.univ.filter _).card : ℝ≥0∞))⁻¹ *
          ((∏ j : Fin k, (((mvec j).factorial : ℝ≥0∞))))⁻¹ *
          (((Finset.univ.filter _).card : ℝ≥0∞) * ∏ j : Fin k, B (mvec j))
        = (((Finset.univ.filter _).card : ℝ≥0∞))⁻¹ *
            ((Finset.univ.filter _).card : ℝ≥0∞) *
            (((∏ j : Fin k, (((mvec j).factorial : ℝ≥0∞))))⁻¹ *
              ∏ j : Fin k, B (mvec j)) := by ring
      _ = ((∏ j : Fin k, (((mvec j).factorial : ℝ≥0∞))))⁻¹ *
            ∏ j : Fin k, B (mvec j) := by
          rw [ENNReal.inv_mul_cancel hcardne (ENNReal.natCast_ne_top _),
            one_mul]
      _ = ∏ j : Fin k, ((((mvec j).factorial : ℝ≥0∞)))⁻¹ * B (mvec j) := by
          rw [Finset.prod_mul_distrib, ← inv_prod_natCast Finset.univ
            (fun j => (mvec j).factorial)
            (fun j _ => (mvec j).factorial_pos.ne')]
  -- assemble
  calc S.rootedVal (n + 1) γ₀
      ≤ (((n + 1).factorial : ℝ≥0∞))⁻¹ *
          ∑ Pa ∈ partitionsOn (Finset.univ : Finset (Fin (n + 1))),
            ∏ W ∈ Pa, B W.card := h1
    _ ≤ (((n + 1).factorial : ℝ≥0∞))⁻¹ *
          ∑ k ∈ Finset.range (n + 2), ((k.factorial : ℝ≥0∞))⁻¹ *
            ∑ f : Fin (n + 1) → Fin k,
              ∏ j : Fin k, B ((Finset.univ.filter fun i => f i = j).card) :=
        mul_le_mul_left' h2 _
    _ = ∑ k ∈ Finset.range (n + 2), ((k.factorial : ℝ≥0∞))⁻¹ *
          ∑ mvec ∈ Finset.piAntidiag (Finset.univ : Finset (Fin k)) (n + 1),
            ∏ j : Fin k, (((mvec j).factorial : ℝ≥0∞))⁻¹ * B (mvec j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [h3 k, ← mul_assoc, mul_comm (((n + 1).factorial : ℝ≥0∞))⁻¹
          ((k.factorial : ℝ≥0∞))⁻¹, mul_assoc, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun mvec hm => h4 k mvec hm
    _ ≤ ∑' k : ℕ, ((k.factorial : ℝ≥0∞))⁻¹ *
          ∑ mvec ∈ Finset.piAntidiag (Finset.univ : Finset (Fin k)) (n + 1),
            ∏ j : Fin k, (((mvec j).factorial : ℝ≥0∞))⁻¹ * B (mvec j) :=
        ENNReal.sum_le_tsum _

open Classical in
/-- The block-value partial sums are controlled by the Kotecký–Preiss
condition, given the inductive bound on smaller rooted values. -/
theorem blockH_partial_le (hKP : S.KPCondition) (γ₀ : P) (N : ℕ)
    (hIH : ∀ δ₀ : P, (∑ n ∈ Finset.range N, S.rootedVal n δ₀)
      ≤ ENNReal.ofReal (Real.exp (S.a δ₀))) :
    (∑ m ∈ Finset.range (N + 1),
        ((m.factorial : ℝ≥0∞))⁻¹ * ∑' δ : Fin m → P, S.blockH γ₀ m δ)
      ≤ ENNReal.ofReal (S.a γ₀) := by
  rw [Finset.sum_range_succ'
    (fun m => ((m.factorial : ℝ≥0∞))⁻¹ *
      ∑' δ : Fin m → P, S.blockH γ₀ m δ) N]
  have h0 : ((Nat.factorial 0 : ℝ≥0∞))⁻¹ *
      ∑' δ : Fin 0 → P, S.blockH γ₀ 0 δ = 0 := by
    rw [tsum_congr (S.blockH_zero γ₀), tsum_zero, mul_zero]
  rw [h0, add_zero,
    Finset.sum_congr rfl fun m' _ =>
      S.inv_factorial_mul_blockH_tsum γ₀ m',
    ← Summable.tsum_finsetSum fun m' _ => ENNReal.summable]
  have hcollect : ∀ δ₀ : P, (∑ m' ∈ Finset.range N,
      if S.bad γ₀ δ₀ then S.W δ₀ * S.rootedVal m' δ₀ else 0)
      = if S.bad γ₀ δ₀ then
          S.W δ₀ * ∑ m' ∈ Finset.range N, S.rootedVal m' δ₀ else 0 := by
    intro δ₀
    by_cases h : S.bad γ₀ δ₀
    · simp only [if_pos h, Finset.mul_sum]
    · simp only [if_neg h, Finset.sum_const_zero]
  rw [tsum_congr hcollect]
  calc (∑' δ₀ : P, if S.bad γ₀ δ₀ then
        S.W δ₀ * ∑ m' ∈ Finset.range N, S.rootedVal m' δ₀ else 0)
      ≤ ∑' δ₀ : P, if S.bad γ₀ δ₀ then
          S.W δ₀ * ENNReal.ofReal (Real.exp (S.a δ₀)) else 0 := by
        refine ENNReal.tsum_le_tsum fun δ₀ => ?_
        by_cases h : S.bad γ₀ δ₀
        · rw [if_pos h, if_pos h]
          exact mul_le_mul_left' (hIH δ₀) _
        · rw [if_neg h, if_neg h]
    _ = ∑' δ₀ : P, if S.bad δ₀ γ₀ then
          S.W δ₀ * ENNReal.ofReal (Real.exp (S.a δ₀)) else 0 := by
        refine tsum_congr fun δ₀ => ?_
        exact if_congr ⟨fun h => S.bad_symm _ _ h,
          fun h => S.bad_symm _ _ h⟩ rfl rfl
    _ ≤ ENNReal.ofReal (S.a γ₀) := hKP γ₀

end PolymerSystem

/-- Dropping the composition constraint: summing the per-size products over
all compositions of all totals up to `N` is dominated by the `k`-th power of
the one-variable partial sum. -/
theorem sum_piAntidiag_le_pow (v : ℕ → ℝ≥0∞) (N k : ℕ) :
    (∑ n ∈ Finset.range N,
        ∑ mvec ∈ Finset.piAntidiag (Finset.univ : Finset (Fin k)) (n + 1),
          ∏ j : Fin k, v (mvec j))
      ≤ (∑ m ∈ Finset.range (N + 1), v m) ^ k := by
  classical
  have hdisjoint : (↑(Finset.range N) : Set ℕ).PairwiseDisjoint
      (fun n => Finset.piAntidiag
        (Finset.univ : Finset (Fin k)) (n + 1)) := by
    intro n₁ _ n₂ _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro mvec h1 h2
    have hs1 := (Finset.mem_piAntidiag.1 h1).1
    have hs2 := (Finset.mem_piAntidiag.1 h2).1
    exact hne (by omega)
  have hsubset : (Finset.range N).biUnion
      (fun n => Finset.piAntidiag
        (Finset.univ : Finset (Fin k)) (n + 1))
      ⊆ Fintype.piFinset fun _ : Fin k => Finset.range (N + 1) := by
    intro mvec hm
    obtain ⟨n, hn, hmem⟩ := Finset.mem_biUnion.1 hm
    rw [Finset.mem_range] at hn
    have hsum := (Finset.mem_piAntidiag.1 hmem).1
    rw [Fintype.mem_piFinset]
    intro j
    rw [Finset.mem_range]
    have : mvec j ≤ n + 1 := by
      rw [← hsum]
      exact Finset.single_le_sum
        (f := fun j => mvec j) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j)
    omega
  calc (∑ n ∈ Finset.range N,
        ∑ mvec ∈ Finset.piAntidiag
          (Finset.univ : Finset (Fin k)) (n + 1),
          ∏ j : Fin k, v (mvec j))
      = ∑ mvec ∈ (Finset.range N).biUnion
          (fun n => Finset.piAntidiag
            (Finset.univ : Finset (Fin k)) (n + 1)),
          ∏ j : Fin k, v (mvec j) :=
        (Finset.sum_biUnion hdisjoint).symm
    _ ≤ ∑ mvec ∈ Fintype.piFinset fun _ : Fin k =>
          Finset.range (N + 1), ∏ j : Fin k, v (mvec j) :=
        Finset.sum_le_sum_of_subset hsubset
    _ = ∏ _j : Fin k, ∑ m ∈ Finset.range (N + 1), v m :=
        (Finset.prod_univ_sum _ _).symm
    _ = (∑ m ∈ Finset.range (N + 1), v m) ^ k := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

private theorem tsum_shift_le {g h : ℕ → ℝ≥0∞} (h0 : g 0 = 0)
    (hle : ∀ k, g (k + 1) ≤ h k) : (∑' k, g k) ≤ ∑' k, h k := by
  have hre : (∑' k : ℕ, g (k + 1)) = ∑' k : ℕ, g k := by
    refine Function.Injective.tsum_eq Nat.succ_injective ?_
    intro x hx
    match x with
    | 0 => exact absurd h0 hx
    | n + 1 => exact ⟨n, rfl⟩
  rw [← hre]
  exact ENNReal.tsum_le_tsum hle

private theorem tsum_shift_add_zero {h : ℕ → ℝ≥0∞} :
    (∑' k, h (k + 1)) + h 0 = ∑' k, h k := by
  classical
  have h1 : (∑' k : ℕ, h (k + 1))
      = ∑' x : ℕ, if x = 0 then 0 else h x := by
    have h2 : (∑' k : ℕ, (if k + 1 = 0 then (0 : ℝ≥0∞) else h (k + 1)))
        = ∑' x : ℕ, if x = 0 then 0 else h x := by
      refine Function.Injective.tsum_eq
        (f := fun x : ℕ => if x = 0 then (0 : ℝ≥0∞) else h x)
        Nat.succ_injective ?_
      intro x hx
      match x with
      | 0 => simp at hx
      | n + 1 => exact ⟨n, rfl⟩
    rw [← h2]
    exact tsum_congr fun k => by rw [if_neg (Nat.succ_ne_zero k)]
  rw [h1, ENNReal.tsum_eq_add_tsum_ite (f := h) 0, add_comm]
  refine congrArg (h 0 + ·) (tsum_congr fun x => ?_)
  by_cases hx : x = 0
  · rw [if_pos hx, if_pos hx]
  · rw [if_neg hx, if_neg hx]

theorem piAntidiag_fin_zero_empty (n : ℕ) :
    Finset.piAntidiag (Finset.univ : Finset (Fin 0)) (n + 1) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro mvec hm
  have := (Finset.mem_piAntidiag.1 hm).1
  simp at this

namespace PolymerSystem

variable {P : Type*} (S : PolymerSystem P)

open Classical in
/-- The tail of the partial rooted sums, bounded through the block values. -/
theorem rootedVal_range_succ_le (γ₀ : P) (N : ℕ) {x : ℝ≥0∞}
    (hbs : (∑ m ∈ Finset.range (N + 1),
      ((m.factorial : ℝ≥0∞))⁻¹ * ∑' δ : Fin m → P, S.blockH γ₀ m δ) ≤ x) :
    (∑ n ∈ Finset.range N, S.rootedVal (n + 1) γ₀)
      ≤ ∑' k : ℕ, (((k + 1).factorial : ℝ≥0∞))⁻¹ * x ^ (k + 1) := by
  classical
  set v : ℕ → ℝ≥0∞ :=
    fun m => ((m.factorial : ℝ≥0∞))⁻¹ *
      ∑' δ : Fin m → P, S.blockH γ₀ m δ with hv
  calc (∑ n ∈ Finset.range N, S.rootedVal (n + 1) γ₀)
      ≤ ∑ n ∈ Finset.range N, ∑' k : ℕ, ((k.factorial : ℝ≥0∞))⁻¹ *
          ∑ mvec ∈ Finset.piAntidiag
            (Finset.univ : Finset (Fin k)) (n + 1),
            ∏ j : Fin k, v (mvec j) :=
        Finset.sum_le_sum fun n _ => S.rootedVal_succ_le γ₀ n
    _ = ∑' k : ℕ, ((k.factorial : ℝ≥0∞))⁻¹ *
          ∑ n ∈ Finset.range N,
          ∑ mvec ∈ Finset.piAntidiag
            (Finset.univ : Finset (Fin k)) (n + 1),
            ∏ j : Fin k, v (mvec j) := by
        rw [← Summable.tsum_finsetSum fun n _ => ENNReal.summable]
        refine tsum_congr fun k => ?_
        rw [Finset.mul_sum]
    _ ≤ ∑' k : ℕ, ((k.factorial : ℝ≥0∞))⁻¹ * x ^ k
          * (if k = 0 then 0 else 1) := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · have hzero : (∑ n ∈ Finset.range N,
              ∑ mvec ∈ Finset.piAntidiag
                (Finset.univ : Finset (Fin 0)) (n + 1),
                ∏ j : Fin 0, v (mvec j)) = 0 := by
            refine Finset.sum_eq_zero fun n _ => ?_
            rw [piAntidiag_fin_zero_empty n, Finset.sum_empty]
          rw [hzero, mul_zero, if_pos rfl, mul_zero]
        · rw [if_neg hk.ne', mul_one]
          refine mul_le_mul_left' ?_ _
          exact le_trans (sum_piAntidiag_le_pow v N k)
            (pow_le_pow_left' hbs k)
    _ ≤ ∑' k : ℕ, (((k + 1).factorial : ℝ≥0∞))⁻¹ * x ^ (k + 1) := by
        refine tsum_shift_le ?_ fun k => ?_
        · rw [if_pos rfl, mul_zero]
        · rw [if_neg (Nat.succ_ne_zero k), mul_one]

open Classical in
/-- FV Theorem 5.4, truncated form: under the Kotecký–Preiss condition the
partial sums of the rooted cluster values are uniformly bounded. -/
theorem rootedVal_partial_le (hKP : S.KPCondition) :
    ∀ (N : ℕ) (γ₀ : P),
      (∑ n ∈ Finset.range N, S.rootedVal n γ₀)
        ≤ ENNReal.ofReal (Real.exp (S.a γ₀)) := by
  intro N
  induction N with
  | zero =>
      intro γ₀
      simp
  | succ N ihN =>
      intro γ₀
      have hbs := S.blockH_partial_le hKP γ₀ N ihN
      have hmain := S.rootedVal_range_succ_le γ₀ N hbs
      calc (∑ n ∈ Finset.range (N + 1), S.rootedVal n γ₀)
          = (∑ n ∈ Finset.range N, S.rootedVal (n + 1) γ₀)
              + S.rootedVal 0 γ₀ := Finset.sum_range_succ' _ N
        _ = (∑ n ∈ Finset.range N, S.rootedVal (n + 1) γ₀) + 1 := by
            rw [S.rootedVal_zero γ₀]
        _ ≤ (∑' k : ℕ, (((k + 1).factorial : ℝ≥0∞))⁻¹ *
              ENNReal.ofReal (S.a γ₀) ^ (k + 1)) + 1 :=
            add_le_add hmain (le_refl 1)
        _ = ∑' k : ℕ, ((k.factorial : ℝ≥0∞))⁻¹ *
              ENNReal.ofReal (S.a γ₀) ^ k := by
            rw [← tsum_shift_add_zero (h := fun k =>
              ((k.factorial : ℝ≥0∞))⁻¹ * ENNReal.ofReal (S.a γ₀) ^ k)]
            congr 1
            simp
        _ = ENNReal.ofReal (Real.exp (S.a γ₀)) :=
            (ofReal_exp_eq_tsum (S.a_nonneg γ₀)).symm

/-- FV Theorem 5.4: the rooted cluster series is bounded by `exp (a γ₀)`. -/
theorem kp_rooted_bound (hKP : S.KPCondition) (γ₀ : P) :
    (∑' n : ℕ, S.rootedVal n γ₀) ≤ ENNReal.ofReal (Real.exp (S.a γ₀)) := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  obtain ⟨M, hM⟩ := Finset.exists_nat_subset_range s
  exact le_trans (Finset.sum_le_sum_of_subset hM)
    (S.rootedVal_partial_le hKP M γ₀)

open Classical in
private theorem tsum_ite_clusterF_cons (r : P → Prop) (n : ℕ) :
    (∑' ρ : Fin (n + 1) → P, (if r (ρ 0) then S.clusterF ρ else 0))
      = ∑' δ₀ : P, if r δ₀ then
          S.W δ₀ * ((n.factorial : ℝ≥0∞) * S.rootedVal n δ₀) else 0 := by
  rw [tsum_cons_split fun ρ => if r (ρ 0) then S.clusterF ρ else 0]
  refine tsum_congr fun δ₀ => ?_
  by_cases h : r δ₀
  · rw [if_pos h]
    have hval : ∀ δ : Fin n → P,
        (if r ((Fin.cons δ₀ δ : Fin (n + 1) → P) 0) then
          S.clusterF (Fin.cons δ₀ δ) else 0)
          = S.W δ₀ * (‖connSum (Finset.univ : Finset (Fin (n + 1)))
              (S.zetaEdge (Fin.cons δ₀ δ))‖ₑ * ∏ j : Fin n, S.W (δ j)) := by
      intro δ
      rw [Fin.cons_zero, if_pos h, clusterF, Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      ring
    rw [tsum_congr hval, ENNReal.tsum_mul_left]
    congr 1
    rw [rootedVal, ← mul_assoc,
      ENNReal.mul_inv_cancel (by exact_mod_cast n.factorial_pos.ne')
        (ENNReal.natCast_ne_top n.factorial), one_mul]
  · rw [if_neg h]
    have hval : ∀ δ : Fin n → P,
        (if r ((Fin.cons δ₀ δ : Fin (n + 1) → P) 0) then
          S.clusterF (Fin.cons δ₀ δ) else 0) = 0 := by
      intro δ
      rw [Fin.cons_zero, if_neg h]
    rw [tsum_congr hval, tsum_zero]

open Classical in
/-- FV (5.29): the series of clusters pinned by any root predicate `r` is
bounded by the corresponding activity row sum. -/
theorem kp_pinned_bound (hKP : S.KPCondition) (r : P → Prop) {eps : ℝ≥0∞}
    (hrow : (∑' γ : P,
        if r γ then S.W γ * ENNReal.ofReal (Real.exp (S.a γ)) else 0) ≤ eps) :
    (∑' n : ℕ, (((n + 1).factorial : ℝ≥0∞))⁻¹ *
        ∑' ρ : Fin (n + 1) → P,
          (if ∃ j, r (ρ j) then S.clusterF ρ else 0)) ≤ eps := by
  -- pin the root at coordinate 0
  have hpin : ∀ n : ℕ,
      (∑' ρ : Fin (n + 1) → P, (if ∃ j, r (ρ j) then S.clusterF ρ else 0))
        ≤ ((n : ℝ≥0∞) + 1) *
            ∑' ρ : Fin (n + 1) → P, (if r (ρ 0) then S.clusterF ρ else 0) := by
    intro n
    have hle : ∀ ρ : Fin (n + 1) → P,
        (if ∃ j, r (ρ j) then S.clusterF ρ else 0)
          ≤ S.clusterF ρ * ∑ j : Fin (n + 1), if r (ρ j) then 1 else 0 := by
      intro ρ
      by_cases h : ∃ j, r (ρ j)
      · rw [if_pos h]
        obtain ⟨j, hj⟩ := h
        conv_lhs => rw [← mul_one (S.clusterF ρ)]
        refine mul_le_mul_left' ?_ _
        calc (1 : ℝ≥0∞) = if r (ρ j) then 1 else 0 := by rw [if_pos hj]
          _ ≤ ∑ j' : Fin (n + 1), if r (ρ j') then 1 else 0 :=
            Finset.single_le_sum (f := fun j' => if r (ρ j') then (1 : ℝ≥0∞) else 0)
              (fun _ _ => bot_le) (Finset.mem_univ j)
      · rw [if_neg h]
        exact bot_le
    calc (∑' ρ : Fin (n + 1) → P, (if ∃ j, r (ρ j) then S.clusterF ρ else 0))
        ≤ ∑' ρ : Fin (n + 1) → P,
            S.clusterF ρ * ∑ j : Fin (n + 1), if r (ρ j) then 1 else 0 :=
          ENNReal.tsum_le_tsum hle
      _ = ((n : ℝ≥0∞) + 1) *
            ∑' ρ : Fin (n + 1) → P, (if r (ρ 0) then S.clusterF ρ else 0) := by
          rw [tsum_sum_pin_eq_card_mul_pinned (F := fun ρ => S.clusterF ρ)
            (fun σ ρ => S.clusterF_comp_perm ρ σ) r]
  calc (∑' n : ℕ, (((n + 1).factorial : ℝ≥0∞))⁻¹ *
        ∑' ρ : Fin (n + 1) → P, (if ∃ j, r (ρ j) then S.clusterF ρ else 0))
      ≤ ∑' n : ℕ, (((n + 1).factorial : ℝ≥0∞))⁻¹ * (((n : ℝ≥0∞) + 1) *
          ∑' ρ : Fin (n + 1) → P, (if r (ρ 0) then S.clusterF ρ else 0)) :=
        ENNReal.tsum_le_tsum fun n => mul_le_mul_left' (hpin n) _
    _ = ∑' n : ℕ, ∑' δ₀ : P, (if r δ₀ then
          S.W δ₀ * S.rootedVal n δ₀ else 0) := by
        refine tsum_congr fun n => ?_
        rw [S.tsum_ite_clusterF_cons r n]
        have hpull : ∀ δ₀ : P,
            (if r δ₀ then
              S.W δ₀ * ((n.factorial : ℝ≥0∞) * S.rootedVal n δ₀) else 0)
              = (n.factorial : ℝ≥0∞) *
                  (if r δ₀ then S.W δ₀ * S.rootedVal n δ₀ else 0) := by
          intro δ₀
          by_cases h : r δ₀
          · rw [if_pos h, if_pos h]
            ring
          · rw [if_neg h, if_neg h, mul_zero]
        rw [tsum_congr hpull, ENNReal.tsum_mul_left, ← mul_assoc, ← mul_assoc]
        have hfac : (((n + 1).factorial : ℝ≥0∞))⁻¹ * ((n : ℝ≥0∞) + 1) *
            (n.factorial : ℝ≥0∞) = 1 := by
          have h1 : ((n + 1).factorial : ℝ≥0∞)
              = ((n : ℝ≥0∞) + 1) * (n.factorial : ℝ≥0∞) := by
            rw [Nat.factorial_succ]
            push_cast
            ring
          rw [mul_assoc, ← h1]
          refine ENNReal.inv_mul_cancel ?_ ?_
          · exact_mod_cast (n + 1).factorial_pos.ne'
          · exact ENNReal.natCast_ne_top _
        rw [hfac, one_mul]
    _ = ∑' δ₀ : P, (if r δ₀ then
          S.W δ₀ * ∑' n : ℕ, S.rootedVal n δ₀ else 0) := by
        rw [ENNReal.tsum_comm]
        refine tsum_congr fun δ₀ => ?_
        by_cases h : r δ₀
        · simp only [if_pos h]
          rw [ENNReal.tsum_mul_left]
        · simp only [if_neg h]
          rw [tsum_zero]
    _ ≤ ∑' δ₀ : P, (if r δ₀ then
          S.W δ₀ * ENNReal.ofReal (Real.exp (S.a δ₀)) else 0) := by
        refine ENNReal.tsum_le_tsum fun δ₀ => ?_
        by_cases h : r δ₀
        · rw [if_pos h, if_pos h]
          exact mul_le_mul_left' (S.kp_rooted_bound hKP δ₀) _
        · rw [if_neg h, if_neg h]
    _ ≤ eps := hrow

open Classical in
/-- The unrooted cluster series is bounded by the total activity sum. -/
theorem kp_total_bound (hKP : S.KPCondition) {eps : ℝ≥0∞}
    (htot : (∑' γ : P, S.W γ * ENNReal.ofReal (Real.exp (S.a γ))) ≤ eps) :
    (∑' n : ℕ, (((n + 1).factorial : ℝ≥0∞))⁻¹ *
        ∑' ρ : Fin (n + 1) → P, S.clusterF ρ) ≤ eps := by
  have h := S.kp_pinned_bound hKP (fun _ => True) (eps := eps) (by simpa using htot)
  refine le_trans (le_of_eq ?_) h
  refine tsum_congr fun n => ?_
  congr 1
  refine tsum_congr fun ρ => ?_
  rw [if_pos ⟨0, trivial⟩]

end PolymerSystem

end PolymerKP
