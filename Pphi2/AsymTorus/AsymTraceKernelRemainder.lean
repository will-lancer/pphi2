/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.AsymTorus.AsymTraceBridge
import Pphi2.GeneralResults.HilbertSchmidt

/-!
# The normalized transfer-kernel remainder

This file identifies the kernel of the ground-orthogonal part of a normalized
asymmetric transfer power.  Write `Omega` for the unit ground vector, `lambda0`
for the top eigenvalue, and `T_hat = lambda0^-1 T`.  The normalized remainder is

`R_hat_m(x,y) = lambda0^(-(m+1)) kPow_m(x,y) - Omega(x) Omega(y)`.

Its integral operator is exactly

`T_hat^(m+1) - |Omega><Omega|`.

The identity separates the two analytic inputs used by the periodic trace
bridge.  The spectral gap bounds the operator norm of this remainder.
Parseval (`hs_basis_norm_sq_tsum_eq` / `_le`) rearranges the finite-lattice
basis sum into the same `L2(volume x volume)` kernel mass already used for
`MemLp`; it is not a uniform envelope.  The model-specific obligation remains
the coupled weighted IUC bound `|R| ≤ C η |Ω||Ω|` under `(Ns : ℝ) * a = Ls`.
-/

open MeasureTheory

namespace Pphi2

variable {Nt Ns : ℕ} [NeZero Nt] [NeZero Ns]

/-- The kernel of the `(m+1)`-st power of the normalized transfer operator. -/
noncomputable def asymNormalizedTransferKernelPower
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (m : ℕ) (x y : SpatialField Ns) : ℝ :=
  (asymTransferGroundEigenvalue Nt Ns P a mass ha hmass ^ (m + 1))⁻¹ *
    (asymTransferSystem Nt Ns P a mass ha hmass).kPow m x y

/-- The normalized transfer kernel with its rank-one ground part removed. -/
noncomputable def asymNormalizedTransferKernelRemainder
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (m : ℕ) (x y : SpatialField Ns) : ℝ :=
  asymNormalizedTransferKernelPower P a mass ha hmass m x y -
    (asymGroundVector Nt Ns P a mass ha hmass) x *
      (asymGroundVector Nt Ns P a mass ha hmass) y

/-! ## Coupled weighted remainder from a relative IUC estimate -/

/-- The algebraic step from a multiplicative relative-kernel estimate to a
ground-weighted remainder estimate. -/
theorem abs_sub_ground_product_le_of_relative_error
    {K OmegaX OmegaY delta C eta : ℝ}
    (hK : K = (1 + delta) * OmegaX * OmegaY)
    (hdelta : |delta| ≤ C * eta) :
    |K - OmegaX * OmegaY| ≤ C * eta * |OmegaX| * |OmegaY| := by
  rw [hK]
  calc
    |(1 + delta) * OmegaX * OmegaY - OmegaX * OmegaY| =
        |delta * OmegaX * OmegaY| := by
      congr 1
      ring
    _ = |delta| * |OmegaX| * |OmegaY| := by
      simp only [abs_mul]
    _ ≤ C * eta * |OmegaX| * |OmegaY| :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hdelta (abs_nonneg OmegaX))
        (abs_nonneg OmegaY)

/-- A relative IUC expansion for the normalized Wick-interacting transfer
kernel gives both the product-measure weighted remainder bound and the
separate diagonal bound.  The diagonal premise is independent: a
product-measure almost-everywhere estimate cannot be restricted to the
product-null diagonal. -/
theorem asymNormalizedTransferKernelRemainder_weighted_of_relative_IUC
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (m : ℕ) (C eta : ℝ)
    (hrelative : ∀ᵐ p : SpatialField Ns × SpatialField Ns
        ∂((volume : Measure (SpatialField Ns)).prod volume),
      ∃ delta : ℝ,
        asymNormalizedTransferKernelPower
            (Nt := Nt) (Ns := Ns) P a mass ha hmass m p.1 p.2 =
          (1 + delta) *
            asymGroundVector Nt Ns P a mass ha hmass p.1 *
            asymGroundVector Nt Ns P a mass ha hmass p.2 ∧
        |delta| ≤ C * eta)
    (hrelative_diag : ∀ᵐ x : SpatialField Ns ∂volume,
      ∃ delta : ℝ,
        asymNormalizedTransferKernelPower
            (Nt := Nt) (Ns := Ns) P a mass ha hmass m x x =
          (1 + delta) *
            asymGroundVector Nt Ns P a mass ha hmass x *
            asymGroundVector Nt Ns P a mass ha hmass x ∧
        |delta| ≤ C * eta) :
    (∀ᵐ p : SpatialField Ns × SpatialField Ns
        ∂((volume : Measure (SpatialField Ns)).prod volume),
      |asymNormalizedTransferKernelRemainder
          (Nt := Nt) (Ns := Ns) P a mass ha hmass m p.1 p.2| ≤
        C * eta *
          |asymGroundVector Nt Ns P a mass ha hmass p.1| *
          |asymGroundVector Nt Ns P a mass ha hmass p.2|) ∧
    (∀ᵐ x : SpatialField Ns ∂volume,
      |asymNormalizedTransferKernelRemainder
          (Nt := Nt) (Ns := Ns) P a mass ha hmass m x x| ≤
        C * eta * (asymGroundVector Nt Ns P a mass ha hmass x) ^ 2) := by
  constructor
  · filter_upwards [hrelative] with p hp
    obtain ⟨delta, hK, hdelta⟩ := hp
    simpa only [asymNormalizedTransferKernelRemainder] using
      abs_sub_ground_product_le_of_relative_error hK hdelta
  · filter_upwards [hrelative_diag] with x hx
    obtain ⟨delta, hK, hdelta⟩ := hx
    have hpair := abs_sub_ground_product_le_of_relative_error hK hdelta
    calc
      |asymNormalizedTransferKernelRemainder
          (Nt := Nt) (Ns := Ns) P a mass ha hmass m x x| ≤
          C * eta *
            |asymGroundVector Nt Ns P a mass ha hmass x| *
            |asymGroundVector Nt Ns P a mass ha hmass x| := by
        simpa only [asymNormalizedTransferKernelRemainder] using hpair
      _ = C * eta *
          |asymGroundVector Nt Ns P a mass ha hmass x| ^ 2 := by ring
      _ = C * eta *
          (asymGroundVector Nt Ns P a mass ha hmass x) ^ 2 := by
        rw [sq_abs]

/-- Coupled fixed-circumference weighted remainder theorem with the remaining
Glimm--Jaffe/cluster relative-IUC uniformity exposed as an ordinary theorem
hypothesis.  The physical smoothing window, finite-period fit, UV cutoff, and
`Ns * a = Ls` scaling remain in the conclusion.  This theorem does not prove
the relative-IUC hypothesis and does not construct the finite trace data. -/
omit [NeZero Nt] [NeZero Ns] in
theorem asymNormalizedTransferKernelRemainder_weighted_fixedLs_of_relative_IUC
    (P : InteractionPolynomial) (mass Ls : ℝ)
    (hmass : 0 < mass) (hLs : 0 < Ls)
    (tau0 cutoff C eta : ℝ)
    (htau0 : 0 < tau0) (hcutoff : 0 < cutoff)
    (hC : 0 ≤ C) (heta : 0 ≤ eta)
    (hrelative :
      ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (ha : 0 < a),
        (Ns : ℝ) * a = Ls → a ≤ cutoff →
        2 * tau0 ≤ (Nt : ℝ) * a →
      ∀ m : ℕ, tau0 ≤ ((m + 1 : ℕ) : ℝ) * a → m + 1 ≤ Nt →
        (∀ᵐ p : SpatialField Ns × SpatialField Ns
            ∂((volume : Measure (SpatialField Ns)).prod volume),
          ∃ delta : ℝ,
            asymNormalizedTransferKernelPower
                (Nt := Nt) (Ns := Ns) P a mass ha hmass m p.1 p.2 =
              (1 + delta) *
                asymGroundVector Nt Ns P a mass ha hmass p.1 *
                asymGroundVector Nt Ns P a mass ha hmass p.2 ∧
            |delta| ≤ C * eta) ∧
        (∀ᵐ x : SpatialField Ns ∂volume,
          ∃ delta : ℝ,
            asymNormalizedTransferKernelPower
                (Nt := Nt) (Ns := Ns) P a mass ha hmass m x x =
              (1 + delta) *
                asymGroundVector Nt Ns P a mass ha hmass x *
                asymGroundVector Nt Ns P a mass ha hmass x ∧
            |delta| ≤ C * eta)) :
    ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (ha : 0 < a),
      (Ns : ℝ) * a = Ls → a ≤ cutoff →
      2 * tau0 ≤ (Nt : ℝ) * a →
    ∀ m : ℕ, tau0 ≤ ((m + 1 : ℕ) : ℝ) * a → m + 1 ≤ Nt →
      (∀ᵐ p : SpatialField Ns × SpatialField Ns
          ∂((volume : Measure (SpatialField Ns)).prod volume),
        |asymNormalizedTransferKernelRemainder
            (Nt := Nt) (Ns := Ns) P a mass ha hmass m p.1 p.2| ≤
          C * eta *
            |asymGroundVector Nt Ns P a mass ha hmass p.1| *
            |asymGroundVector Nt Ns P a mass ha hmass p.2|) ∧
      (∀ᵐ x : SpatialField Ns ∂volume,
        |asymNormalizedTransferKernelRemainder
            (Nt := Nt) (Ns := Ns) P a mass ha hmass m x x| ≤
          C * eta * (asymGroundVector Nt Ns P a mass ha hmass x) ^ 2) := by
  intro Nt Ns _ _ a ha hscale hcut hperiod m hphysical hfit
  exact asymNormalizedTransferKernelRemainder_weighted_of_relative_IUC
    (Nt := Nt) (Ns := Ns) P a mass ha hmass m C eta
    (hrelative Nt Ns a ha hscale hcut hperiod m hphysical hfit).1
    (hrelative Nt Ns a ha hscale hcut hperiod m hphysical hfit).2

/-! ## Finite-lattice square integrability -/

/-- The squared `L2` mass of the one-slice transfer weight. -/
noncomputable def asymTransferWeightSqMass
    (P : InteractionPolynomial) (a mass : ℝ) : ℝ :=
  ∫ x : SpatialField Ns, asymTransferWeight Nt Ns P a mass x ^ 2 ∂volume

theorem asymTransferWeightSqMass_nonneg
    (P : InteractionPolynomial) (a mass : ℝ) :
    0 ≤ asymTransferWeightSqMass (Nt := Nt) (Ns := Ns) P a mass :=
  integral_nonneg fun _ => sq_nonneg _

private theorem transferGaussian_le_one_traceKernel (x : SpatialField Ns) :
    transferGaussian Ns x ≤ 1 := by
  simpa [Real.norm_eq_abs, abs_of_pos (transferGaussian_pos Ns x)] using
    transferGaussian_norm_le_one Ns x

/-- The one-step transfer kernel is bounded by the product of its endpoint
weights. -/
theorem asymTransferKernel_le_weight_product
    (P : InteractionPolynomial) (a mass : ℝ) (x y : SpatialField Ns) :
    asymTransferKernel Nt Ns P a mass x y ≤
      asymTransferWeight Nt Ns P a mass x *
        asymTransferWeight Nt Ns P a mass y := by
  unfold asymTransferKernel
  have hx := (asymTransferWeight_pos Nt Ns P a mass x).le
  have hy := (asymTransferWeight_pos Nt Ns P a mass y).le
  have hG := transferGaussian_le_one_traceKernel (Ns := Ns) (x - y)
  calc
    asymTransferWeight Nt Ns P a mass x * transferGaussian Ns (x - y) *
          asymTransferWeight Nt Ns P a mass y
        ≤ asymTransferWeight Nt Ns P a mass x * 1 *
          asymTransferWeight Nt Ns P a mass y := by
            gcongr
    _ = _ := by ring

/-- A product-weight bound for every iterated transfer kernel. -/
theorem asymTransferKernel_kPow_le_weight_product
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (m : ℕ) (x y : SpatialField Ns) :
    (asymTransferSystem Nt Ns P a mass ha hmass).kPow m x y ≤
      asymTransferWeightSqMass (Nt := Nt) (Ns := Ns) P a mass ^ m *
        asymTransferWeight Nt Ns P a mass x *
        asymTransferWeight Nt Ns P a mass y := by
  let Ts := asymTransferSystem Nt Ns P a mass ha hmass
  let W := asymTransferWeight Nt Ns P a mass
  have hW_nonneg : ∀ z, 0 ≤ W z :=
    fun z => (asymTransferWeight_pos Nt Ns P a mass z).le
  have hW_sq : Integrable (fun z => W z ^ 2) volume :=
    (asymTransferWeight_memLp_two Nt Ns P a mass ha hmass).integrable_sq
  induction m generalizing y with
  | zero =>
      simp only [pow_zero, one_mul]
      rw [TransferSystem.kPow_zero]
      exact asymTransferKernel_le_weight_product (Nt := Nt) (Ns := Ns) P a mass x y
  | succ m ih =>
      rw [TransferSystem.kPow_succ]
      have hpoint : ∀ z, Ts.kPow m x z * Ts.k z y ≤
          (asymTransferWeightSqMass (Nt := Nt) (Ns := Ns) P a mass ^ m * W x) *
            (W z ^ 2 * W y) := by
        intro z
        have hkpow := ih z
        have hk : Ts.k z y ≤ W z * W y :=
          asymTransferKernel_le_weight_product
            (Nt := Nt) (Ns := Ns) P a mass z y
        have hk_nonneg : 0 ≤ Ts.k z y := Ts.k_nonneg z y
        have hdom_nonneg :
            0 ≤ asymTransferWeightSqMass (Nt := Nt) (Ns := Ns) P a mass ^ m *
              W x * W z :=
          mul_nonneg
            (mul_nonneg
              (pow_nonneg
                (asymTransferWeightSqMass_nonneg
                  (Nt := Nt) (Ns := Ns) P a mass) m)
              (hW_nonneg x))
            (hW_nonneg z)
        calc
          Ts.kPow m x z * Ts.k z y
              ≤ (asymTransferWeightSqMass (Nt := Nt) (Ns := Ns) P a mass ^ m *
                    W x * W z) * (W z * W y) :=
                mul_le_mul hkpow hk hk_nonneg hdom_nonneg
          _ = (asymTransferWeightSqMass (Nt := Nt) (Ns := Ns) P a mass ^ m * W x) *
                (W z ^ 2 * W y) := by ring
      have hdom_int : Integrable
          (fun z =>
            (asymTransferWeightSqMass (Nt := Nt) (Ns := Ns) P a mass ^ m * W x) *
              (W z ^ 2 * W y)) volume :=
        (hW_sq.mul_const _).const_mul _
      calc
        ∫ z, Ts.kPow m x z * Ts.k z y ∂volume
            ≤ ∫ z,
                (asymTransferWeightSqMass (Nt := Nt) (Ns := Ns) P a mass ^ m * W x) *
                  (W z ^ 2 * W y) ∂volume :=
              integral_mono_of_nonneg
                (.of_forall fun z => mul_nonneg (Ts.kPow_nonneg m x z) (Ts.k_nonneg z y))
                hdom_int (.of_forall hpoint)
        _ = (asymTransferWeightSqMass (Nt := Nt) (Ns := Ns) P a mass ^ m * W x * W y) *
              ∫ z, W z ^ 2 ∂volume := by
                rw [← integral_const_mul]
                congr 1
                ext z
                ring
        _ = asymTransferWeightSqMass (Nt := Nt) (Ns := Ns) P a mass ^ (m + 1) *
              W x * W y := by
                change
                  (asymTransferWeightSqMass (Nt := Nt) (Ns := Ns) P a mass ^ m * W x * W y) *
                    asymTransferWeightSqMass (Nt := Nt) (Ns := Ns) P a mass = _
                ring

/-- Joint measurability of every iterated transfer kernel. -/
theorem asymTransferKernel_kPow_measurable
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (m : ℕ) :
    Measurable (Function.uncurry
      ((asymTransferSystem Nt Ns P a mass ha hmass).kPow m)) := by
  let Ts := asymTransferSystem Nt Ns P a mass ha hmass
  induction m with
  | zero =>
      simpa only [TransferSystem.kPow_zero, Ts] using Ts.k_meas
  | succ m ih =>
      have hleft : Measurable
          (fun q : (SpatialField Ns × SpatialField Ns) × SpatialField Ns =>
            Ts.kPow m q.1.1 q.2) :=
        ih.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
      have hright : Measurable
          (fun q : (SpatialField Ns × SpatialField Ns) × SpatialField Ns =>
            Ts.k q.2 q.1.2) :=
        Ts.k_meas.comp
          (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
      have hint : Measurable
          (fun q : (SpatialField Ns × SpatialField Ns) × SpatialField Ns =>
            Ts.kPow m q.1.1 q.2 * Ts.k q.2 q.1.2) :=
        hleft.mul hright
      have hparam : Measurable
          (fun p : SpatialField Ns × SpatialField Ns =>
            ∫ z, Ts.kPow m p.1 z * Ts.k z p.2 ∂volume) :=
        (hint.stronglyMeasurable.integral_prod_right').measurable
      simpa only [Function.uncurry_apply_pair, TransferSystem.kPow_succ, Ts] using hparam

/-- Every finite-lattice iterated transfer kernel belongs to
`L2(volume x volume)`.  Its bound may depend on all lattice parameters. -/
theorem asymTransferKernel_kPow_memLp_two
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (m : ℕ) :
    MemLp
      (Function.uncurry ((asymTransferSystem Nt Ns P a mass ha hmass).kPow m))
      2 ((volume : Measure (SpatialField Ns)).prod volume) := by
  let Ts := asymTransferSystem Nt Ns P a mass ha hmass
  let W := asymTransferWeight Nt Ns P a mass
  let C := asymTransferWeightSqMass (Nt := Nt) (Ns := Ns) P a mass ^ m
  have hC_nonneg : 0 ≤ C :=
    pow_nonneg
      (asymTransferWeightSqMass_nonneg (Nt := Nt) (Ns := Ns) P a mass) m
  have hW_nonneg : ∀ x, 0 ≤ W x :=
    fun x => (asymTransferWeight_pos Nt Ns P a mass x).le
  have hW_sq : Integrable (fun x => W x ^ 2) volume :=
    (asymTransferWeight_memLp_two Nt Ns P a mass ha hmass).integrable_sq
  have hbase : Integrable
      (fun p : SpatialField Ns × SpatialField Ns => W p.1 ^ 2 * W p.2 ^ 2)
      (volume.prod volume) :=
    hW_sq.mul_prod hW_sq
  have hdom : Integrable
      (fun p : SpatialField Ns × SpatialField Ns => (C * W p.1 * W p.2) ^ 2)
      (volume.prod volume) := by
    refine (hbase.const_mul (C ^ 2)).congr (.of_forall fun p => ?_)
    ring
  have hk_meas : Measurable (Function.uncurry (Ts.kPow m)) := by
    simpa only [Ts] using
      asymTransferKernel_kPow_measurable
        (Nt := Nt) (Ns := Ns) P a mass ha hmass m
  refine (memLp_two_iff_integrable_sq hk_meas.aestronglyMeasurable).2 ?_
  refine hdom.mono' (hk_meas.pow_const 2).aestronglyMeasurable (.of_forall fun p => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hnon : 0 ≤ Ts.kPow m p.1 p.2 := Ts.kPow_nonneg m p.1 p.2
  have hle : Ts.kPow m p.1 p.2 ≤ C * W p.1 * W p.2 := by
    simpa only [Ts, W, C] using
      asymTransferKernel_kPow_le_weight_product
        (Nt := Nt) (Ns := Ns) P a mass ha hmass m p.1 p.2
  exact pow_le_pow_left₀ hnon hle 2

/-- The diagonal of every finite-lattice transfer-kernel power is integrable.
This statement carries a lattice-dependent product-weight bound. -/
theorem asymTransferKernel_kPow_diag_integrable
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (m : ℕ) :
    Integrable
      (fun x : SpatialField Ns =>
        (asymTransferSystem Nt Ns P a mass ha hmass).kPow m x x)
      volume := by
  let Ts := asymTransferSystem Nt Ns P a mass ha hmass
  let W := asymTransferWeight Nt Ns P a mass
  let C := asymTransferWeightSqMass (Nt := Nt) (Ns := Ns) P a mass ^ m
  have hW_sq : Integrable (fun x => W x ^ 2) volume :=
    (asymTransferWeight_memLp_two Nt Ns P a mass ha hmass).integrable_sq
  have hdom : Integrable (fun x => C * W x * W x) volume := by
    refine (hW_sq.const_mul C).congr (.of_forall fun x => ?_)
    ring
  have hdiag_meas : Measurable (fun x : SpatialField Ns => Ts.kPow m x x) :=
    (asymTransferKernel_kPow_measurable
      (Nt := Nt) (Ns := Ns) P a mass ha hmass m).comp
        (measurable_id.prodMk measurable_id)
  refine hdom.mono' hdiag_meas.aestronglyMeasurable (.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Ts.kPow_nonneg m x x)]
  simpa only [Ts, W, C] using
    asymTransferKernel_kPow_le_weight_product
      (Nt := Nt) (Ns := Ns) P a mass ha hmass m x x

/-- The rank-one ground kernel belongs to `L2(volume x volume)`. -/
theorem asymGroundVector_mul_groundVector_memLp_two
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    MemLp
      (fun p : SpatialField Ns × SpatialField Ns =>
        (asymGroundVector Nt Ns P a mass ha hmass) p.1 *
          (asymGroundVector Nt Ns P a mass ha hmass) p.2)
      2 ((volume : Measure (SpatialField Ns)).prod volume) := by
  let Omega := asymGroundVector Nt Ns P a mass ha hmass
  have hOmega_sq : Integrable (fun x => Omega x ^ 2) volume :=
    (Lp.memLp Omega).integrable_sq
  have hprod_sq : Integrable
      (fun p : SpatialField Ns × SpatialField Ns =>
        (Omega p.1 * Omega p.2) ^ 2) (volume.prod volume) := by
    refine (hOmega_sq.mul_prod hOmega_sq).congr (.of_forall fun p => ?_)
    ring
  have hprod_meas : AEStronglyMeasurable
      (fun p : SpatialField Ns × SpatialField Ns => Omega p.1 * Omega p.2)
      (volume.prod volume) :=
    (Lp.aestronglyMeasurable Omega).comp_fst.mul
      (Lp.aestronglyMeasurable Omega).comp_snd
  exact (memLp_two_iff_integrable_sq hprod_meas).2 hprod_sq

/-- Every finite-lattice normalized remainder kernel is square-integrable. -/
theorem asymNormalizedTransferKernelRemainder_memLp_two
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (m : ℕ) :
    MemLp
      (Function.uncurry
        (asymNormalizedTransferKernelRemainder
          (Nt := Nt) (Ns := Ns) P a mass ha hmass m))
      2 ((volume : Measure (SpatialField Ns)).prod volume) := by
  have hk :=
    (asymTransferKernel_kPow_memLp_two
      (Nt := Nt) (Ns := Ns) P a mass ha hmass m).const_mul
      (asymTransferGroundEigenvalue Nt Ns P a mass ha hmass ^ (m + 1))⁻¹
  have hground :=
    asymGroundVector_mul_groundVector_memLp_two
      (Nt := Nt) (Ns := Ns) P a mass ha hmass
  simpa only [Function.uncurry_apply_pair, asymNormalizedTransferKernelRemainder,
    asymNormalizedTransferKernelPower, Pi.sub_apply] using hk.sub hground

/-- The double ground-orthogonal kernel insertion is controlled by the two
product-space `L2` norms.  The second kernel is transposed by the product-measure
swap, which preserves its `L2` norm. -/
theorem asymNormalizedTransferKernelRemainder_double_insertion_norm_le
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (m n : ℕ) (A B : SpatialField Ns → ℂ) (BF BG : ℝ)
    (hBF : 0 ≤ BF) (hBG : 0 ≤ BG)
    (hA : ∀ x, ‖A x‖ ≤ BF) (hB : ∀ x, ‖B x‖ ≤ BG)
    (hRm : MemLp
      (Function.uncurry
        (asymNormalizedTransferKernelRemainder
          (Nt := Nt) (Ns := Ns) P a mass ha hmass m))
      2 ((volume : Measure (SpatialField Ns)).prod volume))
    (hRn : MemLp
      (Function.uncurry
        (asymNormalizedTransferKernelRemainder
          (Nt := Nt) (Ns := Ns) P a mass ha hmass n))
      2 ((volume : Measure (SpatialField Ns)).prod volume)) :
    ‖∫ p : SpatialField Ns × SpatialField Ns,
        A p.1 *
          (asymNormalizedTransferKernelRemainder
            (Nt := Nt) (Ns := Ns) P a mass ha hmass m p.1 p.2 : ℂ) *
          B p.2 *
          (asymNormalizedTransferKernelRemainder
            (Nt := Nt) (Ns := Ns) P a mass ha hmass n p.2 p.1 : ℂ)
        ∂((volume : Measure (SpatialField Ns)).prod volume)‖ ≤
      BF * BG *
        ‖hRm.toLp
          (Function.uncurry
            (asymNormalizedTransferKernelRemainder
              (Nt := Nt) (Ns := Ns) P a mass ha hmass m))‖ *
        ‖hRn.toLp
          (Function.uncurry
            (asymNormalizedTransferKernelRemainder
              (Nt := Nt) (Ns := Ns) P a mass ha hmass n))‖ := by
  let Rm := asymNormalizedTransferKernelRemainder
    (Nt := Nt) (Ns := Ns) P a mass ha hmass m
  let Rn := asymNormalizedTransferKernelRemainder
    (Nt := Nt) (Ns := Ns) P a mass ha hmass n
  let μ2 := (volume : Measure (SpatialField Ns)).prod volume
  have hRnT : MemLp
      (Function.uncurry Rn ∘
        (Prod.swap : SpatialField Ns × SpatialField Ns →
          SpatialField Ns × SpatialField Ns)) 2 μ2 :=
    GeneralResults.memLp_two_prod_swap (Function.uncurry Rn) hRn
  have hmain := GeneralResults.norm_integral_complex_four_mul_le_toLp
    μ2 (fun p => A p.1) (fun p => B p.2)
      (Function.uncurry Rm)
      (Function.uncurry Rn ∘
        (Prod.swap : SpatialField Ns × SpatialField Ns →
          SpatialField Ns × SpatialField Ns))
      BF BG hBF hBG (fun p => hA p.1) (fun p => hB p.2) hRm hRnT
  have hswap := GeneralResults.norm_toLp_two_prod_swap
    (Function.uncurry Rn) hRn
  rw [hswap] at hmain
  simpa only [Rm, Rn, μ2, Function.comp_apply, Function.uncurry_apply_pair,
    Prod.fst_swap, Prod.snd_swap] using hmain

/-- The diagonal of the normalized transfer-kernel power is integrable at
every finite lattice. -/
theorem asymNormalizedTransferKernelPower_diag_integrable
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (m : ℕ) :
    Integrable
      (fun x : SpatialField Ns =>
        asymNormalizedTransferKernelPower
          (Nt := Nt) (Ns := Ns) P a mass ha hmass m x x)
      volume := by
  simpa only [asymNormalizedTransferKernelPower] using
    (asymTransferKernel_kPow_diag_integrable
      (Nt := Nt) (Ns := Ns) P a mass ha hmass m).const_mul
        (asymTransferGroundEigenvalue Nt Ns P a mass ha hmass ^ (m + 1))⁻¹

/-- The normalized remainder also has an integrable diagonal at every finite
lattice.  This does not follow from product-space `L2` alone; it uses the
explicit product-weight kernel bound. -/
theorem asymNormalizedTransferKernelRemainder_diag_integrable
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (m : ℕ) :
    Integrable
      (fun x : SpatialField Ns =>
        asymNormalizedTransferKernelRemainder
          (Nt := Nt) (Ns := Ns) P a mass ha hmass m x x)
      volume := by
  have hpower := asymNormalizedTransferKernelPower_diag_integrable
    (Nt := Nt) (Ns := Ns) P a mass ha hmass m
  have hground : Integrable (fun x : SpatialField Ns =>
      (asymGroundVector Nt Ns P a mass ha hmass x) ^ 2) volume :=
    (Lp.memLp (asymGroundVector Nt Ns P a mass ha hmass)).integrable_sq
  simpa only [asymNormalizedTransferKernelRemainder, pow_two] using
    hpower.sub hground

/-- The diagonal integral of the rank-one ground kernel is one. -/
theorem integral_asymGroundVector_sq_eq_one
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    ∫ x : SpatialField Ns,
        (asymGroundVector Nt Ns P a mass ha hmass x) ^ 2 ∂volume = 1 := by
  let Omega := asymGroundVector Nt Ns P a mass ha hmass
  calc
    ∫ x : SpatialField Ns, Omega x ^ 2 ∂volume =
        @inner ℝ _ _ Omega Omega := by
      rw [MeasureTheory.L2.inner_def]
      simp only [Real.inner_apply, pow_two]
    _ = ‖Omega‖ ^ 2 := real_inner_self_eq_norm_sq
    _ = 1 := by
      rw [asymGroundVector_norm_eq_one]
      norm_num

/-- The normalized diagonal trace is the ground contribution `1` plus the
diagonal trace of the ground-orthogonal remainder. -/
theorem integral_asymNormalizedTransferKernelPower_diag_eq_one_add_remainder
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (m : ℕ) :
    (∫ x : SpatialField Ns,
        asymNormalizedTransferKernelPower
          (Nt := Nt) (Ns := Ns) P a mass ha hmass m x x ∂volume) =
      1 +
        ∫ x : SpatialField Ns,
          asymNormalizedTransferKernelRemainder
            (Nt := Nt) (Ns := Ns) P a mass ha hmass m x x ∂volume := by
  let Omega := asymGroundVector Nt Ns P a mass ha hmass
  let K := asymNormalizedTransferKernelPower
    (Nt := Nt) (Ns := Ns) P a mass ha hmass m
  let R := asymNormalizedTransferKernelRemainder
    (Nt := Nt) (Ns := Ns) P a mass ha hmass m
  have hR := asymNormalizedTransferKernelRemainder_diag_integrable
    (Nt := Nt) (Ns := Ns) P a mass ha hmass m
  have hground : Integrable (fun x : SpatialField Ns => Omega x ^ 2) volume :=
    (Lp.memLp Omega).integrable_sq
  have hground_integral : ∫ x : SpatialField Ns, Omega x ^ 2 ∂volume = 1 := by
    simpa only [Omega] using
      integral_asymGroundVector_sq_eq_one
        (Nt := Nt) (Ns := Ns) P a mass ha hmass
  calc
    ∫ x : SpatialField Ns, K x x ∂volume =
        ∫ x : SpatialField Ns, (R x x + Omega x ^ 2) ∂volume := by
      refine integral_congr_ae (.of_forall fun x => ?_)
      simp only [R, K, asymNormalizedTransferKernelRemainder, pow_two]
      ring
    _ = (∫ x : SpatialField Ns, R x x ∂volume) +
          ∫ x : SpatialField Ns, Omega x ^ 2 ∂volume := by
      rw [integral_add hR hground]
    _ = 1 + ∫ x : SpatialField Ns, R x x ∂volume := by
      rw [hground_integral]
      ring

/-- A weighted diagonal estimate turns directly into a trace-remainder bound.
The substantive input is the almost-everywhere comparison with the normalized
ground density; the kernel facts above supply all integrability obligations. -/
theorem asymNormalizedTransferKernelRemainder_diag_abs_integral_le_of_weighted
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (m : ℕ) (C eta : ℝ)
    (hdiag : ∀ᵐ x : SpatialField Ns ∂volume,
      |asymNormalizedTransferKernelRemainder
          (Nt := Nt) (Ns := Ns) P a mass ha hmass m x x| ≤
        C * eta * (asymGroundVector Nt Ns P a mass ha hmass x) ^ 2) :
    |∫ x : SpatialField Ns,
        asymNormalizedTransferKernelRemainder
          (Nt := Nt) (Ns := Ns) P a mass ha hmass m x x ∂volume| ≤
      C * eta := by
  let Omega := asymGroundVector Nt Ns P a mass ha hmass
  let R := asymNormalizedTransferKernelRemainder
    (Nt := Nt) (Ns := Ns) P a mass ha hmass m
  have hR : Integrable (fun x : SpatialField Ns => R x x) volume := by
    simpa only [R] using
      asymNormalizedTransferKernelRemainder_diag_integrable
        (Nt := Nt) (Ns := Ns) P a mass ha hmass m
  have hground : Integrable (fun x : SpatialField Ns => Omega x ^ 2) volume :=
    (Lp.memLp Omega).integrable_sq
  have hupper : Integrable
      (fun x : SpatialField Ns => C * eta * Omega x ^ 2) volume :=
    hground.const_mul (C * eta)
  calc
    |∫ x : SpatialField Ns, R x x ∂volume| ≤
        ∫ x : SpatialField Ns, |R x x| ∂volume :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x : SpatialField Ns, C * eta * Omega x ^ 2 ∂volume := by
      refine integral_mono_ae hR.abs hupper ?_
      simpa only [R, Omega] using hdiag
    _ = C * eta * ∫ x : SpatialField Ns, Omega x ^ 2 ∂volume := by
      rw [integral_const_mul]
    _ = C * eta := by
      rw [show (∫ x : SpatialField Ns, Omega x ^ 2 ∂volume) = 1 by
        simpa only [Omega] using
          integral_asymGroundVector_sq_eq_one
            (Nt := Nt) (Ns := Ns) P a mass ha hmass]
      ring

/-- The ground-orthogonal part of a normalized transfer power. -/
noncomputable def asymNormalizedTransferRemainderCLM
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (m : ℕ) : L2SpatialField Ns →L[ℝ] L2SpatialField Ns :=
  (asymTransferNormalized Nt Ns P a mass ha hmass) ^ (m + 1) -
    InnerProductSpace.rankOne ℝ
      (asymGroundVector Nt Ns P a mass ha hmass)
      (asymGroundVector Nt Ns P a mass ha hmass)

/-- The normalized transfer fixes the chosen ground vector. -/
theorem asymTransferNormalized_groundVector
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    asymTransferNormalized Nt Ns P a mass ha hmass
        (asymGroundVector Nt Ns P a mass ha hmass) =
      asymGroundVector Nt Ns P a mass ha hmass := by
  unfold asymTransferNormalized
  rw [ContinuousLinearMap.smul_apply, asymTransferOperatorCLM_groundVector,
    smul_smul, inv_mul_cancel₀
      (ne_of_gt (asymTransferGroundEigenvalue_pos Nt Ns P a mass ha hmass)),
    one_smul]

/-- Every normalized transfer power fixes the chosen ground vector. -/
theorem asymTransferNormalized_pow_groundVector
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (n : ℕ) :
    ((asymTransferNormalized Nt Ns P a mass ha hmass) ^ n)
        (asymGroundVector Nt Ns P a mass ha hmass) =
      asymGroundVector Nt Ns P a mass ha hmass := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply, ih,
        asymTransferNormalized_groundVector]

/-- The remainder is the normalized transfer power applied to the centered
input. -/
theorem asymNormalizedTransferRemainderCLM_apply_eq_pow_centered
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (m : ℕ) (f : L2SpatialField Ns) :
    asymNormalizedTransferRemainderCLM
        (Nt := Nt) (Ns := Ns) P a mass ha hmass m f =
      ((asymTransferNormalized Nt Ns P a mass ha hmass) ^ (m + 1))
        (f - (@inner ℝ _ _
          (asymGroundVector Nt Ns P a mass ha hmass) f) •
            asymGroundVector Nt Ns P a mass ha hmass) := by
  unfold asymNormalizedTransferRemainderCLM
  rw [ContinuousLinearMap.sub_apply, InnerProductSpace.rankOne_apply,
    map_sub, map_smul, asymTransferNormalized_pow_groundVector]

/-- A later remainder is obtained by applying the intervening normalized
transfer power to an earlier remainder. -/
theorem asymNormalizedTransferRemainderCLM_add_apply
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (m n : ℕ) (f : L2SpatialField Ns) :
    asymNormalizedTransferRemainderCLM
        (Nt := Nt) (Ns := Ns) P a mass ha hmass (m + n) f =
      ((asymTransferNormalized Nt Ns P a mass ha hmass) ^ n)
        (asymNormalizedTransferRemainderCLM
          (Nt := Nt) (Ns := Ns) P a mass ha hmass m f) := by
  let T := asymTransferNormalized Nt Ns P a mass ha hmass
  let Omega := asymGroundVector Nt Ns P a mass ha hmass
  let centered := f - (@inner ℝ _ _ Omega f) • Omega
  calc
    asymNormalizedTransferRemainderCLM
          (Nt := Nt) (Ns := Ns) P a mass ha hmass (m + n) f =
        (T ^ ((m + n) + 1)) centered := by
      simpa only [T, Omega, centered] using
        asymNormalizedTransferRemainderCLM_apply_eq_pow_centered
          (Nt := Nt) (Ns := Ns) P a mass ha hmass (m + n) f
    _ = (T ^ (n + (m + 1))) centered := by
      congr 2
      omega
    _ = ((T ^ n) * (T ^ (m + 1))) centered := by rw [pow_add]
    _ = (T ^ n) ((T ^ (m + 1)) centered) := by
      rw [ContinuousLinearMap.mul_apply]
    _ = (T ^ n)
          (asymNormalizedTransferRemainderCLM
            (Nt := Nt) (Ns := Ns) P a mass ha hmass m f) := by
      rw [asymNormalizedTransferRemainderCLM_apply_eq_pow_centered]

/-- Once a remainder has been smoothed, every additional transfer step damps
it by the ground-orthogonal gap. -/
theorem asymNormalizedTransferRemainderCLM_add_apply_norm_le
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (gamma : ℝ) (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1)
    (hnorm : ∀ v : L2SpatialField Ns,
      @inner ℝ _ _ (asymGroundVector Nt Ns P a mass ha hmass) v = 0 →
      ‖asymTransferNormalized Nt Ns P a mass ha hmass v‖ ≤ gamma * ‖v‖)
    (m n : ℕ) (f : L2SpatialField Ns) :
    ‖asymNormalizedTransferRemainderCLM
        (Nt := Nt) (Ns := Ns) P a mass ha hmass (m + n) f‖ ≤
      gamma ^ n *
        ‖asymNormalizedTransferRemainderCLM
          (Nt := Nt) (Ns := Ns) P a mass ha hmass m f‖ := by
  let Omega := asymGroundVector Nt Ns P a mass ha hmass
  let G := asymGappedTransfer Nt Ns P a mass ha hmass gamma hgamma0 hgamma1 hnorm
  have hcentered :
      @inner ℝ _ _ Omega (f - (@inner ℝ _ _ Omega f) • Omega) = 0 := by
    rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq,
      asymGroundVector_norm_eq_one]
    ring
  have hperp :
      @inner ℝ _ _ Omega
        (asymNormalizedTransferRemainderCLM
          (Nt := Nt) (Ns := Ns) P a mass ha hmass m f) = 0 := by
    rw [asymNormalizedTransferRemainderCLM_apply_eq_pow_centered]
    exact G.inner_vacuum_T_pow_eq_zero hcentered (m + 1)
  rw [asymNormalizedTransferRemainderCLM_add_apply]
  exact G.norm_T_pow_le hperp n

/-- The normalized kernel power acts as the corresponding normalized transfer
power. -/
theorem asymNormalizedTransferKernelPower_apply
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (m : ℕ) (f : L2SpatialField Ns) :
    (⇑(((asymTransferNormalized Nt Ns P a mass ha hmass) ^ (m + 1)) f) :
        SpatialField Ns → ℝ) =ᵐ[volume]
      fun x => ∫ y, asymNormalizedTransferKernelPower P a mass ha hmass m x y * f y
        ∂volume := by
  let lambda0 := asymTransferGroundEigenvalue Nt Ns P a mass ha hmass
  have hlambda0 : 0 < lambda0 :=
    asymTransferGroundEigenvalue_pos Nt Ns P a mass ha hmass
  have hpow_ne : lambda0 ^ (m + 1) ≠ 0 := pow_ne_zero _ hlambda0.ne'
  have hscale :
      ((asymTransferNormalized Nt Ns P a mass ha hmass) ^ (m + 1)) f =
        (lambda0 ^ (m + 1))⁻¹ •
          ((asymTransferOperatorCLM Nt Ns P a mass ha hmass) ^ (m + 1)) f := by
    rw [asymTransferOperatorCLM_eq_smul_normalized, smul_pow,
      ContinuousLinearMap.smul_apply, smul_smul, inv_mul_cancel₀ hpow_ne, one_smul]
  rw [hscale]
  have hkernel := asymTransferKernel_kPow_apply Nt Ns P a mass ha hmass m f
  filter_upwards [Lp.coeFn_smul (lambda0 ^ (m + 1))⁻¹
      (((asymTransferOperatorCLM Nt Ns P a mass ha hmass) ^ (m + 1)) f), hkernel]
      with x hx hkernel_x
  rw [hx, hkernel_x, ← integral_const_mul]
  refine integral_congr_ae (.of_forall fun y => ?_)
  simp only [asymNormalizedTransferKernelPower, lambda0]
  ring

/-- If the normalized remainder kernel is square-integrable, it represents the
ground-orthogonal remainder operator in standard integral-kernel form. -/
theorem asymNormalizedTransferKernelRemainder_apply_of_memLp
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (m : ℕ)
    (hR : MemLp
      (Function.uncurry
        (asymNormalizedTransferKernelRemainder
          (Nt := Nt) (Ns := Ns) P a mass ha hmass m))
      2 ((volume : Measure (SpatialField Ns)).prod volume))
    (f : L2SpatialField Ns) :
    (⇑(asymNormalizedTransferRemainderCLM
        (Nt := Nt) (Ns := Ns) P a mass ha hmass m f) : SpatialField Ns → ℝ) =ᵐ[volume]
      fun x => ∫ y,
        asymNormalizedTransferKernelRemainder P a mass ha hmass m x y * f y ∂volume := by
  let Omega := asymGroundVector Nt Ns P a mass ha hmass
  let Tpow := (asymTransferNormalized Nt Ns P a mass ha hmass) ^ (m + 1)
  let K := asymNormalizedTransferKernelPower
    (Nt := Nt) (Ns := Ns) P a mass ha hmass m
  let R := asymNormalizedTransferKernelRemainder
    (Nt := Nt) (Ns := Ns) P a mass ha hmass m
  have hT : (⇑(Tpow f) : SpatialField Ns → ℝ) =ᵐ[volume]
      fun x => ∫ y, K x y * f y ∂volume := by
    simpa only [Tpow, K] using
      asymNormalizedTransferKernelPower_apply
        (Nt := Nt) (Ns := Ns) P a mass ha hmass m f
  have hrank :
      (⇑(InnerProductSpace.rankOne ℝ Omega Omega f) : SpatialField Ns → ℝ) =ᵐ[volume]
        fun x => (@inner ℝ _ _ Omega f) * Omega x := by
    rw [InnerProductSpace.rankOne_apply]
    filter_upwards [Lp.coeFn_smul (@inner ℝ _ _ Omega f) Omega] with x hx
    simpa [smul_eq_mul] using hx
  have hsub :
      (⇑(Tpow f - InnerProductSpace.rankOne ℝ Omega Omega f) : SpatialField Ns → ℝ) =ᵐ[volume]
        fun x => (Tpow f) x - (InnerProductSpace.rankOne ℝ Omega Omega f) x := by
    exact Lp.coeFn_sub _ _
  have hinner : @inner ℝ _ _ Omega f = ∫ y, Omega y * f y ∂volume := by
    rw [MeasureTheory.L2.inner_def]
    simp only [Real.inner_apply]
  have hOmega_f : Integrable (fun y => Omega y * f y) volume :=
    (Lp.memLp Omega).integrable_mul (Lp.memLp f)
  have hR_sq : Integrable (fun p : SpatialField Ns × SpatialField Ns =>
      Function.uncurry R p ^ 2) (volume.prod volume) := by
    simpa only [R] using hR.integrable_sq
  have hR_meas : AEStronglyMeasurable (Function.uncurry R)
      ((volume : Measure (SpatialField Ns)).prod volume) := by
    simpa only [R] using hR.aestronglyMeasurable
  change (⇑(Tpow f - InnerProductSpace.rankOne ℝ Omega Omega f) :
      SpatialField Ns → ℝ) =ᵐ[volume]
    fun x => ∫ y, R x y * f y ∂volume
  filter_upwards [hT, hrank, hsub, hR_sq.prod_right_ae, hR_meas.prodMk_left]
      with x hTx hrankx hsubx hR_sq_x hR_meas_x
  have hR_mem_x : MemLp (R x) 2 (volume : Measure (SpatialField Ns)) :=
    (memLp_two_iff_integrable_sq hR_meas_x).2 hR_sq_x
  have hR_f : Integrable (fun y => R x y * f y) volume :=
    hR_mem_x.integrable_mul (Lp.memLp f)
  have hground_f : Integrable (fun y => Omega x * (Omega y * f y)) volume :=
    hOmega_f.const_mul _
  calc
    (Tpow f - InnerProductSpace.rankOne ℝ Omega Omega f : L2SpatialField Ns) x
        = (Tpow f) x - (InnerProductSpace.rankOne ℝ Omega Omega f) x := hsubx
    _ = (∫ y, K x y * f y ∂volume) - (@inner ℝ _ _ Omega f) * Omega x := by
      rw [hTx, hrankx]
    _ = (∫ y, (R x y * f y + Omega x * (Omega y * f y)) ∂volume) -
          (@inner ℝ _ _ Omega f) * Omega x := by
      congr 2
      refine integral_congr_ae (.of_forall fun y => ?_)
      simp only [R, K, asymNormalizedTransferKernelRemainder]
      ring
    _ = ((∫ y, R x y * f y ∂volume) +
          ∫ y, Omega x * (Omega y * f y) ∂volume) -
          (@inner ℝ _ _ Omega f) * Omega x := by
      rw [integral_add hR_f hground_f]
    _ = ∫ y, R x y * f y ∂volume := by
      rw [integral_const_mul, ← hinner]
      ring

/-- The finite-lattice normalized remainder has its standard integral-kernel
representation. -/
theorem asymNormalizedTransferKernelRemainder_apply
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (m : ℕ) (f : L2SpatialField Ns) :
    (⇑(asymNormalizedTransferRemainderCLM
        (Nt := Nt) (Ns := Ns) P a mass ha hmass m f) : SpatialField Ns → ℝ) =ᵐ[volume]
      fun x => ∫ y,
        asymNormalizedTransferKernelRemainder P a mass ha hmass m x y * f y ∂volume :=
  asymNormalizedTransferKernelRemainder_apply_of_memLp
    (Nt := Nt) (Ns := Ns) P a mass ha hmass m
    (asymNormalizedTransferKernelRemainder_memLp_two
      (Nt := Nt) (Ns := Ns) P a mass ha hmass m) f

/-- An `L2` bound on the normalized remainder kernel gives Hilbert--Schmidt
summability of the corresponding transfer remainder on every Hilbert basis. -/
theorem asymNormalizedTransferKernelRemainder_basis_summable_of_memLp
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (m : ℕ)
    (hR : MemLp
      (Function.uncurry
        (asymNormalizedTransferKernelRemainder
          (Nt := Nt) (Ns := Ns) P a mass ha hmass m))
      2 ((volume : Measure (SpatialField Ns)).prod volume))
    {ι : Type*} (b : HilbertBasis ι ℝ (L2SpatialField Ns)) :
    Summable (fun i : ι =>
      ‖asymNormalizedTransferRemainderCLM
        (Nt := Nt) (Ns := Ns) P a mass ha hmass m (b i)‖ ^ 2) := by
  exact GeneralResults.hs_basis_norm_summable
    (asymNormalizedTransferKernelRemainder
      (Nt := Nt) (Ns := Ns) P a mass ha hmass m)
    hR
    (asymNormalizedTransferRemainderCLM
      (Nt := Nt) (Ns := Ns) P a mass ha hmass m)
    (asymNormalizedTransferKernelRemainder_apply_of_memLp
      (Nt := Nt) (Ns := Ns) P a mass ha hmass m hR)
    b

/-- Parseval rearrangement: the remainder's squared basis-norm sum is at most
its canonical `L2` kernel mass.  This is not a uniform weighted IUC bound. -/
theorem asymNormalizedTransferKernelRemainder_basis_tsum_le_of_memLp
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (m : ℕ)
    (hR : MemLp
      (Function.uncurry
        (asymNormalizedTransferKernelRemainder
          (Nt := Nt) (Ns := Ns) P a mass ha hmass m))
      2 ((volume : Measure (SpatialField Ns)).prod volume))
    {ι : Type*} (b : HilbertBasis ι ℝ (L2SpatialField Ns)) :
    ∑' i : ι,
        ‖asymNormalizedTransferRemainderCLM
          (Nt := Nt) (Ns := Ns) P a mass ha hmass m (b i)‖ ^ 2
      ≤ ‖hR.toLp
          (Function.uncurry
            (asymNormalizedTransferKernelRemainder
              (Nt := Nt) (Ns := Ns) P a mass ha hmass m))‖ ^ 2 := by
  exact GeneralResults.hs_basis_norm_sq_tsum_le
    (asymNormalizedTransferKernelRemainder
      (Nt := Nt) (Ns := Ns) P a mass ha hmass m)
    hR
    (asymNormalizedTransferRemainderCLM
      (Nt := Nt) (Ns := Ns) P a mass ha hmass m)
    (asymNormalizedTransferKernelRemainder_apply_of_memLp
      (Nt := Nt) (Ns := Ns) P a mass ha hmass m hR)
    b

/-- Hilbert--Schmidt Parseval identity for a countably indexed basis: the
squared remainder basis-norm sum equals the canonical `L2` kernel mass.
This rearranges an already-proved finite-lattice `MemLp` certificate; it
does not prove `|R| ≤ C η |Ω||Ω|`. -/
theorem asymNormalizedTransferKernelRemainder_basis_tsum_eq_of_memLp
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (m : ℕ)
    (hR : MemLp
      (Function.uncurry
        (asymNormalizedTransferKernelRemainder
          (Nt := Nt) (Ns := Ns) P a mass ha hmass m))
      2 ((volume : Measure (SpatialField Ns)).prod volume))
    {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℝ (L2SpatialField Ns)) :
    ∑' i : ι,
        ‖asymNormalizedTransferRemainderCLM
          (Nt := Nt) (Ns := Ns) P a mass ha hmass m (b i)‖ ^ 2
      = ‖hR.toLp
          (Function.uncurry
            (asymNormalizedTransferKernelRemainder
              (Nt := Nt) (Ns := Ns) P a mass ha hmass m))‖ ^ 2 := by
  exact GeneralResults.hs_basis_norm_sq_tsum_eq
    (asymNormalizedTransferKernelRemainder
      (Nt := Nt) (Ns := Ns) P a mass ha hmass m)
    hR
    (asymNormalizedTransferRemainderCLM
      (Nt := Nt) (Ns := Ns) P a mass ha hmass m)
    (asymNormalizedTransferKernelRemainder_apply_of_memLp
      (Nt := Nt) (Ns := Ns) P a mass ha hmass m hR)
    b

/-- Every finite-lattice normalized transfer remainder is Hilbert--Schmidt in
the basis-summability sense. -/
theorem asymNormalizedTransferKernelRemainder_basis_summable
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (m : ℕ) {ι : Type*} (b : HilbertBasis ι ℝ (L2SpatialField Ns)) :
    Summable (fun i : ι =>
      ‖asymNormalizedTransferRemainderCLM
        (Nt := Nt) (Ns := Ns) P a mass ha hmass m (b i)‖ ^ 2) :=
  asymNormalizedTransferKernelRemainder_basis_summable_of_memLp
    (Nt := Nt) (Ns := Ns) P a mass ha hmass m
    (asymNormalizedTransferKernelRemainder_memLp_two
      (Nt := Nt) (Ns := Ns) P a mass ha hmass m) b

/-- Finite-lattice Parseval comparison for the canonical remainder `MemLp`
certificate: the basis-norm sum is at most that kernel's `L2` mass.  The
right-hand side remains lattice-dependent; this is not Checkpoint 1 and
does not prove weighted IUC. -/
theorem asymNormalizedTransferKernelRemainder_basis_tsum_le
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (m : ℕ) {ι : Type*} (b : HilbertBasis ι ℝ (L2SpatialField Ns)) :
    ∑' i : ι,
        ‖asymNormalizedTransferRemainderCLM
          (Nt := Nt) (Ns := Ns) P a mass ha hmass m (b i)‖ ^ 2
      ≤ ‖(asymNormalizedTransferKernelRemainder_memLp_two
            (Nt := Nt) (Ns := Ns) P a mass ha hmass m).toLp
          (Function.uncurry
            (asymNormalizedTransferKernelRemainder
              (Nt := Nt) (Ns := Ns) P a mass ha hmass m))‖ ^ 2 :=
  asymNormalizedTransferKernelRemainder_basis_tsum_le_of_memLp
    (Nt := Nt) (Ns := Ns) P a mass ha hmass m
    (asymNormalizedTransferKernelRemainder_memLp_two
      (Nt := Nt) (Ns := Ns) P a mass ha hmass m) b

/-- A Hilbert--Schmidt bound at one smoothing time propagates to every later
time with the square of the ground-orthogonal gap factor. -/
theorem asymNormalizedTransferKernelRemainder_add_basis_tsum_le_of_memLp
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (gamma : ℝ) (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1)
    (hnorm : ∀ v : L2SpatialField Ns,
      @inner ℝ _ _ (asymGroundVector Nt Ns P a mass ha hmass) v = 0 →
      ‖asymTransferNormalized Nt Ns P a mass ha hmass v‖ ≤ gamma * ‖v‖)
    (m n : ℕ)
    (hR : MemLp
      (Function.uncurry
        (asymNormalizedTransferKernelRemainder
          (Nt := Nt) (Ns := Ns) P a mass ha hmass m))
      2 ((volume : Measure (SpatialField Ns)).prod volume))
    {ι : Type*} (b : HilbertBasis ι ℝ (L2SpatialField Ns)) :
    ∑' i : ι,
        ‖asymNormalizedTransferRemainderCLM
          (Nt := Nt) (Ns := Ns) P a mass ha hmass (m + n) (b i)‖ ^ 2
      ≤ (gamma ^ n) ^ 2 *
        ‖hR.toLp
          (Function.uncurry
            (asymNormalizedTransferKernelRemainder
              (Nt := Nt) (Ns := Ns) P a mass ha hmass m))‖ ^ 2 := by
  have hbase : Summable (fun i : ι =>
      ‖asymNormalizedTransferRemainderCLM
        (Nt := Nt) (Ns := Ns) P a mass ha hmass m (b i)‖ ^ 2) :=
    asymNormalizedTransferKernelRemainder_basis_summable_of_memLp
      (Nt := Nt) (Ns := Ns) P a mass ha hmass m hR b
  have hlater : Summable (fun i : ι =>
      ‖asymNormalizedTransferRemainderCLM
        (Nt := Nt) (Ns := Ns) P a mass ha hmass (m + n) (b i)‖ ^ 2) :=
    asymNormalizedTransferKernelRemainder_basis_summable
      (Nt := Nt) (Ns := Ns) P a mass ha hmass (m + n) b
  have hscaled : Summable (fun i : ι =>
      (gamma ^ n) ^ 2 *
        ‖asymNormalizedTransferRemainderCLM
          (Nt := Nt) (Ns := Ns) P a mass ha hmass m (b i)‖ ^ 2) :=
    hbase.mul_left _
  have hpoint : ∀ i : ι,
      ‖asymNormalizedTransferRemainderCLM
          (Nt := Nt) (Ns := Ns) P a mass ha hmass (m + n) (b i)‖ ^ 2 ≤
        (gamma ^ n) ^ 2 *
          ‖asymNormalizedTransferRemainderCLM
            (Nt := Nt) (Ns := Ns) P a mass ha hmass m (b i)‖ ^ 2 := by
    intro i
    have hi := asymNormalizedTransferRemainderCLM_add_apply_norm_le
      (Nt := Nt) (Ns := Ns) P a mass ha hmass gamma hgamma0 hgamma1 hnorm
      m n (b i)
    calc
      ‖asymNormalizedTransferRemainderCLM
          (Nt := Nt) (Ns := Ns) P a mass ha hmass (m + n) (b i)‖ ^ 2 ≤
          (gamma ^ n *
            ‖asymNormalizedTransferRemainderCLM
              (Nt := Nt) (Ns := Ns) P a mass ha hmass m (b i)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hi 2
      _ = (gamma ^ n) ^ 2 *
          ‖asymNormalizedTransferRemainderCLM
            (Nt := Nt) (Ns := Ns) P a mass ha hmass m (b i)‖ ^ 2 := by
        ring
  calc
    ∑' i : ι,
        ‖asymNormalizedTransferRemainderCLM
          (Nt := Nt) (Ns := Ns) P a mass ha hmass (m + n) (b i)‖ ^ 2 ≤
        ∑' i : ι, (gamma ^ n) ^ 2 *
          ‖asymNormalizedTransferRemainderCLM
            (Nt := Nt) (Ns := Ns) P a mass ha hmass m (b i)‖ ^ 2 :=
      Summable.tsum_le_tsum hpoint hlater hscaled
    _ = (gamma ^ n) ^ 2 *
        ∑' i : ι,
          ‖asymNormalizedTransferRemainderCLM
            (Nt := Nt) (Ns := Ns) P a mass ha hmass m (b i)‖ ^ 2 := by
      rw [tsum_mul_left]
    _ ≤ (gamma ^ n) ^ 2 *
        ‖hR.toLp
          (Function.uncurry
            (asymNormalizedTransferKernelRemainder
              (Nt := Nt) (Ns := Ns) P a mass ha hmass m))‖ ^ 2 :=
      mul_le_mul_of_nonneg_left
        (asymNormalizedTransferKernelRemainder_basis_tsum_le_of_memLp
          (Nt := Nt) (Ns := Ns) P a mass ha hmass m hR b)
        (sq_nonneg _)

/-- The spectral gap gives the operator-norm part of the normalized remainder
estimate.  This statement supplies no trace or Hilbert--Schmidt bound. -/
theorem asymNormalizedTransferRemainderCLM_apply_norm_le
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (gamma : ℝ) (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1)
    (hnorm : ∀ v : L2SpatialField Ns,
      @inner ℝ _ _ (asymGroundVector Nt Ns P a mass ha hmass) v = 0 →
      ‖asymTransferNormalized Nt Ns P a mass ha hmass v‖ ≤ gamma * ‖v‖)
    (m : ℕ) (f : L2SpatialField Ns) :
    ‖asymNormalizedTransferRemainderCLM
        (Nt := Nt) (Ns := Ns) P a mass ha hmass m f‖
      ≤ gamma ^ (m + 1) * ‖f‖ := by
  let Omega := asymGroundVector Nt Ns P a mass ha hmass
  let G := asymGappedTransfer Nt Ns P a mass ha hmass gamma hgamma0 hgamma1 hnorm
  have hperp : @inner ℝ _ _ Omega (f - (@inner ℝ _ _ Omega f) • Omega) = 0 := by
    rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq,
      asymGroundVector_norm_eq_one]
    ring
  have hground_pow : (G.T ^ (m + 1)) Omega = Omega := by
    induction m with
    | zero => simpa only [pow_one, G, Omega] using G.vacuum_eq
    | succ n ih =>
        rw [pow_succ', ContinuousLinearMap.mul_apply, ih]
        exact G.vacuum_eq
  have hid :
      asymNormalizedTransferRemainderCLM
          (Nt := Nt) (Ns := Ns) P a mass ha hmass m f =
        (G.T ^ (m + 1)) (f - (@inner ℝ _ _ Omega f) • Omega) := by
    simp only [asymNormalizedTransferRemainderCLM,
      ContinuousLinearMap.sub_apply, InnerProductSpace.rankOne_apply]
    change (G.T ^ (m + 1)) f - (@inner ℝ _ _ Omega f) • Omega = _
    rw [map_sub, map_smul, hground_pow]
  rw [hid]
  calc
    ‖(G.T ^ (m + 1)) (f - (@inner ℝ _ _ Omega f) • Omega)‖
        ≤ gamma ^ (m + 1) * ‖f - (@inner ℝ _ _ Omega f) • Omega‖ :=
          G.norm_T_pow_le hperp (m + 1)
    _ ≤ gamma ^ (m + 1) * ‖f‖ :=
      mul_le_mul_of_nonneg_left
        (norm_sub_groundProj_le (Nt := Nt) (Ns := Ns) P a mass ha hmass f)
        (pow_nonneg hgamma0 _)

end Pphi2
