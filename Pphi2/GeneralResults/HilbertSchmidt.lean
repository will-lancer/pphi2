/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hilbert-Schmidt Compactness for L² Integral Operators

General functional-analysis result, with no QFT content. Belongs upstream in
`SpectralThm` or Mathlib once a full Hilbert-Schmidt theory lands.

## Main result

`integral_operator_l2_kernel_compact`:

If `G` is a locally compact, second-countable, T₂ normed real vector space with
Haar measure `μ`, `K : G × G → ℝ` is a kernel with `K ∈ L²(μ ⊗ μ)`, and
`T : L²(μ) → L²(μ)` is a continuous linear map such that
  `(T f)(x) = ∫ K(x, t) · f(x − t) dμ(t)`
holds a.e. in `x`, then `T` is a compact operator.

## Proof strategy

The proof composes:

1. **Convolution → standard form** (proved): the substitution
   `Φ : (x, y) ↦ (x, x − y)` is a measure-preserving automorphism of `μ ⊗ μ`
   on a Haar group, so the convolution-form kernel `K(x, t)` rewrites to a
   standard-form kernel `K_std(x, y) := K(x, x − y)` with the same `L²(μ⊗μ)`
   norm and the same induced operator.

2. **Hilbert-Schmidt summability** (`hs_basis_norm_summable`, proved):
   for any Hilbert basis `b` of `L²(μ)`, `Σᵢ ‖T (b i)‖²_{L²(μ)} < ∞`. The
   proof is one Parseval-on-the-slice step plus Tonelli.

3. **Operator-theoretic HS ⟹ compact** (`isCompactOperator_of_basis_norm_summable`,
   proved): a bounded operator with summable squared basis norms is compact,
   via finite-rank truncation and the Bessel residual.

Both helpers (Reed-Simon I, Theorem VI.22) are split out as standalone
theorems so they can be reused independently and so the main composition
reads cleanly.

## References

- Reed, M. and Simon, B., *Methods of Modern Mathematical Physics, Vol. I:
  Functional Analysis* (Academic Press, 1980), §VI.6 — Hilbert-Schmidt
  operators, Theorem VI.22.
- Simon, B., *Trace Ideals and their Applications* (AMS, 2nd ed., 2005), §III.2.
-/

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.Normed.Operator.Compact.Basic

namespace Pphi2.GeneralResults

open MeasureTheory Real Filter

noncomputable section

/-! ## Hilbert-Schmidt helpers

Two analytic facts factored out as standalone theorems. Each is one well-known
result from Reed-Simon I §VI.6, proved here against Mathlib's current API.
They are split out to make the proof of the main theorem read cleanly and to
make the two reusable pieces independently citable. -/

/-- **Hilbert-Schmidt summability of basis norms.**

For any standard-form integral operator `T` with kernel `K ∈ L²(μ ⊗ μ)` and any
Hilbert basis `{bᵢ}` of `L²(μ)`, the sequence `i ↦ ‖T (bᵢ)‖²` is summable.

In fact equality holds (`Σᵢ ‖T bᵢ‖² = ‖K‖²_{L²(μ⊗μ)}`); we state only the
summability since that is all the compactness argument needs.

**Reference**: Reed-Simon I (1980), Theorem VI.22.

**Proof sketch**: For each `i`, the function `T bᵢ : L²(μ)` admits the
representative `x ↦ ∫ K(x, y) · (bᵢ)(y) dμ(y) = ⟨K(x, ·), bᵢ⟩_{L²(μ)}`, where
`K(x, ·) ∈ L²(μ)` for a.e. `x` by Fubini. Parseval applied to the slice
`K(x, ·)` gives `Σᵢ |⟨K(x, ·), bᵢ⟩|² = ‖K(x, ·)‖²_{L²(μ)}`, and integrating in
`x` via Tonelli yields `Σᵢ ‖T bᵢ‖² = ∫ ‖K(x, ·)‖² dμ(x) = ‖K‖²_{L²(μ⊗μ)}`. -/
private theorem hs_basis_norm_sq_eq_integral
    {G : Type*} [MeasurableSpace G] {μ : Measure G}
    (f : Lp ℝ 2 μ) :
    ‖f‖ ^ 2 = ∫ x, ((f : G → ℝ) x) ^ 2 ∂μ := by
  calc
    ‖f‖ ^ 2 = inner ℝ f f := by rw [← real_inner_self_eq_norm_sq]
    _ = ∫ x, ((f : G → ℝ) x) ^ 2 ∂μ := by
      rw [MeasureTheory.L2.inner_def]
      simp [pow_two]

private theorem hs_slice_inner_eq_integral
    {G : Type*} [MeasurableSpace G] {μ : Measure G}
    {K₀ : G × G → ℝ} {x : G}
    (hxslice : MemLp (fun y => K₀ (x, y)) 2 μ)
    {ι : Type*} (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) (i : ι) :
    inner ℝ (b i) (hxslice.toLp (fun y => K₀ (x, y))) =
      ∫ y, (b i : G → ℝ) y * K₀ (x, y) ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp hxslice] with y hy
  calc
    inner ℝ ((b i : G → ℝ) y) ((hxslice.toLp (fun y => K₀ (x, y))) y)
      = inner ℝ ((b i : G → ℝ) y) (K₀ (x, y)) := by simp [hy]
    _ = (b i : G → ℝ) y * K₀ (x, y) := by
          simpa using (RCLike.inner_apply' ((b i : G → ℝ) y) (K₀ (x, y)))

private theorem hs_slice_norm_sq_eq_integral
    {G : Type*} [MeasurableSpace G] {μ : Measure G}
    {K₀ : G × G → ℝ} {x : G}
    (hxslice : MemLp (fun y => K₀ (x, y)) 2 μ) :
    ‖hxslice.toLp (fun y => K₀ (x, y))‖ ^ 2 =
      ∫ y, K₀ (x, y) ^ 2 ∂μ := by
  calc
    ‖hxslice.toLp (fun y => K₀ (x, y))‖ ^ 2
      = inner ℝ (hxslice.toLp (fun y => K₀ (x, y))) (hxslice.toLp (fun y => K₀ (x, y))) := by
          rw [← real_inner_self_eq_norm_sq]
    _ = ∫ y, K₀ (x, y) ^ 2 ∂μ := by
      rw [MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp hxslice] with y hy
      calc
        inner ℝ
            ((hxslice.toLp (fun y => K₀ (x, y))) y)
            ((hxslice.toLp (fun y => K₀ (x, y))) y)
          = inner ℝ (K₀ (x, y)) (K₀ (x, y)) := by simp [hy]
        _ = K₀ (x, y) ^ 2 := by
              simp [pow_two]

private theorem hs_basis_norm_summable_and_tsum_le
    {G : Type*} [MeasurableSpace G] {μ : Measure G} [SigmaFinite μ]
    (K : G → G → ℝ)
    (hK : MemLp (Function.uncurry K) 2 (μ.prod μ))
    (T : (Lp ℝ 2 μ) →L[ℝ] (Lp ℝ 2 μ))
    (hT : ∀ f : Lp ℝ 2 μ,
      (T f : G → ℝ) =ᵐ[μ] fun x => ∫ y, K x y * (f : G → ℝ) y ∂μ)
    {ι : Type*} (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) :
    Summable (fun i : ι => ‖T (b i)‖ ^ 2) ∧
      (∑' i : ι, ‖T (b i)‖ ^ 2 ≤
        ‖hK.toLp (Function.uncurry K)‖ ^ 2) ∧
      (∀ [Countable ι],
        ∑' i : ι, ‖T (b i)‖ ^ 2 =
          ‖hK.toLp (Function.uncurry K)‖ ^ 2) := by
  classical
  let K₀ : G × G → ℝ := hK.aestronglyMeasurable.mk (Function.uncurry K)
  have hK₀_meas : StronglyMeasurable K₀ := hK.aestronglyMeasurable.stronglyMeasurable_mk
  have hK₀_ae : Function.uncurry K =ᵐ[μ.prod μ] K₀ := hK.aestronglyMeasurable.ae_eq_mk
  have hK₀_mem : MemLp K₀ 2 (μ.prod μ) := (memLp_congr_ae hK₀_ae).mp hK
  have hK₀_sq : Integrable (fun z => K₀ z ^ 2) (μ.prod μ) := hK₀_mem.integrable_sq
  have hK₀_ae_slices : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, K x y = K₀ (x, y) := by
    simpa [Function.uncurry] using (MeasureTheory.Measure.ae_ae_of_ae_prod hK₀_ae)
  have hT₀ :
      ∀ i : ι, (T (b i) : G → ℝ) =ᵐ[μ] fun x =>
        ∫ y, K₀ (x, y) * (b i : G → ℝ) y ∂μ := by
    intro i
    refine (hT (b i)).trans ?_
    filter_upwards [hK₀_ae_slices] with x hx
    apply integral_congr_ae
    filter_upwards [hx] with y hy
    simp [hy]
  have hT₀_finset :
      ∀ S : Finset ι, ∀ᵐ x ∂μ, ∀ i ∈ S,
        (T (b i) : G → ℝ) x = ∫ y, K₀ (x, y) * (b i : G → ℝ) y ∂μ := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        exact Filter.Eventually.of_forall (fun x i hi => False.elim (by simp at hi))
    | insert a s ha hs =>
        have hae := hT₀ a
        have hse := hs
        filter_upwards [hae, hse] with x hxa hxs i hi
        rcases Finset.mem_insert.mp hi with rfl | hi'
        · exact hxa
        · exact hxs i hi'
  have hsum_bound :
      ∀ S : Finset ι,
        ∑ i ∈ S, ‖T (b i)‖ ^ 2 ≤ ∫ x, ∫ y, K₀ (x, y) ^ 2 ∂μ ∂μ := by
    intro S
    let F : G → ℝ := fun x => ∑ i ∈ S, ((T (b i) : G → ℝ) x) ^ 2
    let Gs : G → ℝ := fun x => ∫ y, K₀ (x, y) ^ 2 ∂μ
    have hF_int : Integrable F μ := by
      refine integrable_finset_sum S ?_
      intro i hi
      simpa using (Lp.memLp (T (b i))).integrable_sq
    have hGs_int : Integrable Gs μ := by
      simpa [Gs] using hK₀_sq.integral_prod_left
    have hT₀S :
        ∀ᵐ x ∂μ, ∀ i ∈ S,
          (T (b i) : G → ℝ) x = ∫ y, K₀ (x, y) * (b i : G → ℝ) y ∂μ :=
      hT₀_finset S
    have hpointwise : ∀ᵐ x ∂μ, F x ≤ Gs x := by
      filter_upwards [hK₀_sq.prod_right_ae, hT₀S] with x hx_sq hxT
      have hslice_meas : AEStronglyMeasurable (fun y => K₀ (x, y)) μ :=
        (hK₀_meas.comp_measurable measurable_prodMk_left).aestronglyMeasurable
      have hslice_mem : MemLp (fun y => K₀ (x, y)) 2 μ :=
        (memLp_two_iff_integrable_sq hslice_meas).2 hx_sq
      let kx : Lp ℝ 2 μ := hslice_mem.toLp (fun y => K₀ (x, y))
      have hk_norm : ‖kx‖ ^ 2 = Gs x := by
        simpa [kx, Gs] using hs_slice_norm_sq_eq_integral (K₀ := K₀) hslice_mem
      have hk_inner :
          ∀ i ∈ S, (T (b i) : G → ℝ) x = inner ℝ (b i) kx := by
        intro i hi
        calc
          (T (b i) : G → ℝ) x = ∫ y, K₀ (x, y) * (b i : G → ℝ) y ∂μ := hxT i hi
          _ = ∫ y, (b i : G → ℝ) y * K₀ (x, y) ∂μ := by simp_rw [mul_comm]
          _ = inner ℝ (b i) kx := by
                symm
                simpa [kx] using hs_slice_inner_eq_integral (K₀ := K₀) hslice_mem b i
      have hF_eq : F x = ∑ i ∈ S, ‖inner ℝ (b i) kx‖ ^ 2 := by
        simp only [F]
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [hk_inner i hi]
        have hsq : inner ℝ (b i) kx ^ 2 = ‖inner ℝ (b i) kx‖ ^ 2 := by
          have habs : inner ℝ (b i) kx ^ 2 = |inner ℝ (b i) kx| ^ 2 := by
            exact (sq_abs (inner ℝ (b i) kx)).symm
          rw [Real.norm_eq_abs]
          exact habs
        exact hsq
      have hBessel : ∑ i ∈ S, ‖inner ℝ (b i) kx‖ ^ 2 ≤ ‖kx‖ ^ 2 :=
        b.orthonormal.sum_inner_products_le (s := S) kx
      exact hF_eq.trans_le (hBessel.trans_eq hk_norm)
    calc
      ∑ i ∈ S, ‖T (b i)‖ ^ 2 = ∑ i ∈ S, ∫ x, ((T (b i) : G → ℝ) x) ^ 2 ∂μ := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simpa using hs_basis_norm_sq_eq_integral (T (b i))
      _ = ∫ x, F x ∂μ := by
        have hFin :
            ∫ x, F x ∂μ = ∑ i ∈ S, ∫ x, ((T (b i) : G → ℝ) x) ^ 2 ∂μ := by
          simpa [F] using
            (integral_finset_sum S (fun i hi => by
              simpa using (Lp.memLp (T (b i))).integrable_sq))
        exact hFin.symm
      _ ≤ ∫ x, Gs x ∂μ := by
        simpa [Gs] using integral_mono_ae hF_int hGs_int hpointwise
      _ = ∫ x, ∫ y, K₀ (x, y) ^ 2 ∂μ ∂μ := rfl
  have hsummable : Summable (fun i : ι => ‖T (b i)‖ ^ 2) :=
    summable_of_sum_le (fun i => by positivity) hsum_bound
  have htsum : ∑' i : ι, ‖T (b i)‖ ^ 2 ≤
      ∫ x, ∫ y, K₀ (x, y) ^ 2 ∂μ ∂μ :=
    hsummable.tsum_le_of_sum_le hsum_bound
  have htoLp :
      hK.toLp (Function.uncurry K) = hK₀_mem.toLp K₀ :=
    MemLp.toLp_congr hK hK₀_mem hK₀_ae
  have hkernel_norm :
      (∫ x, ∫ y, K₀ (x, y) ^ 2 ∂μ ∂μ) =
        ‖hK.toLp (Function.uncurry K)‖ ^ 2 := by
    have hFubini :
        (∫ x, ∫ y, K₀ (x, y) ^ 2 ∂μ ∂μ) =
          ∫ z, K₀ z ^ 2 ∂μ.prod μ := by
      simpa only [Function.uncurry] using
        (integral_integral (f := fun x y => K₀ (x, y) ^ 2) hK₀_sq)
    rw [hFubini, htoLp]
    symm
    calc
      ‖hK₀_mem.toLp K₀‖ ^ 2 =
          ∫ z, ((hK₀_mem.toLp K₀ : G × G → ℝ) z) ^ 2 ∂μ.prod μ :=
        hs_basis_norm_sq_eq_integral (hK₀_mem.toLp K₀)
      _ = ∫ z, K₀ z ^ 2 ∂μ.prod μ := by
        refine integral_congr_ae ?_
        filter_upwards [MemLp.coeFn_toLp hK₀_mem] with z hz
        rw [hz]
  have hEq : ∀ [Countable ι],
      ∑' i : ι, ‖T (b i)‖ ^ 2 =
        ‖hK.toLp (Function.uncurry K)‖ ^ 2 := by
    intro _
    let Gs : G → ℝ := fun x => ∫ y, K₀ (x, y) ^ 2 ∂μ
    have hT₀_all : ∀ᵐ x ∂μ, ∀ i : ι,
        (T (b i) : G → ℝ) x =
          ∫ y, K₀ (x, y) * (b i : G → ℝ) y ∂μ := by
      exact ae_all_iff.2 hT₀
    have hpointwise_hasSum : ∀ᵐ x ∂μ, HasSum
        (fun i : ι => ((T (b i) : G → ℝ) x) ^ 2)
        (Gs x) := by
      filter_upwards [hK₀_sq.prod_right_ae, hT₀_all] with x hx_sq hxT
      have hslice_meas : AEStronglyMeasurable (fun y => K₀ (x, y)) μ :=
        (hK₀_meas.comp_measurable measurable_prodMk_left).aestronglyMeasurable
      have hslice_mem : MemLp (fun y => K₀ (x, y)) 2 μ :=
        (memLp_two_iff_integrable_sq hslice_meas).2 hx_sq
      let kx : Lp ℝ 2 μ := hslice_mem.toLp (fun y => K₀ (x, y))
      have hk_inner : ∀ i : ι,
          (T (b i) : G → ℝ) x = inner ℝ (b i) kx := by
        intro i
        calc
          (T (b i) : G → ℝ) x =
              ∫ y, K₀ (x, y) * (b i : G → ℝ) y ∂μ := hxT i
          _ = ∫ y, (b i : G → ℝ) y * K₀ (x, y) ∂μ := by
                simp_rw [mul_comm]
          _ = inner ℝ (b i) kx := by
                symm
                simpa [kx] using
                  hs_slice_inner_eq_integral (K₀ := K₀) hslice_mem b i
      have hsum_inner : HasSum
          (fun i : ι => ((T (b i) : G → ℝ) x) ^ 2)
          (inner ℝ kx kx) := by
        refine (b.hasSum_inner_mul_inner kx kx).congr ?_
        intro i
        calc
          inner ℝ kx (b i) * inner ℝ (b i) kx =
              inner ℝ (b i) kx * inner ℝ (b i) kx := by
                rw [real_inner_comm kx (b i)]
          _ = ((T (b i) : G → ℝ) x) ^ 2 := by
                rw [hk_inner i]
      have hk_norm : ‖kx‖ ^ 2 = Gs x := by
        simpa [kx, Gs] using
          hs_slice_norm_sq_eq_integral (K₀ := K₀) hslice_mem
      have hk_self : inner ℝ kx kx = Gs x := by
        rw [real_inner_self_eq_norm_sq, hk_norm]
      rw [hk_self] at hsum_inner
      exact hsum_inner
    have hFi_int : ∀ i : ι, Integrable
        (fun x => ((T (b i) : G → ℝ) x) ^ 2) μ := by
      intro i
      simpa using (Lp.memLp (T (b i))).integrable_sq
    have hFi_sum_norm : Summable (fun i : ι =>
        ∫ x, ‖((T (b i) : G → ℝ) x) ^ 2‖ ∂μ) := by
      apply hsummable.congr
      intro i
      calc
        ‖T (b i)‖ ^ 2 =
            ∫ x, ((T (b i) : G → ℝ) x) ^ 2 ∂μ :=
          hs_basis_norm_sq_eq_integral (T (b i))
        _ = ∫ x, ‖((T (b i) : G → ℝ) x) ^ 2‖ ∂μ := by
              refine integral_congr_ae (.of_forall fun x => ?_)
              rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hintegral_tsum :
        ∑' i : ι, ∫ x, ((T (b i) : G → ℝ) x) ^ 2 ∂μ =
          ∫ x, ∑' i : ι, ((T (b i) : G → ℝ) x) ^ 2 ∂μ :=
      integral_tsum_of_summable_integral_norm hFi_int hFi_sum_norm
    calc
      ∑' i : ι, ‖T (b i)‖ ^ 2 =
          ∑' i : ι, ∫ x, ((T (b i) : G → ℝ) x) ^ 2 ∂μ := by
            apply tsum_congr
            intro i
            exact hs_basis_norm_sq_eq_integral (T (b i))
      _ = ∫ x, ∑' i : ι, ((T (b i) : G → ℝ) x) ^ 2 ∂μ :=
        hintegral_tsum
      _ = ∫ x, Gs x ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [hpointwise_hasSum] with x hx
        exact hx.tsum_eq
      _ = ∫ x, ∫ y, K₀ (x, y) ^ 2 ∂μ ∂μ := rfl
      _ = ‖hK.toLp (Function.uncurry K)‖ ^ 2 := hkernel_norm
  exact ⟨hsummable, htsum.trans_eq hkernel_norm, hEq⟩

/-- **Hilbert-Schmidt summability of basis norms.**

For any standard-form integral operator with an `L2` kernel, the squared norms
of its values on a Hilbert basis form a summable family. -/
theorem hs_basis_norm_summable
    {G : Type*} [MeasurableSpace G] {μ : Measure G} [SigmaFinite μ]
    (K : G → G → ℝ)
    (hK : MemLp (Function.uncurry K) 2 (μ.prod μ))
    (T : (Lp ℝ 2 μ) →L[ℝ] (Lp ℝ 2 μ))
    (hT : ∀ f : Lp ℝ 2 μ,
      (T f : G → ℝ) =ᵐ[μ] fun x => ∫ y, K x y * (f : G → ℝ) y ∂μ)
    {ι : Type*} (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) :
    Summable (fun i : ι => ‖T (b i)‖ ^ 2) :=
  (hs_basis_norm_summable_and_tsum_le K hK T hT b).1

/-- One-sided Parseval comparison: the squared basis-norm sum is at most the
squared `L²` kernel mass.  This rearranges the Hilbert--Schmidt pairing; it
is not a model-specific envelope and does not prove the coupled weighted IUC
bound `|R| ≤ C η |Ω||Ω|`. -/
theorem hs_basis_norm_sq_tsum_le
    {G : Type*} [MeasurableSpace G] {μ : Measure G} [SigmaFinite μ]
    (K : G → G → ℝ)
    (hK : MemLp (Function.uncurry K) 2 (μ.prod μ))
    (T : (Lp ℝ 2 μ) →L[ℝ] (Lp ℝ 2 μ))
    (hT : ∀ f : Lp ℝ 2 μ,
      (T f : G → ℝ) =ᵐ[μ] fun x => ∫ y, K x y * (f : G → ℝ) y ∂μ)
    {ι : Type*} (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) :
    ∑' i : ι, ‖T (b i)‖ ^ 2 ≤
      ‖hK.toLp (Function.uncurry K)‖ ^ 2 :=
  (hs_basis_norm_summable_and_tsum_le K hK T hT b).2.1

/-! The reverse Hilbert--Schmidt inequality is Parseval's equality.  The
countability assumption is explicit because the Bochner integral/tsum
interchange used in the proof is countable-indexed.  In the separable
`L²` applications, an orthonormal-basis countability instance supplies it. -/

/-- **Hilbert--Schmidt Parseval identity.**

For a countably indexed Hilbert basis,
`∑' i, ‖T (b i)‖² = ‖K‖²_{L²(μ⊗μ)}`.  This is an identity/rearrangement of
the kernel's `L²` mass, not a quantitative Hilbert--Schmidt bound and not a
Checkpoint 1 closer.  The finite-sum estimate gives only the forward
inequality; the proof uses `HilbertBasis.hasSum_inner_mul_inner` on almost
every kernel slice and `integral_tsum_of_summable_integral_norm` to exchange
the series with the outer integral.  The weighted IUC estimate
`|R| ≤ C η |Ω||Ω|` uniform under `(Ns : ℝ) * a = Ls` remains unproved. -/
theorem hs_basis_norm_sq_tsum_eq
    {G : Type*} [MeasurableSpace G] {μ : Measure G} [SigmaFinite μ]
    (K : G → G → ℝ)
    (hK : MemLp (Function.uncurry K) 2 (μ.prod μ))
    (T : (Lp ℝ 2 μ) →L[ℝ] (Lp ℝ 2 μ))
    (hT : ∀ f : Lp ℝ 2 μ,
      (T f : G → ℝ) =ᵐ[μ] fun x => ∫ y, K x y * (f : G → ℝ) y ∂μ)
    {ι : Type*} [Countable ι] (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) :
    ∑' i : ι, ‖T (b i)‖ ^ 2 =
      ‖hK.toLp (Function.uncurry K)‖ ^ 2 :=
  (hs_basis_norm_summable_and_tsum_le K hK T hT b).2.2

/-- Swapping the two variables of a product-space `L2` kernel preserves
membership in `L2`. -/
theorem memLp_two_prod_swap
    {S E : Type*} [MeasurableSpace S] [NormedAddCommGroup E]
    {μ : Measure S} [SFinite μ]
    (K : S × S → E) (hK : MemLp K 2 (μ.prod μ)) :
    MemLp (K ∘ (Prod.swap : S × S → S × S)) 2 (μ.prod μ) := by
  exact hK.comp_measurePreserving
    (Measure.measurePreserving_swap (μ := μ) (ν := μ))

/-- The `L2` norm of a product-space kernel is unchanged by transposing its
variables. -/
theorem norm_toLp_two_prod_swap
    {S E : Type*} [MeasurableSpace S] [NormedAddCommGroup E]
    {μ : Measure S} [SFinite μ]
    (K : S × S → E) (hK : MemLp K 2 (μ.prod μ)) :
    ‖(hK.comp_measurePreserving
        (Measure.measurePreserving_swap (μ := μ) (ν := μ))).toLp
      (K ∘ (Prod.swap : S × S → S × S))‖ =
      ‖hK.toLp K‖ := by
  let hswap : MeasurePreserving (Prod.swap : S × S → S × S)
      (μ.prod μ) (μ.prod μ) :=
    Measure.measurePreserving_swap (μ := μ) (ν := μ)
  rw [← Lp.toLp_compMeasurePreserving hK hswap]
  exact Lp.norm_compMeasurePreserving (hK.toLp K) hswap

/-- The square-root form of the real `L2` integral is the norm of the
corresponding `Lp` element. -/
theorem integral_norm_sq_rpow_half_eq_norm_toLp
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (R : α → ℝ) (hR : MemLp R 2 μ) :
    (∫ x, ‖R x‖ ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) = ‖hR.toLp R‖ := by
  have hsq : ‖hR.toLp R‖ ^ 2 = ∫ x, ‖R x‖ ^ (2 : ℝ) ∂μ := by
    calc
      ‖hR.toLp R‖ ^ 2 =
          ∫ x, ((hR.toLp R : α → ℝ) x) ^ 2 ∂μ :=
        hs_basis_norm_sq_eq_integral (hR.toLp R)
      _ = ∫ x, R x ^ 2 ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [MemLp.coeFn_toLp hR] with x hx
        rw [hx]
      _ = ∫ x, ‖R x‖ ^ (2 : ℝ) ∂μ := by
        refine integral_congr_ae (.of_forall fun x => ?_)
        simp only [Real.norm_eq_abs, Real.rpow_two, sq_abs]
  rw [← hsq, ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)]

/-- A concrete Hilbert--Schmidt Cauchy bound for a complex insertion between
two real `L2` kernels. -/
theorem norm_integral_complex_four_mul_le_L2
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (F G : α → ℂ) (R S : α → ℝ) (BF BG : ℝ)
    (hBF : 0 ≤ BF) (hBG : 0 ≤ BG)
    (hF : ∀ x, ‖F x‖ ≤ BF) (hG : ∀ x, ‖G x‖ ≤ BG)
    (hR : MemLp R 2 μ) (hS : MemLp S 2 μ) :
    ‖∫ x, F x * (R x : ℂ) * G x * (S x : ℂ) ∂μ‖ ≤
      BF * BG *
        (∫ x, ‖R x‖ ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) *
        (∫ x, ‖S x‖ ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) := by
  letI : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 := ⟨by norm_num⟩
  have hRS : Integrable (fun x => ‖R x‖ * ‖S x‖) μ := by
    have h := hR.norm.integrable_mul hS.norm
    simpa only [Pi.mul_apply] using h
  have hmajor : Integrable
      (fun x => BF * BG * (‖R x‖ * ‖S x‖)) μ :=
    hRS.const_mul (BF * BG)
  have hpoint : ∀ x,
      ‖F x * (R x : ℂ) * G x * (S x : ℂ)‖ ≤
        BF * BG * (‖R x‖ * ‖S x‖) := by
    intro x
    calc
      ‖F x * (R x : ℂ) * G x * (S x : ℂ)‖ =
          (‖F x‖ * ‖G x‖) * (‖R x‖ * ‖S x‖) := by
        simp only [norm_mul, Complex.norm_real]
        ring
      _ ≤ (BF * BG) * (‖R x‖ * ‖S x‖) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul (hF x) (hG x) (norm_nonneg _) hBF
        · exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hCS :
      ∫ x, ‖R x‖ * ‖S x‖ ∂μ ≤
        (∫ x, ‖R x‖ ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) *
          (∫ x, ‖S x‖ ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) := by
    refine integral_mul_norm_le_Lp_mul_Lq (μ := μ) (E := ℝ)
      (p := (2 : ℝ)) (q := (2 : ℝ)) Real.HolderConjugate.two_two ?_ ?_
    · rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
      exact hR
    · rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
      exact hS
  calc
    ‖∫ x, F x * (R x : ℂ) * G x * (S x : ℂ) ∂μ‖ ≤
        ∫ x, BF * BG * (‖R x‖ * ‖S x‖) ∂μ :=
      norm_integral_le_of_norm_le hmajor (ae_of_all _ hpoint)
    _ = BF * BG * (∫ x, ‖R x‖ * ‖S x‖ ∂μ) := by
      rw [integral_const_mul]
    _ ≤ BF * BG *
        ((∫ x, ‖R x‖ ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) *
          (∫ x, ‖S x‖ ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left hCS (mul_nonneg hBF hBG)
    _ = BF * BG *
        (∫ x, ‖R x‖ ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) *
        (∫ x, ‖S x‖ ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) := by
      ring

/-- The same four-factor estimate written with the `Lp` norms of the two
kernel representatives. -/
theorem norm_integral_complex_four_mul_le_toLp
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (F G : α → ℂ) (R S : α → ℝ) (BF BG : ℝ)
    (hBF : 0 ≤ BF) (hBG : 0 ≤ BG)
    (hF : ∀ x, ‖F x‖ ≤ BF) (hG : ∀ x, ‖G x‖ ≤ BG)
    (hR : MemLp R 2 μ) (hS : MemLp S 2 μ) :
    ‖∫ x, F x * (R x : ℂ) * G x * (S x : ℂ) ∂μ‖ ≤
      BF * BG * ‖hR.toLp R‖ * ‖hS.toLp S‖ := by
  have h := norm_integral_complex_four_mul_le_L2
    μ F G R S BF BG hBF hBG hF hG hR hS
  rw [integral_norm_sq_rpow_half_eq_norm_toLp R hR,
    integral_norm_sq_rpow_half_eq_norm_toLp S hS] at h
  exact h

/-! ### Scaffolding for the operator-theoretic Hilbert-Schmidt criterion

`isCompactOperator_of_basis_norm_summable` below is the operator-theoretic
step "summable squared basis norms ⟹ compact" (Reed-Simon I,
Theorem VI.22(a)). The classical proof uses finite-rank truncations and the
Bessel residual bound: the finite-rank truncation `T_S` is built from rank-1
operators `x ↦ ⟨bᵢ, x⟩ • T(bᵢ)`, each compact (as it factors through `ℝ`),
and `‖T - T_S‖²_{op} ≤ Σ_{i ∉ S} ‖T(bᵢ)‖² → 0` along `Filter.atTop`.

The two helpers `rank1Op_isCompactOperator` and `truncatedOp_isCompactOperator`
below discharge the "build T_S; T_S is compact" half; `tendsto_truncatedOp`
discharges the operator-norm convergence half via the Bessel residual on the
summable tail. -/

section HSCriterion

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {ι : Type*} (b : HilbertBasis ι ℝ H) (T : H →L[ℝ] H)

/-- The rank-1 operator `x ↦ ⟨bᵢ, x⟩ • T(bᵢ)`. -/
private noncomputable def rank1Op (i : ι) : H →L[ℝ] H :=
  ContinuousLinearMap.smulRight (innerSL ℝ (b i)) (T (b i))

@[simp] private theorem rank1Op_apply (i : ι) (x : H) :
    rank1Op b T i x = (inner ℝ (b i) x) • T (b i) := by
  simp [rank1Op]

/-- Each rank-1 operator factors through `ℝ` — locally compact — hence is compact. -/
private theorem rank1Op_isCompactOperator (i : ι) :
    IsCompactOperator (rank1Op b T i) := by
  -- Factor: rank1Op b T i = (smulRight 1 (T (b i))) ∘L (innerSL ℝ (b i))
  -- Source ℝ of the outer map is locally compact, so the outer map is compact;
  -- pre-composing with a CLM keeps compactness.
  have h_outer :
      IsCompactOperator
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (T (b i))) :=
    isCompactOperator_of_locallyCompactSpace_rng _
  have hcomp :
      rank1Op b T i =
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (T (b i))).comp
          (innerSL ℝ (b i)) := by
    ext x
    simp [rank1Op]
  rw [hcomp]
  exact h_outer.comp_clm _

/-- The truncated operator `T_S x := Σ_{i ∈ S} ⟨bᵢ, x⟩ • T(bᵢ)`. -/
private noncomputable def truncatedOp (S : Finset ι) : H →L[ℝ] H :=
  ∑ i ∈ S, rank1Op b T i

/-- The truncated operator is compact (finite sum of rank-1 operators). -/
private theorem truncatedOp_isCompactOperator (S : Finset ι) :
    IsCompactOperator (truncatedOp b T S) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simpa [truncatedOp] using
      (isCompactOperator_zero (M₁ := H) (M₂ := H))
  | insert a s ha ih =>
    show IsCompactOperator (truncatedOp b T (insert a s))
    rw [truncatedOp, Finset.sum_insert ha]
    exact (rank1Op_isCompactOperator b T a).add (by simpa [truncatedOp] using ih)

variable (hT_summable : Summable (fun i : ι => ‖T (b i)‖ ^ 2))

/-- The full Hilbert-basis expansion of `T x` in rank-1 pieces. -/
private theorem hasSum_rank1Op_apply (x : H) :
    HasSum (fun i : ι => rank1Op b T i x) (T x) := by
  simpa [rank1Op_apply, HilbertBasis.repr_apply_apply] using
    (b.hasSum_repr x).mapL T

variable [CompleteSpace H]

/-- The truncation residual is the `tsum` over the complement. -/
private theorem sub_truncatedOp_apply_eq_tsum (S : Finset ι) (x : H) :
    (T - truncatedOp b T S) x =
      ∑' i : {i // i ∉ S}, (inner ℝ (b i.1) x) • T (b i.1) := by
  have hsummable : Summable (fun i : ι => rank1Op b T i x) :=
    (hasSum_rank1Op_apply b T x).summable
  have hsum := hsummable.sum_add_tsum_subtype_compl S
  have htsum : ∑' i : ι, rank1Op b T i x = T x :=
    (hasSum_rank1Op_apply b T x).tsum_eq
  change T x - truncatedOp b T S x = _
  rw [sub_eq_iff_eq_add']
  rw [← htsum]
  simpa [truncatedOp, rank1Op_apply, add_comm, add_left_comm, add_assoc] using hsum.symm

/-- Pointwise Bessel-tail bound for the truncation residual. -/
private theorem norm_sub_truncatedOp_apply_le
    (hT_summable : Summable (fun i : ι => ‖T (b i)‖ ^ 2)) (S : Finset ι) (x : H) :
    ‖(T - truncatedOp b T S) x‖ ≤
      Real.sqrt (∑' i : {i // i ∉ S}, ‖T (b i.1)‖ ^ 2) * ‖x‖ := by
  let f : {i // i ∉ S} → ℝ := fun i => ‖inner ℝ (b i.1) x‖
  let g : {i // i ∉ S} → ℝ := fun i => ‖T (b i.1)‖
  have hf_summable : Summable (fun i : {i // i ∉ S} => f i ^ 2) := by
    exact ((b.orthonormal.inner_products_summable x).subtype _)
  have hg_summable : Summable (fun i : {i // i ∉ S} => g i ^ 2) := by
    simpa [g] using Summable.subtype hT_summable {i : ι | i ∉ S}
  have hf_summable_rpow : Summable (fun i : {i // i ∉ S} => f i ^ (2 : ℝ)) := by
    simpa [Real.rpow_natCast] using hf_summable
  have hg_summable_rpow : Summable (fun i : {i // i ∉ S} => g i ^ (2 : ℝ)) := by
    simpa [Real.rpow_natCast] using hg_summable
  have hholder :=
    Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg HolderConjugate.two_two
      (fun i => norm_nonneg _)
      (fun i => norm_nonneg _)
      hf_summable_rpow
      hg_summable_rpow
  have hfg :
      ∑' i : {i // i ∉ S}, f i * g i ≤
        Real.sqrt (∑' i : {i // i ∉ S}, f i ^ 2) *
          Real.sqrt (∑' i : {i // i ∉ S}, g i ^ 2) := by
    calc
      ∑' i : {i // i ∉ S}, f i * g i
        ≤ (∑' i : {i // i ∉ S}, f i ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
            (∑' i : {i // i ∉ S}, g i ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := hholder.2
      _ = Real.sqrt (∑' i : {i // i ∉ S}, f i ^ 2) *
            Real.sqrt (∑' i : {i // i ∉ S}, g i ^ 2) := by
              simp [Real.sqrt_eq_rpow, one_div]
  have hBessel :
      ∑' i : {i // i ∉ S}, f i ^ 2 ≤ ‖x‖ ^ 2 := by
    have hsplit := (b.orthonormal.inner_products_summable x).tsum_subtype_add_tsum_subtype_compl
      {i : ι | i ∈ S}
    calc
      ∑' i : {i // i ∉ S}, f i ^ 2
        ≤ ∑' i : {i // i ∈ S}, ‖inner ℝ (b i.1) x‖ ^ 2
            + ∑' i : {i // i ∉ S}, ‖inner ℝ (b i.1) x‖ ^ 2 := by
              exact le_add_of_nonneg_left (tsum_nonneg fun i => by positivity)
      _ = ∑' i : ι, ‖inner ℝ (b i) x‖ ^ 2 := by
            simpa [f] using hsplit
      _ ≤ ‖x‖ ^ 2 := b.orthonormal.tsum_inner_products_le x
  have hsqrt :
      Real.sqrt (∑' i : {i // i ∉ S}, f i ^ 2) ≤ ‖x‖ := by
    calc
      Real.sqrt (∑' i : {i // i ∉ S}, f i ^ 2)
        ≤ Real.sqrt (‖x‖ ^ 2) := Real.sqrt_le_sqrt hBessel
      _ = ‖x‖ := by
        rw [Real.sqrt_sq_eq_abs]
        exact abs_of_nonneg (norm_nonneg _)
  have hprod_summable : Summable (fun i : {i // i ∉ S} => f i * g i) := hholder.1
  have hnorm_summable :
      Summable (fun i : {i // i ∉ S} => ‖(inner ℝ (b i.1) x) • T (b i.1)‖) := by
    simpa [f, g, norm_smul] using hprod_summable
  have hnorm :
      ‖∑' i : {i // i ∉ S}, (inner ℝ (b i.1) x) • T (b i.1)‖
        ≤ ∑' i : {i // i ∉ S}, f i * g i := by
    simpa [f, g, norm_smul] using (norm_tsum_le_tsum_norm hnorm_summable)
  calc
    ‖(T - truncatedOp b T S) x‖
      = ‖∑' i : {i // i ∉ S}, (inner ℝ (b i.1) x) • T (b i.1)‖ := by
          rw [sub_truncatedOp_apply_eq_tsum b T S x]
    _ ≤ ∑' i : {i // i ∉ S}, f i * g i := hnorm
    _ ≤ Real.sqrt (∑' i : {i // i ∉ S}, f i ^ 2) *
          Real.sqrt (∑' i : {i // i ∉ S}, g i ^ 2) := hfg
    _ ≤ Real.sqrt (∑' i : {i // i ∉ S}, ‖T (b i.1)‖ ^ 2) * ‖x‖ := by
          simpa [g, mul_comm] using
            (mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg (∑' i : {i // i ∉ S}, g i ^ 2)))

/-- Operator-norm control by the `ℓ²` tail. -/
private theorem opNorm_sub_truncatedOp_le
    (hT_summable : Summable (fun i : ι => ‖T (b i)‖ ^ 2)) (S : Finset ι) :
    ‖T - truncatedOp b T S‖ ≤
      Real.sqrt (∑' i : {i // i ∉ S}, ‖T (b i.1)‖ ^ 2) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) ?_
  intro x
  exact norm_sub_truncatedOp_apply_le b T hT_summable S x

/-- The finite-rank truncations converge to `T` in operator norm. -/
private theorem tendsto_truncatedOp
    (hT_summable : Summable (fun i : ι => ‖T (b i)‖ ^ 2)) :
    Filter.Tendsto (fun S : Finset ι => truncatedOp b T S) Filter.atTop (nhds T) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have htail :
      Filter.Tendsto
        (fun S : Finset ι => ∑' i : {i // i ∉ S}, ‖T (b i.1)‖ ^ 2)
        Filter.atTop (nhds 0) := by
    simpa using tendsto_tsum_compl_atTop_zero (fun i : ι => ‖T (b i)‖ ^ 2)
  have hsqrt :
      Filter.Tendsto
        (fun S : Finset ι => Real.sqrt (∑' i : {i // i ∉ S}, ‖T (b i.1)‖ ^ 2))
        Filter.atTop (nhds 0) := by
    simpa using Real.continuous_sqrt.continuousAt.tendsto.comp htail
  refine squeeze_zero (fun S => norm_nonneg _) ?_ hsqrt
  intro S
  simpa [norm_sub_rev] using opNorm_sub_truncatedOp_le b T hT_summable S

end HSCriterion

/-- **Hilbert-Schmidt criterion for compactness.**

A bounded operator `T` on a real Hilbert space is compact whenever there exists
a Hilbert basis `b` such that `Σᵢ ‖T (bᵢ)‖²` is summable.

**Reference**: Reed-Simon I (1980), Theorem VI.22(a) (Hilbert-Schmidt operators
are compact).

**Proof sketch**: Define finite-rank truncations `T_S x := Σ_{i ∈ S} ⟨bᵢ, x⟩ •
(T bᵢ)` for `S : Finset ι` (see `truncatedOp` above). The range of `T_S` lies
in the finite-dimensional subspace `span{T bᵢ : i ∈ S}`, hence has compact
closure on bounded sets, so `T_S` is compact (proved as
`truncatedOp_isCompactOperator`). The Bessel residual gives
`‖T - T_S‖²_{op} ≤ Σ_{i ∉ S} ‖T bᵢ‖²`, which tends to `0` along
`(Filter.atTop : Filter (Finset ι))` by summability. By
`isCompactOperator_of_tendsto`, `T` is compact.

Both halves are discharged: `truncatedOp_isCompactOperator` for compactness
of each `T_S`, and `tendsto_truncatedOp` for the Bessel-residual operator-norm
convergence. -/
theorem isCompactOperator_of_basis_norm_summable
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {ι : Type*} (b : HilbertBasis ι ℝ H)
    (T : H →L[ℝ] H)
    (hT_summable : Summable (fun i : ι => ‖T (b i)‖ ^ 2)) :
    IsCompactOperator T := by
  refine isCompactOperator_of_tendsto
    (F := fun S : Finset ι => truncatedOp b T S)
    (f := T)
    (tendsto_truncatedOp b T hT_summable) ?_
  filter_upwards [Filter.Eventually.of_forall (fun S : Finset ι =>
    truncatedOp_isCompactOperator b T S)] with S hS
  exact hS

/-! ## Convolution-to-standard-form bridge (proved)

The substitution `(x, y) ↦ (x, x − y)` is a measure-preserving automorphism of
`μ ⊗ μ` for any Haar measure `μ`. This lets us rewrite a convolution-form
kernel `K(x, t)` as a standard-form kernel `K_std(x, y) := K(x, x − y)` without
changing the induced operator or the kernel's `L²(μ⊗μ)` norm. -/

/-- The standard-form kernel associated to a convolution-form kernel:
`Kstd x y = K x (x - y)`. -/
private def standardKernelOfConvolution {G : Type*} [Sub G]
    (K : G → G → ℝ) : G → G → ℝ :=
  fun x y => K x (x - y)

/-- The change of variables `(x, y) ↦ (x, x - y)` preserves `μ.prod μ`. -/
private theorem measurePreserving_standardKernelOfConvolution
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [MeasurableSpace G] [BorelSpace G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    {μ : Measure G} [μ.IsAddHaarMeasure] :
    MeasurePreserving (fun z : G × G => (z.1, z.1 - z.2)) (μ.prod μ) (μ.prod μ) := by
  let ψ : G × G → G × G := fun z => (z.1, z.2 - z.1)
  have hψ : MeasurePreserving ψ (μ.prod μ) (μ.prod μ) := by
    simpa [ψ, sub_eq_add_neg] using (measurePreserving_prod_sub (μ := μ) (ν := μ))
  have hneg : MeasurePreserving (fun z : G × G => (z.1, -z.2)) (μ.prod μ) (μ.prod μ) := by
    exact MeasurePreserving.prod (MeasurePreserving.id (μ := μ))
      (Measure.measurePreserving_neg (μ := μ))
  convert hneg.comp hψ using 1
  ext z
  · rfl
  · change z.1 - z.2 = -((z.2 - z.1))
    abel

/-- The standard-form kernel has the same `L²` membership as the convolution-form kernel. -/
private theorem standardKernelOfConvolution_memLp
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [MeasurableSpace G] [BorelSpace G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    {μ : Measure G} [μ.IsAddHaarMeasure]
    (K : G → G → ℝ)
    (hK : MemLp (Function.uncurry K) 2 (μ.prod μ)) :
    MemLp (Function.uncurry (standardKernelOfConvolution K)) 2 (μ.prod μ) := by
  change MemLp (fun z : G × G => K z.1 (z.1 - z.2)) 2 (μ.prod μ)
  simpa [Function.comp, Function.uncurry] using
    hK.comp_measurePreserving (measurePreserving_standardKernelOfConvolution (μ := μ))

/-- For fixed `x`, the substitution `y = x - t` rewrites the convolution-form integral as the
standard-form integral. -/
private theorem convolution_integral_eq_standard_integral
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [MeasurableSpace G] [BorelSpace G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    {μ : Measure G} [μ.IsAddHaarMeasure]
    (K : G → G → ℝ) (f : G → ℝ) (x : G) :
    (∫ t, K x t * f (x - t) ∂μ) = ∫ y, standardKernelOfConvolution K x y * f y ∂μ := by
  let g : G → ℝ := fun y => standardKernelOfConvolution K x y * f y
  have hmp : MeasurePreserving (fun y : G => x - y) μ μ :=
    Measure.measurePreserving_sub_left (μ := μ) x
  simpa [g, standardKernelOfConvolution, sub_sub_cancel] using
    MeasurePreserving.integral_comp hmp (measurableEmbedding_subLeft x) g

/-- The convolution-form a.e. representation of `T` rewrites to the standard form with
`standardKernelOfConvolution K`. -/
private theorem convolution_ae_eq_standard
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [MeasurableSpace G] [BorelSpace G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    {μ : Measure G} [μ.IsAddHaarMeasure]
    (K : G → G → ℝ)
    (T : (Lp ℝ 2 μ) →L[ℝ] (Lp ℝ 2 μ))
    (hT : ∀ f : Lp ℝ 2 μ,
      (T f : G → ℝ) =ᵐ[μ] fun x => ∫ t, K x t * (f : G → ℝ) (x - t) ∂μ) :
    ∀ f : Lp ℝ 2 μ,
      (T f : G → ℝ) =ᵐ[μ] fun x =>
        ∫ y, standardKernelOfConvolution K x y * (f : G → ℝ) y ∂μ := by
  intro f
  refine (hT f).trans ?_
  exact Filter.Eventually.of_forall (fun x =>
    convolution_integral_eq_standard_integral (μ := μ) K (f : G → ℝ) x)

-- `L²(μ)` admits a Hilbert basis indexed by a `Set (Lp ℝ 2 μ)`. This is just
-- `_root_.exists_hilbertBasis` specialised; we inline its use below to avoid
-- universe-polymorphism juggling around an explicit existential wrapper.

/-! ## Main theorem -/

/-- **Hilbert-Schmidt compactness in standard kernel form.**

The standard-form integral operator with kernel `K ∈ L²(μ ⊗ μ)` is compact.

This composes the two helper theorems `hs_basis_norm_summable` (kernel ⟹
summable basis norms) and `isCompactOperator_of_basis_norm_summable`
(summable basis norms ⟹ compact operator). -/
private theorem integral_operator_l2_kernel_compact_standard
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [MeasurableSpace G] [BorelSpace G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    {μ : Measure G} [μ.IsAddHaarMeasure]
    (K : G → G → ℝ)
    (hK : MemLp (Function.uncurry K) 2 (μ.prod μ))
    (T : (Lp ℝ 2 μ) →L[ℝ] (Lp ℝ 2 μ))
    (hT : ∀ f : Lp ℝ 2 μ,
      (T f : G → ℝ) =ᵐ[μ] fun x => ∫ y, K x y * (f : G → ℝ) y ∂μ) :
    IsCompactOperator T := by
  obtain ⟨w, b, _⟩ := _root_.exists_hilbertBasis (𝕜 := ℝ) (E := Lp ℝ 2 μ)
  exact isCompactOperator_of_basis_norm_summable b T
    (hs_basis_norm_summable K hK T hT b)

/-- **Hilbert-Schmidt compactness theorem (convolution-kernel form).**

If `K ∈ L²(μ ⊗ μ)` is a real-valued kernel on a locally compact, second-countable,
T₂ normed space `G` with Haar measure `μ`, and `T : L²(μ) → L²(μ)` is a
continuous linear map representing the convolution-style integral operator
`(T f)(x) = ∫ K(x, t) f(x − t) dμ(t)` a.e., then `T` is compact.

The convolution form is reduced to the standard form via the Haar-invariant
substitution `(x, y) ↦ (x, x − y)`, then `integral_operator_l2_kernel_compact_standard`
finishes via the two helper theorems above.

**Reference**: Reed-Simon I, Theorem VI.23. -/
theorem integral_operator_l2_kernel_compact
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [MeasurableSpace G] [BorelSpace G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    {μ : Measure G} [μ.IsAddHaarMeasure]
    (K : G → G → ℝ)
    (hK : MemLp (Function.uncurry K) 2 (μ.prod μ))
    (T : (Lp ℝ 2 μ) →L[ℝ] (Lp ℝ 2 μ))
    (hT : ∀ f : Lp ℝ 2 μ,
      (T f : G → ℝ) =ᵐ[μ] fun x => ∫ t, K x t * (f : G → ℝ) (x - t) ∂μ) :
    IsCompactOperator T := by
  exact integral_operator_l2_kernel_compact_standard
    (standardKernelOfConvolution K)
    (standardKernelOfConvolution_memLp (μ := μ) K hK)
    T
    (convolution_ae_eq_standard (μ := μ) K T hT)

end

end Pphi2.GeneralResults
