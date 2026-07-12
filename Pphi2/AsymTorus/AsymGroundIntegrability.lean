/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.AsymTorus.AsymObsTrunc

/-!
# Layer-B2 Stage C, task C2: ground-vector slice-observable L² integrability

Discharges the recurring hypothesis `hInt` of the Route-A pieces: for every
spatial test vector `g`, the function `ψ ↦ ⟨g, ψ⟩² · Ω(ψ)²` is integrable on
`(SpatialField Ns, volume)`, where `Ω = asymGroundVector` is the Jentzsch
ground state of the asym transfer operator. Equivalently, `M_g Ω ∈ L²(volume)`
for the (unbounded) linear slice observable `A_g(ψ) = ⟨g, ψ⟩`.

## Route (the plan's C2 smoothing argument)

The proof uses the transfer-kernel smoothing of the ground state, not the
path-measure marginal: since `T Ω = λ₀ Ω` with `λ₀ > 0` and `T` is the
integral operator with kernel `k(x,y) = w(x)·G(x−y)·w(y)`
(`asymTransferOperatorCLM_apply`), the eigen-identity gives, a.e. in `x`,

`|Ω(x)| = λ₀⁻¹ |∫ k(x,y) Ω(y) dy| ≤ λ₀⁻¹ w(x) ∫ w(y)|Ω(y)| dy = C·w(x)`,

using `0 < G ≤ 1` and `w·|Ω| ∈ L¹` (both factors are in `L²`). The weight `w`
has explicit Gaussian decay (`asymTransferWeight_gaussian_decay`), so
`⟨g,ψ⟩²·w(ψ)²` is integrable by finite-dimensional Cauchy–Schwarz plus a
product-Gaussian dominator, and `⟨g,ψ⟩²·Ω(ψ)² ≤ C²·⟨g,ψ⟩²·w(ψ)²` a.e. closes
the claim by domination. No truncation limit or marginal-density
identification is needed: the domination is direct and `K`-free.

## Main declarations

* `asymGroundVector_abs_le_weight` — `|Ω| ≤ C·w` a.e. for some `C ≥ 0`.
* `asymSliceObsLinear_sq_mul_weight_sq_integrable` — `⟨g,·⟩²·w² ∈ L¹(volume)`.
* `asymGroundVector_sliceObs_sq_integrable` — **the `hInt` discharge**:
  `⟨g,·⟩²·Ω² ∈ L¹(volume)` for every `g : SpatialField Ns`.
* `asymGroundVector_sliceObs_sq_integrable_family` — the slice-family form
  `∀ t, ⟨g t,·⟩²·Ω² ∈ L¹(volume)` consumed by the Route-A assembly.

## References

* Glimm–Jaffe Ch. 6, 18: regularity of transfer-matrix ground states.
* `planning/b2-stageB-holes-spec.md`, §"Stage C work plan", task C2.
-/

open MeasureTheory

namespace Pphi2

variable (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]

/-! ## Kernel-versus-weight bound (local copies of private upstream lemmas) -/

private theorem transferGaussian_le_one_local (z : SpatialField Ns) :
    transferGaussian Ns z ≤ 1 := by
  simpa [Real.norm_eq_abs, abs_of_pos (transferGaussian_pos Ns z)] using
    transferGaussian_norm_le_one Ns z

/-- `k(x,y) ≤ w(x)·w(y)`: the Gaussian factor of the transfer kernel is at most `1`. -/
private theorem asymTransferKernel_le_weight_prod (P : InteractionPolynomial) (a mass : ℝ)
    (x y : SpatialField Ns) :
    asymTransferKernel Nt Ns P a mass x y ≤
      asymTransferWeight Nt Ns P a mass x * asymTransferWeight Nt Ns P a mass y := by
  have hG : transferGaussian Ns (x - y) ≤ 1 := transferGaussian_le_one_local Ns (x - y)
  have hx : 0 ≤ asymTransferWeight Nt Ns P a mass x :=
    (asymTransferWeight_pos Nt Ns P a mass x).le
  have hy : 0 ≤ asymTransferWeight Nt Ns P a mass y :=
    (asymTransferWeight_pos Nt Ns P a mass y).le
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hG hx) hy
  simpa [asymTransferKernel, mul_assoc] using h

/-! ## The ground state is dominated by the transfer weight -/

/-- **Ground-state smoothing bound.** The Jentzsch ground vector is dominated a.e. by a
constant multiple of the transfer weight: `|Ω(x)| ≤ C·w(x)`.

From the eigen-identity `Ω = λ₀⁻¹ T Ω` and the integral-operator form of `T`
(`asymTransferOperatorCLM_apply`), a.e. in `x`,
`|Ω(x)| = λ₀⁻¹|∫ w(x)G(x−y)w(y)Ω(y) dy| ≤ λ₀⁻¹ w(x) ∫ w|Ω|`,
using `0 < G ≤ 1` and `w·|Ω| ∈ L¹` (product of two `L²` functions). -/
theorem asymGroundVector_abs_le_weight (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᵐ x ∂(volume : Measure (SpatialField Ns)),
        |(asymGroundVector Nt Ns P a mass ha hmass) x| ≤
          C * asymTransferWeight Nt Ns P a mass x := by
  set Ω := asymGroundVector Nt Ns P a mass ha hmass with hΩ_def
  have hlam : 0 < asymTransferGroundEigenvalue Nt Ns P a mass ha hmass :=
    asymTransferGroundEigenvalue_pos Nt Ns P a mass ha hmass
  have hw_pos : ∀ ψ, 0 < asymTransferWeight Nt Ns P a mass ψ :=
    asymTransferWeight_pos Nt Ns P a mass
  -- `w·|Ω|` is integrable (product of two `L²` functions).
  have hwΩ : Integrable (fun y => asymTransferWeight Nt Ns P a mass y * Ω y) volume :=
    (asymTransferWeight_memLp_two Nt Ns P a mass ha hmass).integrable_mul (Lp.memLp Ω)
  have hwΩabs : Integrable (fun y => asymTransferWeight Nt Ns P a mass y * |Ω y|) volume := by
    refine hwΩ.abs.congr (Filter.Eventually.of_forall fun y => ?_)
    show |asymTransferWeight Nt Ns P a mass y * Ω y| =
      asymTransferWeight Nt Ns P a mass y * |Ω y|
    rw [abs_mul, abs_of_nonneg (hw_pos y).le]
  set C₀ := ∫ y, asymTransferWeight Nt Ns P a mass y * |Ω y| ∂volume with hC₀_def
  have hC₀ : 0 ≤ C₀ :=
    integral_nonneg fun y => mul_nonneg (hw_pos y).le (abs_nonneg _)
  refine ⟨(asymTransferGroundEigenvalue Nt Ns P a mass ha hmass)⁻¹ * C₀,
    mul_nonneg (inv_nonneg.mpr hlam.le) hC₀, ?_⟩
  -- The eigen-identity, in pointwise a.e. form.
  have h1 : (⇑(asymTransferOperatorCLM Nt Ns P a mass ha hmass Ω) : SpatialField Ns → ℝ)
      =ᵐ[volume]
        (fun x => ∫ y, asymTransferKernel Nt Ns P a mass x y * Ω y ∂volume) :=
    asymTransferOperatorCLM_apply Nt Ns P a mass ha hmass Ω
  have heig : asymTransferOperatorCLM Nt Ns P a mass ha hmass Ω =
      asymTransferGroundEigenvalue Nt Ns P a mass ha hmass • Ω :=
    asymTransferOperatorCLM_groundVector P a mass ha hmass
  rw [heig] at h1
  have h2 : (⇑(asymTransferGroundEigenvalue Nt Ns P a mass ha hmass • Ω)
      : SpatialField Ns → ℝ) =ᵐ[volume]
        (fun x => asymTransferGroundEigenvalue Nt Ns P a mass ha hmass * Ω x) := by
    filter_upwards [Lp.coeFn_smul (asymTransferGroundEigenvalue Nt Ns P a mass ha hmass) Ω]
      with x hx
    simpa [smul_eq_mul] using hx
  filter_upwards [h2.symm.trans h1] with x hx
  -- `hx : λ₀ * Ω x = ∫ y, k x y * Ω y dy`.
  have hbound : |∫ y, asymTransferKernel Nt Ns P a mass x y * Ω y ∂volume| ≤
      asymTransferWeight Nt Ns P a mass x * C₀ := by
    have habs : |∫ y, asymTransferKernel Nt Ns P a mass x y * Ω y ∂volume| ≤
        ∫ y, |asymTransferKernel Nt Ns P a mass x y * Ω y| ∂volume := by
      simpa [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (fun y => asymTransferKernel Nt Ns P a mass x y * Ω y)
    have hpt : ∀ y, |asymTransferKernel Nt Ns P a mass x y * Ω y| ≤
        asymTransferWeight Nt Ns P a mass x *
          (asymTransferWeight Nt Ns P a mass y * |Ω y|) := by
      intro y
      rw [abs_mul, abs_of_nonneg (asymTransferKernel_nonneg Nt Ns P a mass x y)]
      calc asymTransferKernel Nt Ns P a mass x y * |Ω y|
          ≤ (asymTransferWeight Nt Ns P a mass x * asymTransferWeight Nt Ns P a mass y) *
              |Ω y| :=
            mul_le_mul_of_nonneg_right
              (asymTransferKernel_le_weight_prod Nt Ns P a mass x y) (abs_nonneg _)
        _ = asymTransferWeight Nt Ns P a mass x *
              (asymTransferWeight Nt Ns P a mass y * |Ω y|) := by ring
    have hmono : ∫ y, |asymTransferKernel Nt Ns P a mass x y * Ω y| ∂volume ≤
        ∫ y, asymTransferWeight Nt Ns P a mass x *
          (asymTransferWeight Nt Ns P a mass y * |Ω y|) ∂volume :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => abs_nonneg _)
        (hwΩabs.const_mul (asymTransferWeight Nt Ns P a mass x))
        (Filter.Eventually.of_forall hpt)
    calc |∫ y, asymTransferKernel Nt Ns P a mass x y * Ω y ∂volume|
        ≤ ∫ y, |asymTransferKernel Nt Ns P a mass x y * Ω y| ∂volume := habs
      _ ≤ ∫ y, asymTransferWeight Nt Ns P a mass x *
            (asymTransferWeight Nt Ns P a mass y * |Ω y|) ∂volume := hmono
      _ = asymTransferWeight Nt Ns P a mass x * C₀ := integral_const_mul _ _
  calc |Ω x|
      = (asymTransferGroundEigenvalue Nt Ns P a mass ha hmass)⁻¹ *
          |asymTransferGroundEigenvalue Nt Ns P a mass ha hmass * Ω x| := by
        rw [abs_mul, abs_of_pos hlam, ← mul_assoc, inv_mul_cancel₀ hlam.ne', one_mul]
    _ = (asymTransferGroundEigenvalue Nt Ns P a mass ha hmass)⁻¹ *
          |∫ y, asymTransferKernel Nt Ns P a mass x y * Ω y ∂volume| := by rw [hx]
    _ ≤ (asymTransferGroundEigenvalue Nt Ns P a mass ha hmass)⁻¹ *
          (asymTransferWeight Nt Ns P a mass x * C₀) :=
        mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hlam.le)
    _ = ((asymTransferGroundEigenvalue Nt Ns P a mass ha hmass)⁻¹ * C₀) *
          asymTransferWeight Nt Ns P a mass x := by ring

/-! ## Slice observable squared against the weight squared is integrable -/

/-- `⟨g,·⟩²·w² ∈ L¹(volume)`: the transfer weight's Gaussian decay
(`asymTransferWeight_gaussian_decay`) beats the quadratic growth of the squared slice
observable. Finite-dimensional Cauchy–Schwarz gives `⟨g,ψ⟩² ≤ ‖g‖²·Σψₓ²`, and
`u·e^{−βu} ≤ β⁻¹` absorbs the polynomial into one Gaussian factor. -/
theorem asymSliceObsLinear_sq_mul_weight_sq_integrable
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (g : SpatialField Ns) :
    Integrable (fun ψ => (asymSliceObsLinear g ψ) ^ 2 *
      (asymTransferWeight Nt Ns P a mass ψ) ^ 2) volume := by
  obtain ⟨A, hA, hdecay⟩ := asymTransferWeight_gaussian_decay Nt Ns P a mass ha hmass
  set K := Real.exp ((a ^ 2 / 2) * (↑Ns * A)) with hK_def
  set β := a ^ 2 * mass ^ 2 / 4 with hβ_def
  have hβ : 0 < β := by rw [hβ_def]; positivity
  set Gsq := ∑ i, (g i) ^ 2 with hGsq_def
  have hGsq : 0 ≤ Gsq := Finset.sum_nonneg fun i _ => sq_nonneg _
  -- The Gaussian dominator is integrable (product of 1D Gaussians).
  have hdom : Integrable
      (fun ψ : SpatialField Ns => Real.exp (-β * ∑ x, (ψ x) ^ 2)) volume := by
    have hrw : (fun ψ : SpatialField Ns => Real.exp (-β * ∑ x, (ψ x) ^ 2))
        = fun ψ => ∏ x : Fin Ns, Real.exp (-β * (ψ x) ^ 2) := by
      funext ψ
      rw [Finset.mul_sum, Real.exp_sum]
    rw [hrw, show (volume : Measure (SpatialField Ns)) =
        Measure.pi (fun _ : Fin Ns => (volume : Measure ℝ)) from rfl]
    exact Integrable.fintype_prod fun _ => integrable_exp_neg_mul_sq hβ
  refine (hdom.const_mul (Gsq * K ^ 2 * β⁻¹)).mono' ?_ ?_
  · exact (((asymSliceObsLinear_measurable g).pow_const 2).mul
      ((asymTransferWeight_measurable Nt Ns P a mass).pow_const 2)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun ψ => ?_
    set u := ∑ x, (ψ x) ^ 2 with hu_def
    have hu : 0 ≤ u := Finset.sum_nonneg fun x _ => sq_nonneg _
    set E := Real.exp (-β * u) with hE_def
    have hE : 0 < E := Real.exp_pos _
    have hw := hdecay ψ
    rw [← hu_def, ← hE_def] at hw
    -- Cauchy–Schwarz: `⟨g,ψ⟩² ≤ Gsq · u`.
    have h1 : (asymSliceObsLinear g ψ) ^ 2 ≤ Gsq * u := by
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ g ψ
      rw [hGsq_def, hu_def]
      unfold asymSliceObsLinear
      exact hcs
    -- Weight decay squared: `w² ≤ K²·E²`.
    have h2 : (asymTransferWeight Nt Ns P a mass ψ) ^ 2 ≤ K ^ 2 * E ^ 2 := by
      have hsq := pow_le_pow_left₀ (asymTransferWeight_pos Nt Ns P a mass ψ).le hw 2
      rwa [mul_pow] at hsq
    -- `u·E ≤ β⁻¹`.
    have hβu : β * u ≤ Real.exp (β * u) := by
      have := Real.add_one_le_exp (β * u)
      linarith
    have huE : u * E ≤ β⁻¹ := by
      have h3 : u ≤ β⁻¹ * Real.exp (β * u) := by
        rw [inv_mul_eq_div, le_div_iff₀ hβ]
        calc u * β = β * u := mul_comm u β
          _ ≤ Real.exp (β * u) := hβu
      have hcancel : Real.exp (β * u) * E = 1 := by
        rw [hE_def, ← Real.exp_add, neg_mul, add_neg_cancel, Real.exp_zero]
      calc u * E ≤ (β⁻¹ * Real.exp (β * u)) * E :=
            mul_le_mul_of_nonneg_right h3 hE.le
        _ = β⁻¹ * (Real.exp (β * u) * E) := by ring
        _ = β⁻¹ := by rw [hcancel, mul_one]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    calc (asymSliceObsLinear g ψ) ^ 2 * (asymTransferWeight Nt Ns P a mass ψ) ^ 2
        ≤ (Gsq * u) * (K ^ 2 * E ^ 2) :=
          mul_le_mul h1 h2 (sq_nonneg _) (mul_nonneg hGsq hu)
      _ = (Gsq * K ^ 2) * ((u * E) * E) := by ring
      _ ≤ (Gsq * K ^ 2) * (β⁻¹ * E) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right huE hE.le) (mul_nonneg hGsq (sq_nonneg K))
      _ = Gsq * K ^ 2 * β⁻¹ * E := by ring

/-! ## The `hInt` discharge -/

/-- **Ground-vector slice-observable L² integrability** (the Layer-B2 `hInt` discharge).
For every spatial test vector `g`, the squared slice observable against the squared
Jentzsch ground state is integrable: `M_{A_g} Ω ∈ L²(volume)`.

Combines `asymGroundVector_abs_le_weight` (`|Ω| ≤ C·w` a.e.) with
`asymSliceObsLinear_sq_mul_weight_sq_integrable` (`⟨g,·⟩²·w² ∈ L¹`) by domination. -/
theorem asymGroundVector_sliceObs_sq_integrable
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (g : SpatialField Ns) :
    Integrable (fun ψ => (asymSliceObsLinear g ψ) ^ 2 *
      ((asymGroundVector Nt Ns P a mass ha hmass) ψ) ^ 2) volume := by
  obtain ⟨C, hC, hae⟩ := asymGroundVector_abs_le_weight Nt Ns P a mass ha hmass
  have hdom := (asymSliceObsLinear_sq_mul_weight_sq_integrable
    Nt Ns P a mass ha hmass g).const_mul (C ^ 2)
  refine hdom.mono' ?_ ?_
  · exact (((asymSliceObsLinear_measurable g).pow_const 2).aestronglyMeasurable.mul
      ((Lp.aestronglyMeasurable (asymGroundVector Nt Ns P a mass ha hmass)).pow 2))
  · filter_upwards [hae] with ψ hψ
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    have hsq : ((asymGroundVector Nt Ns P a mass ha hmass) ψ) ^ 2 ≤
        C ^ 2 * (asymTransferWeight Nt Ns P a mass ψ) ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg _) hψ 2
      rwa [sq_abs, mul_pow] at h
    calc (asymSliceObsLinear g ψ) ^ 2 *
          ((asymGroundVector Nt Ns P a mass ha hmass) ψ) ^ 2
        ≤ (asymSliceObsLinear g ψ) ^ 2 *
            (C ^ 2 * (asymTransferWeight Nt Ns P a mass ψ) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
      _ = C ^ 2 * ((asymSliceObsLinear g ψ) ^ 2 *
            (asymTransferWeight Nt Ns P a mass ψ) ^ 2) := by ring

/-- Slice-family form of the `hInt` discharge, matching the recurring hypothesis of the
Route-A susceptibility theorems verbatim. -/
theorem asymGroundVector_sliceObs_sq_integrable_family
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (g : ZMod Nt → SpatialField Ns) :
    ∀ t : ZMod Nt, Integrable (fun ψ => (asymSliceObsLinear (g t) ψ) ^ 2 *
      ((asymGroundVector Nt Ns P a mass ha hmass) ψ) ^ 2) volume :=
  fun t => asymGroundVector_sliceObs_sq_integrable Nt Ns P a mass ha hmass (g t)

end Pphi2
