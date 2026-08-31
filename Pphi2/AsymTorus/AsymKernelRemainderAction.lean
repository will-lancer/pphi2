/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.AsymTorus.AsymTraceBridge
import ReflectionPositivity.GroundBridge

/-!
# The asymmetric transfer-kernel remainder action

The generic `ReflectionPositivity.kernelRemainder` is defined by subtracting
the rank-one ground kernel from an iterated transfer kernel.  This file gives
the concrete asymmetric-torus operator whose a.e. action is that remainder.
The slice integrability needed to split the two integrals is exposed by
`asymTransferKernel_kPow_slice_integrable` in
`AsymTransferKernelOperator.lean`.
-/

open MeasureTheory
open ReflectionPositivity

namespace Pphi2

variable {Nt Ns : ℕ} [NeZero Nt] [NeZero Ns]

/-- The unnormalised asymmetric-torus kernel remainder at power `m`. -/
noncomputable def asymTransferKernelRemainder
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (m : ℕ) (x y : SpatialField Ns) : ℝ :=
  kernelRemainder
    (asymTransferSystem Nt Ns P a mass ha hmass)
    (asymGroundVector Nt Ns P a mass ha hmass)
    (asymTransferGroundEigenvalue Nt Ns P a mass ha hmass) m x y

/-- The operator obtained by removing the ground rank-one contribution from
the `(m+1)`-st asymmetric transfer power. -/
noncomputable def asymTransferRemainderCLM
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (m : ℕ) : L2SpatialField Ns →L[ℝ] L2SpatialField Ns :=
  (asymTransferOperatorCLM Nt Ns P a mass ha hmass) ^ (m + 1) -
    (asymTransferGroundEigenvalue Nt Ns P a mass ha hmass ^ (m + 1)) •
      InnerProductSpace.rankOne ℝ
        (asymGroundVector Nt Ns P a mass ha hmass)
        (asymGroundVector Nt Ns P a mass ha hmass)

/-- The unnormalised rank-one split in the concrete asymmetric-torus
notation. -/
theorem asymTransferKernel_rankOne_split
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (m : ℕ) (x y : SpatialField Ns) :
    (asymTransferSystem Nt Ns P a mass ha hmass).kPow m x y =
      (asymTransferGroundEigenvalue Nt Ns P a mass ha hmass) ^ (m + 1) *
          (asymGroundVector Nt Ns P a mass ha hmass) x *
          (asymGroundVector Nt Ns P a mass ha hmass) y +
        asymTransferKernelRemainder Nt Ns P a mass ha hmass m x y := by
  simpa only [asymTransferKernelRemainder, kernelRemainder, rankOneKernel]
    using rankOne_kernel_split
      (asymTransferSystem Nt Ns P a mass ha hmass)
      (asymGroundVector Nt Ns P a mass ha hmass)
      (asymTransferGroundEigenvalue Nt Ns P a mass ha hmass) m x y

/-- The kernel remainder acts as the transfer power with its ground
projection removed, almost everywhere on the spatial slice. -/
theorem asymTransferKernelRemainder_apply
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (m : ℕ) (f : L2SpatialField Ns) :
    (⇑(asymTransferRemainderCLM Nt Ns P a mass ha hmass m f) :
        SpatialField Ns → ℝ) =ᵐ[volume]
      (fun x => ∫ y,
        asymTransferKernelRemainder Nt Ns P a mass ha hmass m x y * f y ∂volume) := by
  let Ts := asymTransferSystem Nt Ns P a mass ha hmass
  let Ω := asymGroundVector Nt Ns P a mass ha hmass
  let λ := asymTransferGroundEigenvalue Nt Ns P a mass ha hmass
  let Tpow := (asymTransferOperatorCLM Nt Ns P a mass ha hmass) ^ (m + 1)
  let P0 := (λ ^ (m + 1)) • InnerProductSpace.rankOne ℝ Ω Ω
  have hT : (⇑(Tpow f) : SpatialField Ns → ℝ) =ᵐ[volume]
      (fun x => ∫ y, Ts.kPow m x y * f y ∂volume) := by
    simpa only [Tpow, Ts] using
      asymTransferKernel_kPow_apply Nt Ns P a mass ha hmass m f
  have hP0 : (⇑(P0 f) : SpatialField Ns → ℝ) =ᵐ[volume]
      (fun x => λ ^ (m + 1) * (@inner ℝ _ _ Ω f) * Ω x) := by
    rw [ContinuousLinearMap.smul_apply, InnerProductSpace.rankOne_apply, smul_smul]
    filter_upwards [Lp.coeFn_smul (λ ^ (m + 1) * @inner ℝ _ _ Ω f) Ω] with x hx
    simpa [smul_eq_mul] using hx
  have hsub :
      (⇑(Tpow f - P0 f) : SpatialField Ns → ℝ) =ᵐ[volume]
        (fun x => (Tpow f) x - (P0 f) x) :=
    Lp.coeFn_sub _ _
  have hinner : @inner ℝ _ _ Ω f = ∫ y, Ω y * f y ∂volume := by
    rw [MeasureTheory.L2.inner_def]
    simp only [Real.inner_apply]
  have hΩf : Integrable (fun y => Ω y * f y) volume :=
    (Lp.memLp Ω).integrable_mul (Lp.memLp f)
  change (⇑(Tpow f - P0 f) : SpatialField Ns → ℝ) =ᵐ[volume]
    (fun x => ∫ y,
      kernelRemainder Ts Ω λ m x y * f y ∂volume)
  filter_upwards [hT, hP0, hsub] with x hTx hP0x hsubx
  have hKf : Integrable (fun y => Ts.kPow m x y * f y) volume :=
    asymTransferKernel_kPow_slice_integrable Nt Ns P a mass ha hmass m x f
  have hground : Integrable
      (fun y => λ ^ (m + 1) * Ω x * (Ω y * f y)) volume :=
    hΩf.const_mul (λ ^ (m + 1) * Ω x)
  calc
    (Tpow f - P0 f : L2SpatialField Ns) x = (Tpow f) x - (P0 f) x := hsubx
    _ = (∫ y, Ts.kPow m x y * f y ∂volume) -
          λ ^ (m + 1) * (@inner ℝ _ _ Ω f) * Ω x := by
      rw [hTx, hP0x]
    _ = (∫ y,
          (kernelRemainder Ts Ω λ m x y * f y +
            λ ^ (m + 1) * Ω x * (Ω y * f y)) ∂volume) -
          λ ^ (m + 1) * (@inner ℝ _ _ Ω f) * Ω x := by
      congr 2
      refine integral_congr_ae (.of_forall fun y => ?_)
      simp only [kernelRemainder, rankOneKernel, asymTransferKernelRemainder]
      ring
    _ = ((∫ y, kernelRemainder Ts Ω λ m x y * f y ∂volume) +
          ∫ y, λ ^ (m + 1) * Ω x * (Ω y * f y) ∂volume) -
          λ ^ (m + 1) * (@inner ℝ _ _ Ω f) * Ω x := by
      rw [integral_add hKf hground]
    _ = ∫ y, kernelRemainder Ts Ω λ m x y * f y ∂volume := by
      rw [integral_const_mul, ← hinner]
      ring

end Pphi2
