/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Pphi2.AsymTorus.AsymNormalizedKernelSymmetry

/-!
# Semigroup composition for normalized transfer kernels

The transfer-system kernel `kPow m` represents the `(m+1)`-st transfer power.
This file proves its pointwise composition law with the corresponding index
shift.  After dividing by the ground eigenvalue powers, the normalized kernel
obeys the same law.

The Fubini step uses the finite-lattice product-weight estimate.  No uniform
continuum estimate enters this argument.
-/

noncomputable section

open MeasureTheory ReflectionPositivity

namespace Pphi2

variable {Nt Ns : ℕ} [NeZero Nt] [NeZero Ns]

/-- The triple kernel occurring in the composition proof is integrable on the
two intermediate spatial slices. -/
private theorem asymTransferKernel_kPow_comp_integrable
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (m n : ℕ) (x y : SpatialField Ns) :
    Integrable
      (Function.uncurry (fun w z : SpatialField Ns =>
        (asymTransferSystem Nt Ns P a mass ha hmass).kPow m x z *
          (asymTransferSystem Nt Ns P a mass ha hmass).kPow n z w *
          (asymTransferSystem Nt Ns P a mass ha hmass).k w y))
      ((volume : Measure (SpatialField Ns)).prod volume) := by
  let Ts := asymTransferSystem Nt Ns P a mass ha hmass
  let W := asymTransferWeight Nt Ns P a mass
  let S := asymTransferWeightSqMass (Nt := Nt) (Ns := Ns) P a mass
  let C := S ^ m * S ^ n * W x * W y
  have hW_nonneg : ∀ u, 0 ≤ W u :=
    fun u => (asymTransferWeight_pos Nt Ns P a mass u).le
  have hS_nonneg : 0 ≤ S :=
    asymTransferWeightSqMass_nonneg (Nt := Nt) (Ns := Ns) P a mass
  have hW_sq : Integrable (fun u => W u ^ 2) volume :=
    (asymTransferWeight_memLp_two Nt Ns P a mass ha hmass).integrable_sq
  have hbase : Integrable
      (fun p : SpatialField Ns × SpatialField Ns => W p.1 ^ 2 * W p.2 ^ 2)
      (volume.prod volume) :=
    hW_sq.mul_prod hW_sq
  have hdom : Integrable
      (fun p : SpatialField Ns × SpatialField Ns =>
        C * (W p.1 ^ 2 * W p.2 ^ 2))
      (volume.prod volume) :=
    hbase.const_mul C
  have hm_meas : Measurable
      (Function.uncurry (Ts.kPow m)) := by
    simpa only [Ts] using
      asymTransferKernel_kPow_measurable
        (Nt := Nt) (Ns := Ns) P a mass ha hmass m
  have hn_meas : Measurable
      (Function.uncurry (Ts.kPow n)) := by
    simpa only [Ts] using
      asymTransferKernel_kPow_measurable
        (Nt := Nt) (Ns := Ns) P a mass ha hmass n
  have hintegrand_meas : Measurable
      (Function.uncurry (fun w z : SpatialField Ns =>
        Ts.kPow m x z * Ts.kPow n z w * Ts.k w y)) := by
    have hm' : Measurable
        (fun p : SpatialField Ns × SpatialField Ns => Ts.kPow m x p.2) :=
      hm_meas.comp (measurable_const.prodMk measurable_snd)
    have hn' : Measurable
        (fun p : SpatialField Ns × SpatialField Ns => Ts.kPow n p.2 p.1) :=
      hn_meas.comp (measurable_snd.prodMk measurable_fst)
    have hk' : Measurable
        (fun p : SpatialField Ns × SpatialField Ns => Ts.k p.1 y) :=
      Ts.k_meas.comp (measurable_fst.prodMk measurable_const)
    exact (hm'.mul hn').mul hk'
  refine hdom.mono' hintegrand_meas.aestronglyMeasurable
    (.of_forall fun p => ?_)
  obtain ⟨w, z⟩ := p
  simp only [Function.uncurry_apply_pair]
  have hm_le : Ts.kPow m x z ≤ S ^ m * W x * W z := by
    simpa only [Ts, S, W] using
      asymTransferKernel_kPow_le_weight_product
        (Nt := Nt) (Ns := Ns) P a mass ha hmass m x z
  have hn_le : Ts.kPow n z w ≤ S ^ n * W z * W w := by
    simpa only [Ts, S, W] using
      asymTransferKernel_kPow_le_weight_product
        (Nt := Nt) (Ns := Ns) P a mass ha hmass n z w
  have hk_le : Ts.k w y ≤ W w * W y := by
    simpa only [Ts, W] using
      asymTransferKernel_le_weight_product
        (Nt := Nt) (Ns := Ns) P a mass w y
  have hm_nonneg : 0 ≤ Ts.kPow m x z := Ts.kPow_nonneg m x z
  have hn_nonneg : 0 ≤ Ts.kPow n z w := Ts.kPow_nonneg n z w
  have hk_nonneg : 0 ≤ Ts.k w y := Ts.k_nonneg w y
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (mul_nonneg hm_nonneg hn_nonneg) hk_nonneg)]
  calc
    Ts.kPow m x z * Ts.kPow n z w * Ts.k w y ≤
        (S ^ m * W x * W z) * (S ^ n * W z * W w) * (W w * W y) := by
      have hA_nonneg : 0 ≤ S ^ m * W x * W z :=
        mul_nonneg
          (mul_nonneg (pow_nonneg hS_nonneg m) (hW_nonneg x))
          (hW_nonneg z)
      have hB_nonneg : 0 ≤ S ^ n * W z * W w :=
        mul_nonneg
          (mul_nonneg (pow_nonneg hS_nonneg n) (hW_nonneg z))
          (hW_nonneg w)
      have hAB_nonneg :
          0 ≤ (S ^ m * W x * W z) * (S ^ n * W z * W w) :=
        mul_nonneg hA_nonneg hB_nonneg
      exact mul_le_mul
        (mul_le_mul hm_le hn_le hn_nonneg hA_nonneg)
        hk_le hk_nonneg hAB_nonneg
    _ = C * (W w ^ 2 * W z ^ 2) := by ring

/-- Pointwise composition for iterated transfer kernels.  Since `kPow m` is
the kernel of the `(m+1)`-st power, composing `m` and `n` produces the index
`m+n+1`. -/
theorem asymTransferKernel_kPow_add_one_comp
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (m n : ℕ) (x y : SpatialField Ns) :
    (asymTransferSystem Nt Ns P a mass ha hmass).kPow (m + n + 1) x y =
      ∫ z, (asymTransferSystem Nt Ns P a mass ha hmass).kPow m x z *
        (asymTransferSystem Nt Ns P a mass ha hmass).kPow n z y ∂volume := by
  let Ts := asymTransferSystem Nt Ns P a mass ha hmass
  induction n generalizing y with
  | zero =>
      simp only [Nat.add_zero]
      rw [TransferSystem.kPow_zero, TransferSystem.kPow_succ]
  | succ n ih =>
      simp only [Nat.succ_eq_add_one]
      have hindex : m + (n + 1) + 1 = (m + n + 1) + 1 := by omega
      rw [hindex, TransferSystem.kPow_succ]
      calc
        (∫ w, Ts.kPow (m + n + 1) x w * Ts.k w y ∂volume) =
            ∫ w, (∫ z, Ts.kPow m x z * Ts.kPow n z w ∂volume) *
              Ts.k w y ∂volume := by
          refine integral_congr_ae (.of_forall fun w => ?_)
          rw [ih w]
        _ = ∫ w, ∫ z,
              Ts.kPow m x z * Ts.kPow n z w * Ts.k w y ∂volume ∂volume := by
          refine integral_congr_ae (.of_forall fun w => ?_)
          rw [← integral_mul_const]
          refine integral_congr_ae (.of_forall fun z => ?_)
          ring
        _ = ∫ z, ∫ w,
              Ts.kPow m x z * Ts.kPow n z w * Ts.k w y ∂volume ∂volume := by
          rw [MeasureTheory.integral_integral_swap
            (asymTransferKernel_kPow_comp_integrable
              (Nt := Nt) (Ns := Ns) P a mass ha hmass m n x y)]
        _ = ∫ z, Ts.kPow m x z * Ts.kPow (n + 1) z y ∂volume := by
          refine integral_congr_ae (.of_forall fun z => ?_)
          calc
            (∫ w, Ts.kPow m x z * Ts.kPow n z w * Ts.k w y ∂volume) =
                Ts.kPow m x z *
                  ∫ w, Ts.kPow n z w * Ts.k w y ∂volume := by
              rw [← integral_const_mul]
              refine integral_congr_ae (.of_forall fun w => ?_)
              ring
            _ = Ts.kPow m x z * Ts.kPow (n + 1) z y := by
              rw [TransferSystem.kPow_succ]

/-- The normalized transfer kernel has the semigroup composition law with the
same shifted index. -/
theorem asymNormalizedTransferKernelPower_add_one_comp
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (m n : ℕ) (x y : SpatialField Ns) :
    asymNormalizedTransferKernelPower
        (Nt := Nt) (Ns := Ns) P a mass ha hmass (m + n + 1) x y =
      ∫ z, asymNormalizedTransferKernelPower
          (Nt := Nt) (Ns := Ns) P a mass ha hmass m x z *
        asymNormalizedTransferKernelPower
          (Nt := Nt) (Ns := Ns) P a mass ha hmass n z y ∂volume := by
  let Ts := asymTransferSystem Nt Ns P a mass ha hmass
  let lam := asymTransferGroundEigenvalue Nt Ns P a mass ha hmass
  change (lam ^ (m + n + 1 + 1))⁻¹ * Ts.kPow (m + n + 1) x y =
    ∫ z, (lam ^ (m + 1))⁻¹ * Ts.kPow m x z *
      ((lam ^ (n + 1))⁻¹ * Ts.kPow n z y) ∂volume
  rw [asymTransferKernel_kPow_add_one_comp
    (Nt := Nt) (Ns := Ns) P a mass ha hmass m n x y]
  rw [← integral_const_mul]
  refine integral_congr_ae (.of_forall fun z => ?_)
  rw [show m + n + 1 + 1 = (m + 1) + (n + 1) by omega, pow_add, mul_inv]
  ring

end Pphi2
