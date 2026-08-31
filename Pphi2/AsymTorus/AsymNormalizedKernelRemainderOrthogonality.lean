/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Pphi2.AsymTorus.AsymNormalizedKernelSymmetry
import Pphi2.AsymTorus.AsymTraceKernelRemainder

/-!
# Orthogonality of the normalized transfer-kernel remainder

The kernel symmetry from `AsymNormalizedKernelSymmetry` also applies to the
rank-one-subtracted remainder.  The kernel representation of the remainder
operator then gives the row orthogonality relation against the normalized
ground vector.  This is a finite-lattice identity; no uniform trace or IUC
estimate is used here.
-/

noncomputable section

open MeasureTheory

namespace Pphi2

variable {Nt Ns : ℕ} [NeZero Nt] [NeZero Ns]

/-- The normalized transfer-kernel remainder is symmetric in its endpoints. -/
theorem asymNormalizedTransferKernelRemainder_symm
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (m : ℕ) (x y : SpatialField Ns) :
    asymNormalizedTransferKernelRemainder
        (Nt := Nt) (Ns := Ns) P a mass ha hmass m x y =
      asymNormalizedTransferKernelRemainder
        (Nt := Nt) (Ns := Ns) P a mass ha hmass m y x := by
  unfold asymNormalizedTransferKernelRemainder
  rw [asymNormalizedTransferKernelPower_symm]
  ring

/-- Each row of the normalized remainder is orthogonal to the ground vector.

The equality is almost everywhere in the row variable because the existing
kernel/operator representation is an a.e. statement on `L2`. -/
theorem asymNormalizedTransferKernelRemainder_row_ground_orthogonal
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (m : ℕ) :
    (fun x : SpatialField Ns =>
      ∫ y, asymNormalizedTransferKernelRemainder
          (Nt := Nt) (Ns := Ns) P a mass ha hmass m x y *
            asymGroundVector Nt Ns P a mass ha hmass y ∂volume) =ᵐ[volume]
      (fun _ : SpatialField Ns => 0) := by
  let Omega := asymGroundVector Nt Ns P a mass ha hmass
  have hzero :
      asymNormalizedTransferRemainderCLM
          (Nt := Nt) (Ns := Ns) P a mass ha hmass m Omega = 0 := by
    rw [asymNormalizedTransferRemainderCLM_apply_eq_pow_centered]
    have hinner : @inner ℝ _ _ Omega Omega = 1 := by
      rw [real_inner_self_eq_norm_sq, asymGroundVector_norm_eq_one]
      norm_num
    rw [hinner]
    simp
  have hrepr := asymNormalizedTransferKernelRemainder_apply
    (Nt := Nt) (Ns := Ns) P a mass ha hmass m Omega
  rw [hzero] at hrepr
  simpa [Omega] using hrepr.symm

/-- Each column of the normalized remainder is orthogonal to the ground vector.

This is the row statement transported through the pointwise symmetry of the
remainder kernel. -/
theorem asymNormalizedTransferKernelRemainder_column_ground_orthogonal
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (m : ℕ) :
    (fun y : SpatialField Ns =>
      ∫ x, asymNormalizedTransferKernelRemainder
          (Nt := Nt) (Ns := Ns) P a mass ha hmass m x y *
            asymGroundVector Nt Ns P a mass ha hmass x ∂volume) =ᵐ[volume]
      (fun _ : SpatialField Ns => 0) := by
  have hrow := asymNormalizedTransferKernelRemainder_row_ground_orthogonal
    (Nt := Nt) (Ns := Ns) P a mass ha hmass m
  filter_upwards [hrow] with y hy
  calc
    (∫ x, asymNormalizedTransferKernelRemainder
        (Nt := Nt) (Ns := Ns) P a mass ha hmass m x y *
          asymGroundVector Nt Ns P a mass ha hmass x ∂volume) =
        ∫ x, asymNormalizedTransferKernelRemainder
          (Nt := Nt) (Ns := Ns) P a mass ha hmass m y x *
            asymGroundVector Nt Ns P a mass ha hmass x ∂volume := by
      apply integral_congr_ae
      exact .of_forall (fun x => by
        rw [asymNormalizedTransferKernelRemainder_symm])
    _ = 0 := hy

end Pphi2
