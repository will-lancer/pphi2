/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Pphi2.AsymTorus.AsymTraceKernelRemainder
import Mathlib.Data.Fin.Rev

/-!
# Symmetry and ground convolution for normalized transfer powers

The generic transfer-system fields give a symmetric one-step kernel and the
integrability needed to fold an open chain.  Reversing the finite interior
coordinates therefore gives symmetry of every iterated kernel.  The
normalized kernel has the same symmetry.  The existing operator/kernel
identity and the normalized ground-vector power identity then give the right
and left ground-convolution formulas.
-/

noncomputable section

open MeasureTheory ReflectionPositivity

namespace ReflectionPositivity.TransferSystem

variable {S : Type*} [MeasurableSpace S]

private noncomputable def finReverseMeasurableEquiv (Ts : TransferSystem S)
    (m : ℕ) : (Fin m → S) ≃ᵐ (Fin m → S) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin m => S)
    (Fin.revPerm : Fin m ≃ Fin m)

private theorem measurePreserving_finReverseMeasurableEquiv
    (Ts : TransferSystem S) (m : ℕ) :
    MeasurePreserving (finReverseMeasurableEquiv Ts m)
      (Measure.pi (fun _ : Fin m => Ts.ν))
      (Measure.pi (fun _ : Fin m => Ts.ν)) := by
  letI := Ts.ν_sigmaFinite
  simpa [finReverseMeasurableEquiv] using
    (measurePreserving_piCongrLeft
      (fun _ : Fin m => Ts.ν) (Fin.revPerm : Fin m ≃ Fin m))

private theorem finReverseMeasurableEquiv_apply
    (Ts : TransferSystem S) (m : ℕ) (q : Fin m → S) :
    finReverseMeasurableEquiv Ts m q = q ∘ Fin.rev := by
  funext i
  simp [finReverseMeasurableEquiv, Function.comp_apply]

private theorem openChainVertices_reverse
    (m : ℕ) (x y : S) (q : Fin m → S) :
    openChainVertices m x y (q ∘ Fin.rev) ∘ Fin.rev =
      openChainVertices m y x q := by
  simp only [openChainVertices, Fin.snoc_comp_rev, Fin.cons_comp_rev]
  simp [Function.comp_def]

private theorem openChainProduct_reverse
    (Ts : TransferSystem S) (m : ℕ) (x y : S) (q : Fin m → S) :
    openChainProduct Ts.k m x y (q ∘ Fin.rev) =
      openChainProduct Ts.k m y x q := by
  let Vxy := openChainVertices m x y (q ∘ Fin.rev)
  let Vyx := openChainVertices m y x q
  have hV : Vxy ∘ Fin.rev = Vyx := by
    simpa [Vxy, Vyx] using openChainVertices_reverse m x y q
  have hleft (i : Fin (m + 1)) :
      Vxy ((Fin.rev i).castSucc) = Vyx i.succ := by
    have h := congrFun hV i.succ
    simpa only [Function.comp_apply, Fin.rev_succ] using h
  have hright (i : Fin (m + 1)) :
      Vxy ((Fin.rev i).succ) = Vyx i.castSucc := by
    have h := congrFun hV i.castSucc
    simpa only [Function.comp_apply, Fin.rev_castSucc] using h
  unfold openChainProduct
  change (∏ i : Fin (m + 1), Ts.k (Vxy i.castSucc) (Vxy i.succ)) =
    ∏ i : Fin (m + 1), Ts.k (Vyx i.castSucc) (Vyx i.succ)
  calc
    (∏ i : Fin (m + 1), Ts.k (Vxy i.castSucc) (Vxy i.succ)) =
        ∏ i : Fin (m + 1),
          Ts.k (Vxy ((Fin.revPerm : Equiv.Perm (Fin (m + 1))) i).castSucc)
            (Vxy ((Fin.revPerm : Equiv.Perm (Fin (m + 1))) i).succ) := by
      symm
      exact Equiv.prod_comp (Fin.revPerm : Equiv.Perm (Fin (m + 1)))
        (fun i : Fin (m + 1) => Ts.k (Vxy i.castSucc) (Vxy i.succ))
    _ = ∏ i : Fin (m + 1), Ts.k (Vyx i.castSucc) (Vyx i.succ) := by
      apply Fintype.prod_congr
      intro i
      simp only [Fin.revPerm_apply]
      calc
        Ts.k (Vxy (Fin.rev i).castSucc) (Vxy (Fin.rev i).succ) =
            Ts.k (Vyx i.succ) (Vyx i.castSucc) := by
              rw [hleft, hright]
        _ = Ts.k (Vyx i.castSucc) (Vyx i.succ) := Ts.k_symm _ _

private theorem openChainDensity_reverse
    (Ts : TransferSystem S) (m : ℕ) (x y : S) (q : Fin m → S) :
    openChainDensity Ts.k m x y (q ∘ Fin.rev) =
      openChainDensity Ts.k m y x q := by
  calc
    openChainDensity Ts.k m x y (q ∘ Fin.rev) =
        openChainProduct Ts.k m x y (q ∘ Fin.rev) :=
      (openChainProduct_eq_density Ts.k m x y (q ∘ Fin.rev)).symm
    _ = openChainProduct Ts.k m y x q :=
      openChainProduct_reverse Ts m x y q
    _ = openChainDensity Ts.k m y x q :=
      openChainProduct_eq_density Ts.k m y x q

/-- Every iterated transfer kernel of a symmetric transfer system is symmetric.

The proof uses only the supplied open-chain integrability through
`openChain_fold`; the reversal map is measure-preserving on the finite product
measure. -/
theorem kPow_symm (Ts : TransferSystem S) (m : ℕ) (x y : S) :
    Ts.kPow m x y = Ts.kPow m y x := by
  let e := finReverseMeasurableEquiv Ts m
  have hmp := measurePreserving_finReverseMeasurableEquiv Ts m
  rw [← Ts.openChain_fold m x y, ← Ts.openChain_fold m y x]
  calc
    (∫ q : Fin m → S, openChainDensity Ts.k m x y q
        ∂Measure.pi (fun _ : Fin m => Ts.ν)) =
        ∫ q : Fin m → S,
          openChainDensity Ts.k m x y (e q)
            ∂Measure.pi (fun _ : Fin m => Ts.ν) := by
      symm
      exact hmp.integral_comp' (fun q => openChainDensity Ts.k m x y q)
    _ = ∫ q : Fin m → S, openChainDensity Ts.k m y x q
          ∂Measure.pi (fun _ : Fin m => Ts.ν) := by
      apply integral_congr_ae
      filter_upwards [] with q
      simpa [e, finReverseMeasurableEquiv_apply] using
        openChainDensity_reverse Ts m x y q

end ReflectionPositivity.TransferSystem

namespace Pphi2

variable {Nt Ns : ℕ} [NeZero Nt] [NeZero Ns]

theorem asymTransferSystem_kPow_symm
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (m : ℕ) (x y : SpatialField Ns) :
    (asymTransferSystem Nt Ns P a mass ha hmass).kPow m x y =
      (asymTransferSystem Nt Ns P a mass ha hmass).kPow m y x := by
  exact ReflectionPositivity.TransferSystem.kPow_symm
    (asymTransferSystem Nt Ns P a mass ha hmass) m x y

theorem asymNormalizedTransferKernelPower_symm
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (m : ℕ) (x y : SpatialField Ns) :
    asymNormalizedTransferKernelPower
        (Nt := Nt) (Ns := Ns) P a mass ha hmass m x y =
      asymNormalizedTransferKernelPower
        (Nt := Nt) (Ns := Ns) P a mass ha hmass m y x := by
  unfold asymNormalizedTransferKernelPower
  rw [asymTransferSystem_kPow_symm]

theorem asymNormalizedTransferKernelPower_right_ground_convolution
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (m : ℕ) :
    (fun x : SpatialField Ns =>
      ∫ y, asymNormalizedTransferKernelPower
          (Nt := Nt) (Ns := Ns) P a mass ha hmass m x y *
            asymGroundVector Nt Ns P a mass ha hmass y ∂volume) =ᵐ[volume]
      (asymGroundVector Nt Ns P a mass ha hmass : SpatialField Ns → ℝ) := by
  have h := asymNormalizedTransferKernelPower_apply
    (Nt := Nt) (Ns := Ns) P a mass ha hmass m
      (asymGroundVector Nt Ns P a mass ha hmass)
  rw [asymTransferNormalized_pow_groundVector] at h
  exact h.symm

theorem asymNormalizedTransferKernelPower_left_ground_convolution
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (m : ℕ) :
    (fun y : SpatialField Ns =>
      ∫ x, asymNormalizedTransferKernelPower
          (Nt := Nt) (Ns := Ns) P a mass ha hmass m x y *
            asymGroundVector Nt Ns P a mass ha hmass x ∂volume) =ᵐ[volume]
      (asymGroundVector Nt Ns P a mass ha hmass : SpatialField Ns → ℝ) := by
  have hright := asymNormalizedTransferKernelPower_right_ground_convolution
    (Nt := Nt) (Ns := Ns) P a mass ha hmass m
  filter_upwards [hright] with y hy
  calc
    (∫ x, asymNormalizedTransferKernelPower
        (Nt := Nt) (Ns := Ns) P a mass ha hmass m x y *
          asymGroundVector Nt Ns P a mass ha hmass x ∂volume) =
        ∫ x, asymNormalizedTransferKernelPower
          (Nt := Nt) (Ns := Ns) P a mass ha hmass m y x *
            asymGroundVector Nt Ns P a mass ha hmass x ∂volume := by
      apply integral_congr_ae
      exact .of_forall (fun x => by
        rw [asymNormalizedTransferKernelPower_symm])
    _ = asymGroundVector Nt Ns P a mass ha hmass y := hy

/-! ## Two-sided remainder factorization -/

/-- Powers of the normalized transfer can be moved across the real inner product.

This is the only operator-theoretic ingredient needed below.  It is proved by
induction from the self-adjointness of the one-step transfer, so it does not
use a spectral-gap or trace hypothesis. -/
private theorem asymTransferNormalized_pow_inner_swap
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (k : ℕ) (u v : L2SpatialField Ns) :
    @inner ℝ _ _
        ((asymTransferNormalized Nt Ns P a mass ha hmass) ^ k u) v =
      @inner ℝ _ _ u
        ((asymTransferNormalized Nt Ns P a mass ha hmass) ^ k v) := by
  have hT : ∀ x y : L2SpatialField Ns,
      @inner ℝ _ _ (asymTransferNormalized Nt Ns P a mass ha hmass x) y =
        @inner ℝ _ _ x (asymTransferNormalized Nt Ns P a mass ha hmass y) := by
    intro x y
    have hsymm :=
      ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
        (asymTransferOperator_isSelfAdjoint
          (Nt := Nt) (Ns := Ns) P a mass ha hmass)
    simp only [asymTransferNormalized, ContinuousLinearMap.smul_apply,
      real_inner_smul_left, real_inner_smul_right]
    congr 1
    exact hsymm x y
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply]
      calc
        @inner ℝ _ _
              (asymTransferNormalized Nt Ns P a mass ha hmass
                ((asymTransferNormalized Nt Ns P a mass ha hmass) ^ k u)) v =
            @inner ℝ _ _
              ((asymTransferNormalized Nt Ns P a mass ha hmass) ^ k u)
              (asymTransferNormalized Nt Ns P a mass ha hmass v) :=
          hT _ _
        _ = @inner ℝ _ _ u
              ((asymTransferNormalized Nt Ns P a mass ha hmass) ^ k
                (asymTransferNormalized Nt Ns P a mass ha hmass v)) :=
          ih _ _
        _ = @inner ℝ _ _ u
              ((asymTransferNormalized Nt Ns P a mass ha hmass) ^ (k + 1) v) := by
          rw [pow_succ, ContinuousLinearMap.mul_apply]

private theorem asymNormalizedTransferRemainderCLM_inner_ground_eq_zero
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (m : ℕ) (f : L2SpatialField Ns) :
    @inner ℝ _ _
        (asymGroundVector Nt Ns P a mass ha hmass)
        (asymNormalizedTransferRemainderCLM
          (Nt := Nt) (Ns := Ns) P a mass ha hmass m f) = 0 := by
  let T := asymTransferNormalized Nt Ns P a mass ha hmass
  let Ω := asymGroundVector Nt Ns P a mass ha hmass
  have hswap := asymTransferNormalized_pow_inner_swap
    (Nt := Nt) (Ns := Ns) P a mass ha hmass (m + 1) Ω f
  have hΩpow : T ^ (m + 1) Ω = Ω := by
    simpa only [T, Ω] using
      asymTransferNormalized_pow_groundVector
        (Nt := Nt) (Ns := Ns) P a mass ha hmass (m + 1)
  have hswap' :
      @inner ℝ _ _ Ω (T ^ (m + 1) f) = @inner ℝ _ _ Ω f := by
    rw [← hswap, hΩpow]
  unfold asymNormalizedTransferRemainderCLM
  rw [ContinuousLinearMap.sub_apply, InnerProductSpace.rankOne_apply]
  rw [show (asymTransferNormalized Nt Ns P a mass ha hmass) ^ (m + 1) = T ^ (m + 1)
      by rfl]
  rw [hswap', inner_smul_right, real_inner_self_eq_norm_sq,
    asymGroundVector_norm_eq_one]
  ring

/-- A remainder with `q` transfer steps on each side factors through the
middle `n` steps:

`R_(2q+n+1) = R_q T^n R_q`.

The `+1` in the subscript records that `R_m` is the ground-removed part of
`T^(m+1)`.  This identity is purely algebraic and is independent of the
finite-periodic trace/IUC estimates. -/
theorem asymNormalizedTransferRemainderCLM_two_sided_factorization
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (q n : ℕ) (f : L2SpatialField Ns) :
    asymNormalizedTransferRemainderCLM
        (Nt := Nt) (Ns := Ns) P a mass ha hmass (2 * q + n + 1) f =
      asymNormalizedTransferRemainderCLM
        (Nt := Nt) (Ns := Ns) P a mass ha hmass q
        (((asymTransferNormalized Nt Ns P a mass ha hmass) ^ n)
          (asymNormalizedTransferRemainderCLM
            (Nt := Nt) (Ns := Ns) P a mass ha hmass q f)) := by
  let T := asymTransferNormalized Nt Ns P a mass ha hmass
  let R := asymNormalizedTransferRemainderCLM
    (Nt := Nt) (Ns := Ns) P a mass ha hmass
  have hleft := asymNormalizedTransferRemainderCLM_add_apply
    (Nt := Nt) (Ns := Ns) P a mass ha hmass q (q + n + 1) f
  have hRperp := asymNormalizedTransferRemainderCLM_inner_ground_eq_zero
    (Nt := Nt) (Ns := Ns) P a mass ha hmass q f
  have hmiddle_perp :
      @inner ℝ _ _ (asymGroundVector Nt Ns P a mass ha hmass)
        (T ^ n (R q f)) = 0 := by
    have hswap := asymTransferNormalized_pow_inner_swap
      (Nt := Nt) (Ns := Ns) P a mass ha hmass n
      (asymGroundVector Nt Ns P a mass ha hmass) (R q f)
    have hΩpow : T ^ n (asymGroundVector Nt Ns P a mass ha hmass) =
        asymGroundVector Nt Ns P a mass ha hmass := by
      simpa only [T] using
        asymTransferNormalized_pow_groundVector
          (Nt := Nt) (Ns := Ns) P a mass ha hmass n
    rw [← hswap, hΩpow, hRperp]
  have hright :
      R q (T ^ n (R q f)) = T ^ (q + 1) (T ^ n (R q f)) := by
    rw [asymNormalizedTransferRemainderCLM_apply_eq_pow_centered]
    rw [hmiddle_perp]
    simp
  calc
    R (2 * q + n + 1) f = T ^ (q + n + 1) (R q f) := by
      rw [show 2 * q + n + 1 = q + (q + n + 1) by omega]
      simpa only [R, T] using hleft
    _ = T ^ (q + 1) (T ^ n (R q f)) := by
      rw [show q + n + 1 = (q + 1) + n by omega]
      rw [pow_add, ContinuousLinearMap.mul_apply]
    _ = R q (T ^ n (R q f)) := hright.symm

end Pphi2
