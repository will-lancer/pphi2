/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.AsymTorus.AsymTraceBridge
import ReflectionPositivity.GroundBridge

/-!
# Signed finite-periodic trace residual

This file separates a normalized finite-periodic trace ratio into its ground
transfer matrix element and a signed residual. The path-integral dictionary is
applied only at a nonzero separation represented strictly below the period.
-/

noncomputable section

open MeasureTheory ReflectionPositivity

namespace Pphi2

variable {S : Type*} [MeasurableSpace S]

/-- Signed difference between the periodic trace ratio and the ground transfer
matrix element at the same separation. -/
noncomputable def finitePeriodicTraceResidual
    (Ts : TransferSystem S)
    (A B : MultiplicationCLMContract Ts.ν)
    (G : GappedTransfer (Lp ℝ 2 Ts.ν))
    (Nt : ℕ) [NeZero Nt] (d : ZMod Nt) : ℝ :=
  traceRatioTwoPoint Ts A B Nt d.val -
    @inner ℝ _ _ G.vacuum
      (A.M ((G.T ^ d.val) (B.M G.vacuum)))

/-- Algebraic decomposition of the trace ratio into its ground contribution
and signed residual. -/
theorem traceRatioTwoPoint_eq_groundTransfer_add_residual
    (Ts : TransferSystem S)
    (A B : MultiplicationCLMContract Ts.ν)
    (G : GappedTransfer (Lp ℝ 2 Ts.ν))
    (Nt : ℕ) [NeZero Nt] (d : ZMod Nt) :
    traceRatioTwoPoint Ts A B Nt d.val =
      @inner ℝ _ _ G.vacuum
        (A.M ((G.T ^ d.val) (B.M G.vacuum))) +
        finitePeriodicTraceResidual Ts A B G Nt d := by
  unfold finitePeriodicTraceResidual
  ring

/-- Transport the signed trace split through the periodic path dictionary. -/
theorem pathTwoPoint_eq_groundTransfer_add_residual
    (Ts : TransferSystem S)
    (A B : MultiplicationCLMContract Ts.ν)
    (G : GappedTransfer (Lp ℝ 2 Ts.ν))
    (Nt : ℕ) [NeZero Nt] (d : ZMod Nt)
    (hd0 : 0 < d.val) (hdlt : d.val < Nt)
    (hAB : Integrable
      (twoPointSplitDensity Ts.k (d.val - 1) (Nt - d.val - 1) A.A B.A)
      (Ts.ν.prod (Ts.ν.prod
        ((Measure.pi (fun _ : Fin (d.val - 1) => Ts.ν)).prod
          (Measure.pi (fun _ : Fin (Nt - d.val - 1) => Ts.ν))))))
    (hSlice : ∀ x : S, Integrable
      (fun p : S × ((Fin (d.val - 1) → S) × (Fin (Nt - d.val - 1) → S)) =>
        twoPointSplitDensity Ts.k (d.val - 1) (Nt - d.val - 1)
          A.A B.A (x, p))
      (Ts.ν.prod ((Measure.pi (fun _ : Fin (d.val - 1) => Ts.ν)).prod
        (Measure.pi (fun _ : Fin (Nt - d.val - 1) => Ts.ν))))) :
    pathTwoPoint Ts A B Nt d =
      @inner ℝ _ _ G.vacuum
        (A.M ((G.T ^ d.val) (B.M G.vacuum))) +
        finitePeriodicTraceResidual Ts A B G Nt d := by
  calc
    pathTwoPoint Ts A B Nt d =
        traceRatioTwoPoint Ts A B Nt d.val :=
      pathTwoPoint_eq_traceRatio_val Ts A B Nt d hd0 hdlt hAB hSlice
    _ = @inner ℝ _ _ G.vacuum
          (A.M ((G.T ^ d.val) (B.M G.vacuum))) +
          finitePeriodicTraceResidual Ts A B G Nt d :=
      traceRatioTwoPoint_eq_groundTransfer_add_residual Ts A B G Nt d

/-- Transport an externally supplied trace remainder through the periodic path
dictionary. This keeps the analytic residual estimate separate from the
algebraic split. -/
theorem pathTwoPoint_eq_groundTransfer_add_remainder
    (Ts : TransferSystem S)
    (A B : MultiplicationCLMContract Ts.ν)
    (G : GappedTransfer (Lp ℝ 2 Ts.ν))
    (Nt : ℕ) [NeZero Nt] (d : ZMod Nt)
    (hd0 : 0 < d.val) (hdlt : d.val < Nt)
    (R : ℝ)
    (hTraceSplit :
      traceRatioTwoPoint Ts A B Nt d.val =
        @inner ℝ _ _ G.vacuum
          (A.M ((G.T ^ d.val) (B.M G.vacuum))) + R)
    (hAB : Integrable
      (twoPointSplitDensity Ts.k (d.val - 1) (Nt - d.val - 1) A.A B.A)
      (Ts.ν.prod (Ts.ν.prod
        ((Measure.pi (fun _ : Fin (d.val - 1) => Ts.ν)).prod
          (Measure.pi (fun _ : Fin (Nt - d.val - 1) => Ts.ν))))))
    (hSlice : ∀ x : S, Integrable
      (fun p : S × ((Fin (d.val - 1) → S) × (Fin (Nt - d.val - 1) → S)) =>
        twoPointSplitDensity Ts.k (d.val - 1) (Nt - d.val - 1)
          A.A B.A (x, p))
      (Ts.ν.prod ((Measure.pi (fun _ : Fin (d.val - 1) => Ts.ν)).prod
        (Measure.pi (fun _ : Fin (Nt - d.val - 1) => Ts.ν))))) :
    pathTwoPoint Ts A B Nt d =
      @inner ℝ _ _ G.vacuum
        (A.M ((G.T ^ d.val) (B.M G.vacuum))) + R := by
  calc
    pathTwoPoint Ts A B Nt d =
        traceRatioTwoPoint Ts A B Nt d.val :=
      pathTwoPoint_eq_traceRatio_val Ts A B Nt d hd0 hdlt hAB hSlice
    _ = @inner ℝ _ _ G.vacuum
          (A.M ((G.T ^ d.val) (B.M G.vacuum))) + R :=
      hTraceSplit

end Pphi2

end
