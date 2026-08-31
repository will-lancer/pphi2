/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.AsymTorus.AsymTraceSplit
import Pphi2.AsymTorus.AsymSliceFamilySusceptibility

/-!
# Concrete asymmetric trace-slice bridge

This module instantiates the generic finite-periodic trace split for the
asymmetric pphi2 transfer system and exposes the exact hypothesis consumed by
the slice-family shell. The trace-ratio equality and the two integrability
conditions remain explicit inputs; this file only transports them through the
path dictionary and identifies the concrete transfer operator.
-/

noncomputable section

open MeasureTheory GaussianField ReflectionPositivity
open scoped BigOperators ENNReal

namespace Pphi2

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

variable {Nt Ns : ℕ} [NeZero Nt] [NeZero Ns]

/-- Instantiate the generic trace-split transport at two truncated asymmetric
slice observables. The `hTraceSplit` input is the concrete trace-ratio theorem
that supplies the finite-periodic remainder; `hAB` and `hSlice` are the exact
Fubini hypotheses required by the path dictionary. -/
theorem interacting_truncSlice_cross_moment_eq_normalizedTransfer_pow_add_remainder_of_traceSplit
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hnorm : ∀ v : L2SpatialField Ns,
      ⟪asymGroundVector Nt Ns P a mass ha hmass, v⟫ = 0 →
        ‖asymTransferNormalized Nt Ns P a mass ha hmass v‖ ≤ γ * ‖v‖)
    (g g' : SpatialField Ns) {K : ℝ} (hK : 0 < K) (t t' : ZMod Nt)
    (R : ℝ)
    (hd0 : 0 < (t' - t).val) (hdlt : (t' - t).val < Nt)
    (hTraceSplit :
      traceRatioTwoPoint
          (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass)
          (asymSliceObsTruncContract (Ns := Ns) g hK)
          (asymSliceObsTruncContract (Ns := Ns) g' hK) Nt (t' - t).val =
        ⟪asymGroundVector Nt Ns P a mass ha hmass,
          (asymSliceObsTruncContract (Ns := Ns) g hK).M
            (((asymTransferNormalized Nt Ns P a mass ha hmass) ^ (t' - t).val)
              ((asymSliceObsTruncContract (Ns := Ns) g' hK).M
                (asymGroundVector Nt Ns P a mass ha hmass)))⟫ + R)
    (hAB : Integrable
      (twoPointSplitDensity
        (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).k
        ((t' - t).val - 1) (Nt - (t' - t).val - 1)
        (asymSliceObsTruncContract (Ns := Ns) g hK).A
        (asymSliceObsTruncContract (Ns := Ns) g' hK).A)
      ((asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).ν.prod
        ((asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).ν.prod
          ((Measure.pi (fun _ : Fin ((t' - t).val - 1) =>
              (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).ν)).prod
            (Measure.pi (fun _ : Fin (Nt - (t' - t).val - 1) =>
              (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).ν)))))
    (hSlice : ∀ x : SpatialField Ns, Integrable
      (fun p : SpatialField Ns ×
          ((Fin ((t' - t).val - 1) → SpatialField Ns) ×
            (Fin (Nt - (t' - t).val - 1) → SpatialField Ns)) =>
        twoPointSplitDensity
          (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).k
          ((t' - t).val - 1) (Nt - (t' - t).val - 1)
          (asymSliceObsTruncContract (Ns := Ns) g hK).A
          (asymSliceObsTruncContract (Ns := Ns) g' hK).A (x, p))
      ((asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).ν.prod
        ((Measure.pi (fun _ : Fin ((t' - t).val - 1) =>
            (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).ν)).prod
          (Measure.pi (fun _ : Fin (Nt - (t' - t).val - 1) =>
            (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).ν))))) :
    ∫ ω, asymSliceObsTrunc g K
            (asymSliceEquiv Nt Ns (evalMapAsym Nt Ns ω) t) *
          asymSliceObsTrunc g' K
            (asymSliceEquiv Nt Ns (evalMapAsym Nt Ns ω) t')
        ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) =
      ⟪asymGroundVector Nt Ns P a mass ha hmass,
        (asymSliceObsTruncContract (Ns := Ns) g hK).M
          (((asymTransferNormalized Nt Ns P a mass ha hmass) ^ (t' - t).val)
            ((asymSliceObsTruncContract (Ns := Ns) g' hK).M
              (asymGroundVector Nt Ns P a mass ha hmass)))⟫ + R := by
  have hTraceSplit' :
      traceRatioTwoPoint
          (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass)
          (asymSliceObsTruncContract (Ns := Ns) g hK)
          (asymSliceObsTruncContract (Ns := Ns) g' hK) Nt (t' - t).val =
        @inner ℝ _ _
          (asymGappedTransfer Nt Ns P a mass ha hmass γ hγ0 hγ1 hnorm).vacuum
          ((asymSliceObsTruncContract (Ns := Ns) g hK).M
            (((asymGappedTransfer Nt Ns P a mass ha hmass γ hγ0 hγ1 hnorm).T ^
                (t' - t).val)
              ((asymSliceObsTruncContract (Ns := Ns) g' hK).M
                (asymGappedTransfer Nt Ns P a mass ha hmass γ hγ0 hγ1 hnorm).vacuum))) + R := by
    simpa only [asymGappedTransfer] using hTraceSplit
  have hPath := pathTwoPoint_eq_groundTransfer_add_remainder
    (Ts := asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass)
    (A := asymSliceObsTruncContract (Ns := Ns) g hK)
    (B := asymSliceObsTruncContract (Ns := Ns) g' hK)
    (G := asymGappedTransfer Nt Ns P a mass ha hmass γ hγ0 hγ1 hnorm)
    (Nt := Nt) (d := t' - t) hd0 hdlt R hTraceSplit' hAB hSlice
  have hPeriodicGroundSplit :
      pathTwoPoint
          (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass)
          (asymSliceObsTruncContract (Ns := Ns) g hK)
          (asymSliceObsTruncContract (Ns := Ns) g' hK) Nt (t' - t) =
        ⟪asymGroundVector Nt Ns P a mass ha hmass,
          (asymSliceObsTruncContract (Ns := Ns) g hK).M
            (((asymTransferNormalized Nt Ns P a mass ha hmass) ^ (t' - t).val)
              ((asymSliceObsTruncContract (Ns := Ns) g' hK).M
                (asymGroundVector Nt Ns P a mass ha hmass)))⟫ + R := by
    simpa only [asymGappedTransfer] using hPath
  exact interacting_truncSlice_cross_moment_eq_normalizedTransfer_pow_add_remainder
    (Nt := Nt) (Ns := Ns) P a mass ha hmass g g' hK t t' R hPeriodicGroundSplit

end Pphi2

end
