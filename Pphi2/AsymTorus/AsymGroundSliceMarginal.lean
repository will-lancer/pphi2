/-!
# Ground one-slice marginal

The normalized ground-state measure on one spatial slice is the measure with
density `Omega ^ 2` against the transfer reference measure.  This file records
the corresponding second-moment identity for `groundSliceVariance` and gives
the existing B5b bound in that measure language.

The measure here is the infinite-time ground-state marginal.  At finite
periodic temporal size the one-slice marginal is instead governed by the
normalized diagonal of the finite transfer power.  Identifying that marginal
with the measure below, or proving its convergence to it, requires a separate
finite-periodic diagonal/trace estimate.  No lattice-family uniformity is
asserted here.
-/

import Pphi2.AsymTorus.AsymB5bSingleSlice

noncomputable section

open MeasureTheory GaussianField ReflectionPositivity
open scoped BigOperators

namespace Pphi2

variable {Nt Ns : ℕ} [NeZero Nt] [NeZero Ns]

local notation "ν" => (volume : Measure (SpatialField Ns))

/-- The normalized one-slice ground-state measure. -/
noncomputable def asymGroundSliceMeasure
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    Measure (SpatialField Ns) :=
  groundMeasure ν (asymGroundStateRep (Nt := Nt) (Ns := Ns) P a mass ha hmass)

/-- The ground-state one-slice measure is a probability measure. -/
noncomputable instance asymGroundSliceMeasure_isProbabilityMeasure
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    IsProbabilityMeasure (asymGroundSliceMeasure (Nt := Nt) (Ns := Ns)
      P a mass ha hmass) := by
  simpa [asymGroundSliceMeasure] using
    asymGroundStateRep_isProbabilityMeasure
      (Nt := Nt) (Ns := Ns) P a mass ha hmass

/-- The density formula for measurable one-slice events. -/
theorem asymGroundSliceMeasure_apply
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    {s : Set (SpatialField Ns)} (hs : MeasurableSet s) :
    asymGroundSliceMeasure (Nt := Nt) (Ns := Ns) P a mass ha hmass s =
      ∫⁻ ψ in s, ENNReal.ofReal
        ((asymGroundStateRep (Nt := Nt) (Ns := Ns) P a mass ha hmass ψ) ^ 2) ∂ν := by
  exact groundMeasure_apply ν
    (asymGroundStateRep (Nt := Nt) (Ns := Ns) P a mass ha hmass) hs

/-- `groundSliceVariance` is the uncentered second moment under the ground
one-slice marginal. -/
theorem groundSliceVariance_eq_asymGroundSliceMeasure_secondMoment
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (g : SpatialField Ns) :
    groundSliceVariance (Nt := Nt) (Ns := Ns) P a mass ha hmass g =
      ∫ ψ, (asymSliceObsLinear g ψ) ^ 2 ∂
        (asymGroundSliceMeasure (Nt := Nt) (Ns := Ns) P a mass ha hmass) := by
  unfold groundSliceVariance asymGroundSliceMeasure
  rw [integral_sq_groundMeasure_eq ν
    (asymGroundStateRep (Nt := Nt) (Ns := Ns) P a mass ha hmass)
    (asymGroundStateRep_measurable (Nt := Nt) (Ns := Ns) P a mass ha hmass)
    (asymSliceObsLinear g)]
  refine integral_congr_ae ?_
  filter_upwards [asymGroundVector_coeFn_eq_groundStateRep
    (Nt := Nt) (Ns := Ns) P a mass ha hmass] with ψ hψ
  rw [hψ]
  ring

/-- The pointwise B5b estimate in ground-measure second-moment form. -/
theorem groundSliceSecondMoment_le_freeCovariance_with_constant
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (Ls : ℝ) (hLs : 0 < Ls) (a : ℝ) (ha : 0 < a)
    (hscale : (Ns : ℝ) * a = Ls) (t : ZMod Nt) (g : SpatialField Ns) :
    (∫ ψ, (asymSliceObsLinear g ψ) ^ 2 ∂
      (asymGroundSliceMeasure (Nt := Nt) (Ns := Ns) P a mass ha hmass)) ≤
      groundVarianceFreeCovarianceConstant P mass hmass Ls hLs *
        freeSingleSliceCovariance (Nt := Nt) (Ns := Ns)
          a mass ha hmass t g := by
  rw [← groundSliceVariance_eq_asymGroundSliceMeasure_secondMoment
    (Nt := Nt) (Ns := Ns) P a mass ha hmass g]
  exact groundVariance_le_freeCovariance_with_constant
    (Nt := Nt) (Ns := Ns) P mass hmass Ls hLs a ha hscale t g

/-- The existing B5b existential estimate, expressed as a ground one-slice
second-moment estimate. -/
theorem groundSliceSecondMoment_le_freeCovariance
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (Ls : ℝ) (hLs : 0 < Ls) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (ha : 0 < a),
        (Ns : ℝ) * a = Ls →
        ∀ (t : ZMod Nt) (g : SpatialField Ns),
          (∫ ψ, (asymSliceObsLinear g ψ) ^ 2 ∂
            (asymGroundSliceMeasure (Nt := Nt) (Ns := Ns)
              P a mass ha hmass)) ≤
            C * freeSingleSliceCovariance (Nt := Nt) (Ns := Ns)
              a mass ha hmass t g := by
  rcases groundVariance_le_freeCovariance P mass hmass Ls hLs with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro Nt Ns _ _ a ha hscale t g
  rw [← groundSliceVariance_eq_asymGroundSliceMeasure_secondMoment
    (Nt := Nt) (Ns := Ns) P a mass ha hmass g]
  exact hbound Nt Ns a ha hscale t g

end Pphi2
