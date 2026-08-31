/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Pphi2.ClusterExpansion.ContinuousConfig

/-!
# Finite-dimensional Gaussian bases for continuous spins

The measure is the centered multivariate Gaussian with the selected covariance,
transported from Euclidean space to the raw product type `Site → ℝ`.
-/

open MeasureTheory NormedSpace ProbabilityTheory WithLp

namespace Pphi2.ClusterExpansion

variable {Site : Type*} [Fintype Site] [DecidableEq Site]

/-- The centered Gaussian probability measure on real site configurations. -/
noncomputable def finiteGaussianMeasure (C : Matrix Site Site ℝ) :
    Measure (ContinuousConfig Site) :=
  (multivariateGaussian 0 C).map
    (MeasurableEquiv.toLp 2 (Site → ℝ)).symm

/-- The transport map realizes the raw configuration measure. -/
theorem measurePreserving_ofLp_finiteGaussianMeasure
    (C : Matrix Site Site ℝ) :
    MeasurePreserving ofLp
      (multivariateGaussian 0 C) (finiteGaussianMeasure C) where
  measurable := by fun_prop
  map_eq := rfl

noncomputable instance finiteGaussianMeasure_isGaussian
    (C : Matrix Site Site ℝ) :
    IsGaussian (finiteGaussianMeasure C) := by
  rw [finiteGaussianMeasure,
    show ⇑(MeasurableEquiv.toLp 2 (Site → ℝ)).symm =
      ⇑(EuclideanSpace.equiv Site ℝ) from rfl]
  infer_instance

noncomputable instance finiteGaussianMeasure_isProbability
    (C : Matrix Site Site ℝ) :
    IsProbabilityMeasure (finiteGaussianMeasure C) := by
  infer_instance

/-- Covariance transport from raw configurations to Euclidean space. -/
theorem covariance_finiteGaussianMeasure
    (C : Matrix Site Site ℝ) (i j : Site) :
    cov[fun φ : ContinuousConfig Site => φ i,
      fun φ : ContinuousConfig Site => φ j; finiteGaussianMeasure C] =
    cov[fun x => (ofLp x) i, fun x => (ofLp x) j;
      multivariateGaussian 0 C] := by
  rw [finiteGaussianMeasure, covariance_map_equiv]
  rfl

/-- A positive-semidefinite covariance matrix is the covariance of the
corresponding finite Gaussian configuration measure. -/
theorem covariance_eval_finiteGaussianMeasure
    (C : Matrix Site Site ℝ) (hC : C.PosSemidef) (i j : Site) :
    cov[fun φ : ContinuousConfig Site => φ i,
      fun φ : ContinuousConfig Site => φ j; finiteGaussianMeasure C] =
      C i j := by
  rw [covariance_finiteGaussianMeasure,
    covariance_eval_multivariateGaussian hC]

/-- Proof-carrying finite Gaussian data for later interpolation. -/
structure FiniteGaussianData (Site : Type*) [Fintype Site]
    [DecidableEq Site] where
  covariance : Matrix Site Site ℝ
  covariance_posSemidef : covariance.PosSemidef

namespace FiniteGaussianData

/-- The probability measure selected by proof-carrying Gaussian data. -/
noncomputable def measure (G : FiniteGaussianData Site) :
    Measure (ContinuousConfig Site) :=
  finiteGaussianMeasure G.covariance

noncomputable instance measure_isProbability (G : FiniteGaussianData Site) :
    IsProbabilityMeasure G.measure := by
  unfold measure
  infer_instance

theorem covariance_eval (G : FiniteGaussianData Site) (i j : Site) :
    cov[fun φ : ContinuousConfig Site => φ i,
      fun φ : ContinuousConfig Site => φ j; G.measure] =
      G.covariance i j :=
  covariance_eval_finiteGaussianMeasure
    G.covariance G.covariance_posSemidef i j

end FiniteGaussianData

end Pphi2.ClusterExpansion
