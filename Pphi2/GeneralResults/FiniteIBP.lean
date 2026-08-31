/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/

import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Finite-dimensional score identities

This file packages the whole-space Haar integration-by-parts theorem for a
smooth density of the form `exp (-S)`. The integrability hypotheses carry the
boundary-at-infinity condition, so the wrapper does not impose compact support.
-/

noncomputable section

open MeasureTheory

namespace Pphi2

/-! ## A score identity for a supplied exponential-density derivative -/

/--
Integration by parts against the density `exp (-S)`, with the pointwise
directional derivative of that density supplied by `hchain`.

The identity is stated on a finite-dimensional real normed space with an
arbitrary additive Haar measure.  The three integrability hypotheses are the
exact hypotheses needed by Mathlib's whole-space integration-by-parts theorem.
In particular, no compact-support assumption is introduced.
-/
theorem integral_fderiv_mul_exp_neg_eq_integral_mul_fderiv_exp_neg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure E} [μ.IsAddHaarMeasure]
    (H S : E → ℝ) (v : E)
    (hHrho : Integrable
      (fun x => fderiv ℝ H x v * Real.exp (-S x)) μ)
    (hHrhod : Integrable
      (fun x => H x * fderiv ℝ (fun y => Real.exp (-S y)) x v) μ)
    (hHrho' : Integrable
      (fun x => H x * Real.exp (-S x)) μ)
    (hH : ∀ x ∈ tsupport (fun y => Real.exp (-S y)),
      DifferentiableAt ℝ H x)
    (hrho : ∀ x ∈ tsupport H,
      DifferentiableAt ℝ (fun y => Real.exp (-S y)) x)
    (hchain : ∀ x,
      fderiv ℝ (fun y => Real.exp (-S y)) x v =
        -(fderiv ℝ S x v) * Real.exp (-S x)) :
    ∫ x, fderiv ℝ H x v * Real.exp (-S x) ∂μ =
      ∫ x, H x * fderiv ℝ S x v * Real.exp (-S x) ∂μ := by
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := μ) (f := H)
    (g := fun x => Real.exp (-S x)) (v := v)
    hHrho hHrhod hHrho' hH hrho
  have hrewrite :
      (fun x => H x * fderiv ℝ (fun y => Real.exp (-S y)) x v) =
        (fun x => -(H x * (fderiv ℝ S x v * Real.exp (-S x)))) := by
    funext x
    rw [hchain]
    ring
  calc
    ∫ x, fderiv ℝ H x v * Real.exp (-S x) ∂μ =
        -(∫ x, H x * fderiv ℝ (fun y => Real.exp (-S y)) x v ∂μ) := by
      linarith
    _ = -(∫ x, -(H x * (fderiv ℝ S x v * Real.exp (-S x))) ∂μ) := by
      rw [hrewrite]
    _ = ∫ x, H x * fderiv ℝ S x v * Real.exp (-S x) ∂μ := by
      rw [integral_neg, neg_neg]
      congr 1
      funext x
      ring

end Pphi2
