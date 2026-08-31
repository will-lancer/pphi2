/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Finite source-tilt score identity

This file turns the coordinate derivative calculus into the finite-dimensional
whole-space integration-by-parts identity.  The analytic boundary condition is
kept explicit in the three integrability hypotheses inherited from
`Pphi2.GeneralResults.FiniteIBP`.  The finite-coordinate differentiability
needed to identify the displayed density with its directional score is proved
here from the scalar Wick derivative and continuous-linear-map calculus.
-/

import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Pphi2.AsymTorus.AsymTiltedIBP
import Pphi2.GeneralResults.FiniteIBP

noncomputable section

open GaussianField MeasureTheory
open scoped BigOperators

namespace Pphi2

/-! ## Frechet derivatives of the finite tilt -/

/--
The finite Gaussian/Wick/source exponent is differentiable at every
coordinate field.  All coordinate dependence is through finite sums,
continuous linear maps, scalar products, powers, and the scalar Wick
polynomials.  The latter are differentiable by the already proved
`wickPolynomial_hasDerivAt` theorem.
-/
theorem asymGaussianSourceTiltExponent_differentiableAt
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass κ : ℝ)
    (g φ : AsymLatticeField Nt Ns) :
    DifferentiableAt ℝ
      (asymGaussianSourceTiltExponent Nt Ns P a mass κ g) φ := by
  let Q : AsymLatticeField Nt Ns →L[ℝ] AsymLatticeField Nt Ns :=
    massOperatorAsym Nt Ns a mass
  have hcoord : ∀ x : AsymLatticeSites Nt Ns,
      DifferentiableAt ℝ (fun ψ : AsymLatticeField Nt Ns => ψ x) φ := by
    intro x
    change DifferentiableAt ℝ
      (ContinuousLinearMap.proj (R := ℝ) x :
        AsymLatticeField Nt Ns →L[ℝ] ℝ) φ
    exact (ContinuousLinearMap.proj (R := ℝ) x :
      AsymLatticeField Nt Ns →L[ℝ] ℝ).differentiableAt
  have hQcoord : ∀ x : AsymLatticeSites Nt Ns,
      DifferentiableAt ℝ (fun ψ : AsymLatticeField Nt Ns => (Q ψ) x) φ := by
    intro x
    change DifferentiableAt ℝ
      ((ContinuousLinearMap.proj (R := ℝ) x :
        AsymLatticeField Nt Ns →L[ℝ] ℝ).comp Q) φ
    exact ((ContinuousLinearMap.proj (R := ℝ) x :
      AsymLatticeField Nt Ns →L[ℝ] ℝ).comp Q).differentiableAt
  have hquad_sum : DifferentiableAt ℝ
      (fun ψ : AsymLatticeField Nt Ns =>
        ∑ x : AsymLatticeSites Nt Ns, ψ x * (Q ψ) x) φ := by
    apply DifferentiableAt.fun_sum
    intro x hx
    exact (hcoord x).mul (hQcoord x)
  have hquad : DifferentiableAt ℝ
      (asymQuadraticForm Nt Ns a mass) φ := by
    simpa [asymQuadraticForm, Q] using hquad_sum
  have hwick_term : ∀ x : AsymLatticeSites Nt Ns,
      DifferentiableAt ℝ
        (fun ψ : AsymLatticeField Nt Ns =>
          wickPolynomial P (wickConstantAsym Nt Ns a mass) (ψ x)) φ := by
    intro x
    have hpoly : DifferentiableAt ℝ
        (wickPolynomial P (wickConstantAsym Nt Ns a mass)) (φ x) :=
      (wickPolynomial_hasDerivAt P
        (wickConstantAsym Nt Ns a mass) (φ x)).differentiableAt
    simpa only [Function.comp_apply] using
      hpoly.comp φ (hcoord x)
  have hwick_sum : DifferentiableAt ℝ
      (fun ψ : AsymLatticeField Nt Ns =>
        ∑ x : AsymLatticeSites Nt Ns,
          wickPolynomial P (wickConstantAsym Nt Ns a mass) (ψ x)) φ := by
    apply DifferentiableAt.fun_sum
    intro x hx
    exact hwick_term x
  have hwick : DifferentiableAt ℝ
      (asymCoordinateWickAction Nt Ns P a mass) φ := by
    simpa [asymCoordinateWickAction] using
      hwick_sum.const_mul (a ^ 2)
  have hsource_term : ∀ x : AsymLatticeSites Nt Ns,
      DifferentiableAt ℝ
        (fun ψ : AsymLatticeField Nt Ns => g x * ψ x) φ := by
    intro x
    exact (hcoord x).const_mul (g x)
  have hsource_pair : DifferentiableAt ℝ
      (asymCoordinateSourcePairing Nt Ns g) φ := by
    have hsum := DifferentiableAt.fun_sum (u := (Finset.univ :
      Finset (AsymLatticeSites Nt Ns))) (fun x hx => hsource_term x)
    simpa [asymCoordinateSourcePairing] using hsum
  have hsource : DifferentiableAt ℝ
      (asymCoordinateSourceExponent Nt Ns P κ g) φ := by
    have hpow := hsource_pair.pow P.n
    have hscaled := hpow.const_mul κ
    have hdiv : DifferentiableAt ℝ
        (fun ψ : AsymLatticeField Nt Ns =>
          κ * (asymCoordinateSourcePairing Nt Ns g ψ) ^ P.n / (P.n : ℝ)) φ :=
      by
        simpa only [div_eq_mul_inv] using
          hscaled.mul_const ((P.n : ℝ)⁻¹)
    simpa [asymCoordinateSourceExponent] using hdiv
  have hfull := (hquad.const_mul (-(a ^ 2 / 2 : ℝ))).sub hwick
  have hfull := hfull.add hsource
  unfold asymGaussianSourceTiltExponent
  simpa using hfull

/--
The Frechet derivative of the full Gaussian/Wick/source exponent is the
directional score from `AsymTiltedIBP`.

Pointwise differentiability is discharged by
`asymGaussianSourceTiltExponent_differentiableAt`.
-/
theorem asymGaussianSourceTiltExponent_fderiv_fieldShift
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass κ : ℝ)
    (g φ v : AsymLatticeField Nt Ns) :
    fderiv ℝ (asymGaussianSourceTiltExponent Nt Ns P a mass κ g) φ v =
      asymGaussianSourceTiltScore Nt Ns P a mass κ g φ v := by
  have hline : HasDerivAt (fun s : ℝ => φ + s • v) v 0 := by
    simpa only [zero_add, one_smul] using
      (hasDerivAt_const (0 : ℝ) φ).add
        ((hasDerivAt_id (0 : ℝ)).smul_const v)
  have hExpDiff := asymGaussianSourceTiltExponent_differentiableAt
    Nt Ns P a mass κ g φ
  have hcomp := hExpDiff.hasFDerivAt.comp_hasDerivAt_of_eq
    0 hline (by simp)
  have hcomp' : HasDerivAt
      (fun s : ℝ =>
        asymGaussianSourceTiltExponent Nt Ns P a mass κ g (φ + s • v))
      (fderiv ℝ (asymGaussianSourceTiltExponent Nt Ns P a mass κ g) φ v) 0 := by
    simpa only [Function.comp_apply] using hcomp
  have hpath := asymGaussianSourceTiltExponent_hasDerivAt_fieldShift
    Nt Ns P a mass κ g φ v 0
  simpa using hcomp'.unique hpath

/--
The Frechet derivative of the complete finite tilt density is density times
the score.  This is the density chain rule used by the whole-space IBP
wrapper below.
-/
theorem asymGaussianSourceTiltDensity_fderiv_fieldShift
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass κ : ℝ)
    (g φ v : AsymLatticeField Nt Ns) :
    fderiv ℝ (asymGaussianSourceTiltDensity Nt Ns P a mass κ g) φ v =
      asymGaussianSourceTiltDensity Nt Ns P a mass κ g φ *
        asymGaussianSourceTiltScore Nt Ns P a mass κ g φ v := by
  have hExpDiff := asymGaussianSourceTiltExponent_differentiableAt
    Nt Ns P a mass κ g φ
  have hscore := asymGaussianSourceTiltExponent_fderiv_fieldShift
    Nt Ns P a mass κ g φ v
  change (fderiv ℝ
      (fun y => Real.exp
        (asymGaussianSourceTiltExponent Nt Ns P a mass κ g y)) φ) v = _
  rw [fderiv_exp hExpDiff]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hscore]
  simp only [asymGaussianSourceTiltDensity]

/-! ## Whole-space coordinate score identity -/

/--
Finite-dimensional score identity for the unnormalized coordinate source
density.  Multiplying both sides by a finite partition normalizer preserves
the identity.

The measure is Haar volume in coordinate space.  The three integrability
hypotheses are exactly the boundary-at-infinity conditions required by the
generic whole-space integration-by-parts theorem.  The proved exponent
differentiability supplies the density derivative through the two chain-rule
lemmas above.  The conclusion has the usual sign for a density `exp
(exponent)`.
-/
theorem asymGaussianSourceTilt_score_integral_identity
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass κ : ℝ)
    (g v : AsymLatticeField Nt Ns)
    (H : AsymLatticeField Nt Ns → ℝ)
    (hHrho : Integrable
      (fun φ => fderiv ℝ H φ v *
        asymGaussianSourceTiltDensity Nt Ns P a mass κ g φ)
      (volume : Measure (AsymLatticeField Nt Ns)))
    (hHrhod : Integrable
      (fun φ => H φ *
        fderiv ℝ (fun y => asymGaussianSourceTiltDensity
          Nt Ns P a mass κ g y) φ v)
      (volume : Measure (AsymLatticeField Nt Ns)))
    (hHrho' : Integrable
      (fun φ => H φ * asymGaussianSourceTiltDensity Nt Ns P a mass κ g φ)
      (volume : Measure (AsymLatticeField Nt Ns)))
    (hH : ∀ φ ∈ tsupport
      (fun y => asymGaussianSourceTiltDensity Nt Ns P a mass κ g y),
      DifferentiableAt ℝ H φ) :
    ∫ φ : AsymLatticeField Nt Ns,
        fderiv ℝ H φ v * asymGaussianSourceTiltDensity Nt Ns P a mass κ g φ
      ∂(volume : Measure (AsymLatticeField Nt Ns)) =
      -∫ φ : AsymLatticeField Nt Ns,
        H φ * asymGaussianSourceTiltScore Nt Ns P a mass κ g φ v *
          asymGaussianSourceTiltDensity Nt Ns P a mass κ g φ
      ∂(volume : Measure (AsymLatticeField Nt Ns)) := by
  let E : AsymLatticeField Nt Ns → ℝ :=
    asymGaussianSourceTiltExponent Nt Ns P a mass κ g

  have hHrho_E : Integrable
      (fun φ => fderiv ℝ H φ v * Real.exp (-(fun y => -E y) φ))
      (volume : Measure (AsymLatticeField Nt Ns)) := by
    simpa [E, asymGaussianSourceTiltDensity] using hHrho
  have hHrhod_E : Integrable
      (fun φ => H φ *
        fderiv ℝ (fun y => Real.exp (-(fun z => -E z) y)) φ v)
      (volume : Measure (AsymLatticeField Nt Ns)) := by
    simpa [E, asymGaussianSourceTiltDensity] using hHrhod
  have hHrho'_E : Integrable
      (fun φ => H φ * Real.exp (-(fun y => -E y) φ))
      (volume : Measure (AsymLatticeField Nt Ns)) := by
    simpa [E, asymGaussianSourceTiltDensity] using hHrho'
  have hH_E : ∀ φ ∈ tsupport
      (fun y => Real.exp (-(fun z => -E z) y)),
      DifferentiableAt ℝ H φ := by
    simpa [E, asymGaussianSourceTiltDensity] using hH
  have hρ_E : ∀ φ ∈ tsupport H,
      DifferentiableAt ℝ (fun y => Real.exp (-(fun z => -E z) y)) φ := by
    intro φ hφ
    simpa only [Pi.neg_apply, neg_neg] using
      (asymGaussianSourceTiltExponent_differentiableAt
        Nt Ns P a mass κ g φ).exp
  have hchain_E : ∀ φ,
      fderiv ℝ (fun y => Real.exp (-(fun z => -E z) y)) φ v =
        -(fderiv ℝ (fun y => -E y) φ v) *
          Real.exp (-(fun z => -E z) φ) := by
    intro φ
    simp only [Pi.neg_apply, neg_neg]
    rw [fderiv_exp (asymGaussianSourceTiltExponent_differentiableAt
      Nt Ns P a mass κ g φ), fderiv_fun_neg]
    simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    ring
  have hibp := integral_fderiv_mul_exp_neg_eq_integral_mul_fderiv_exp_neg
    (μ := (volume : Measure (AsymLatticeField Nt Ns)))
    H (fun y => -E y) v hHrho_E hHrhod_E hHrho'_E hH_E hρ_E hchain_E
  have hscore_E : ∀ φ,
      fderiv ℝ E φ v =
        asymGaussianSourceTiltScore Nt Ns P a mass κ g φ v := by
    intro φ
    exact asymGaussianSourceTiltExponent_fderiv_fieldShift
      Nt Ns P a mass κ g φ v
  have hpotential_E : ∀ φ,
      fderiv ℝ (fun y => -E y) φ v =
        -asymGaussianSourceTiltScore Nt Ns P a mass κ g φ v := by
    intro φ
    rw [fderiv_fun_neg]
    simpa only [ContinuousLinearMap.neg_apply] using
      congrArg (fun z : ℝ => -z) (hscore_E φ)
  have hrewrite :
      (fun φ => H φ * fderiv ℝ (fun y => -E y) φ v *
        Real.exp (-(fun z => -E z) φ)) =
      (fun φ => -(H φ * asymGaussianSourceTiltScore
        Nt Ns P a mass κ g φ v *
        asymGaussianSourceTiltDensity Nt Ns P a mass κ g φ)) := by
    funext φ
    rw [hpotential_E]
    simp [E, asymGaussianSourceTiltDensity]
  calc
    ∫ φ : AsymLatticeField Nt Ns,
        fderiv ℝ H φ v * asymGaussianSourceTiltDensity Nt Ns P a mass κ g φ
      ∂(volume : Measure (AsymLatticeField Nt Ns)) =
        ∫ φ : AsymLatticeField Nt Ns,
          fderiv ℝ H φ v * Real.exp (-(fun y => -E y) φ)
          ∂(volume : Measure (AsymLatticeField Nt Ns)) := by
            congr 1
            funext φ
            simp [E, asymGaussianSourceTiltDensity]
    _ = ∫ φ : AsymLatticeField Nt Ns,
          H φ * fderiv ℝ (fun y => -E y) φ v *
            Real.exp (-(fun z => -E z) φ)
          ∂(volume : Measure (AsymLatticeField Nt Ns)) := hibp
    _ = ∫ φ : AsymLatticeField Nt Ns,
          -(H φ * asymGaussianSourceTiltScore
            Nt Ns P a mass κ g φ v *
            asymGaussianSourceTiltDensity Nt Ns P a mass κ g φ)
          ∂(volume : Measure (AsymLatticeField Nt Ns)) := by
            rw [hrewrite]
    _ = -∫ φ : AsymLatticeField Nt Ns,
          H φ * asymGaussianSourceTiltScore
            Nt Ns P a mass κ g φ v *
            asymGaussianSourceTiltDensity Nt Ns P a mass κ g φ
          ∂(volume : Measure (AsymLatticeField Nt Ns)) := by
            rw [integral_neg]

end Pphi2
