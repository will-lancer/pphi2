/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Finite source-tilt calculus

This file records the algebraic derivatives needed before an interacting
finite-dimensional integration-by-parts proof can start.  The coordinate
change is made through the existing measurable equivalence
`evalMapAsymMeasurableEquiv`.  No integration-by-parts statement is asserted
here.  The displayed exponential is the interacting source weight relative
to the free Gaussian measure; a complete score identity must still combine
it with Gaussian integration by parts and the required integrability.
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Pphi2.AsymTorus.AsymMeasureFactorization

noncomputable section

open GaussianField MeasureTheory
open scoped BigOperators

namespace Pphi2

/-! ## Derivatives of the Wick interaction -/

/-- The derivative of a Wick monomial, including the `n = 0` case. -/
theorem wickMonomial_hasDerivAt_all (n : ℕ) (c : ℝ) :
    ∀ x, HasDerivAt (wickMonomial n c)
      ((n : ℝ) * wickMonomial (n - 1) c x) x := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro x
      cases n with
      | zero =>
          simpa using (hasDerivAt_const x (1 : ℝ))
      | succ n =>
          cases n with
          | zero =>
              simpa using (hasDerivAt_id x)
          | succ n =>
              have h₁ := (hasDerivAt_id x).mul
                (ih (n + 1) (by omega) x)
              have h₂ := (hasDerivAt_const x (((n + 1 : ℕ) : ℝ) * c)).mul
                (ih n (by omega) x)
              have h := h₁.sub h₂
              convert h using 1 <;>
                simp only [wickMonomial_succ_succ, Nat.succ_eq_add_one,
                  Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
              · ring
              · ring

/-- The pointwise derivative appearing in the Wick-ordered interaction. -/
def wickPolynomialDerivative (P : InteractionPolynomial) (c x : ℝ) : ℝ :=
  (1 / (P.n : ℝ)) *
      ((P.n : ℝ) * wickMonomial (P.n - 1) c x) +
    ∑ m : Fin P.n,
      P.coeff m * (((m : ℕ) : ℝ) * wickMonomial ((m : ℕ) - 1) c x)

/-- The Wick polynomial has the derivative given by differentiating each
Wick monomial in its finite defining sum. -/
theorem wickPolynomial_hasDerivAt (P : InteractionPolynomial) (c x : ℝ) :
    HasDerivAt (wickPolynomial P c) (wickPolynomialDerivative P c x) x := by
  unfold wickPolynomial
  have htop := (wickMonomial_hasDerivAt_all P.n c x).const_mul
    (1 / (P.n : ℝ))
  have hsum : HasDerivAt
      (fun y : ℝ => ∑ m : Fin P.n,
        P.coeff m * wickMonomial (m : ℕ) c y)
      (∑ m : Fin P.n,
        P.coeff m * (((m : ℕ) : ℝ) * wickMonomial ((m : ℕ) - 1) c x)) x := by
    have h := HasDerivAt.sum (fun m (_ : m ∈ (Finset.univ : Finset (Fin P.n))) =>
      (wickMonomial_hasDerivAt_all (m : ℕ) c x).const_mul (P.coeff m))
    convert h using 1 <;>
      simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h := htop.add hsum
  simpa [wickPolynomialDerivative, Finset.sum_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, mul_assoc] using h

/-! ## Coordinate shifts -/

/-- A finite-field translation of a configuration.  The translation is made
in coordinates, then returned to the configuration space by the existing
inverse evaluation map. -/
noncomputable def asymCoordinateShift
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (ω : Configuration (AsymLatticeField Nt Ns))
    (v : AsymLatticeField Nt Ns) (t : ℝ) :
    Configuration (AsymLatticeField Nt Ns) :=
  evalMapAsymInv Nt Ns (evalMapAsym Nt Ns ω + t • v)

/-- Evaluation of the coordinate shift at a lattice delta function. -/
theorem asymCoordinateShift_eval_delta
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (ω : Configuration (AsymLatticeField Nt Ns))
    (v : AsymLatticeField Nt Ns) (t : ℝ)
    (x : AsymLatticeSites Nt Ns) :
    asymCoordinateShift Nt Ns ω v t (asymLatticeDelta Nt Ns x) =
      (evalMapAsym Nt Ns ω) x + t * v x := by
  unfold asymCoordinateShift
  change (evalMapAsym Nt Ns
      (evalMapAsymInv Nt Ns (evalMapAsym Nt Ns ω + t • v))) x = _
  rw [evalMap_evalMapInvAsym]
  rfl

/-- Directional derivative of a finite coordinate pairing. -/
theorem configuration_pairing_hasDerivAt_coordinateShift
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (ω : Configuration (AsymLatticeField Nt Ns))
    (v g : AsymLatticeField Nt Ns) (t : ℝ) :
    HasDerivAt
      (fun s => asymCoordinateShift Nt Ns ω v s g)
      (∑ x : AsymLatticeSites Nt Ns, g x * v x) t := by
  have hsum : HasDerivAt
      (fun s : ℝ => ∑ x : AsymLatticeSites Nt Ns,
        g x * ((evalMapAsym Nt Ns ω) x + s * v x))
      (∑ x : AsymLatticeSites Nt Ns, g x * v x) t := by
    apply HasDerivAt.fun_sum
    intro x hx
    have harg := (hasDerivAt_const t ((evalMapAsym Nt Ns ω) x)).add
      ((hasDerivAt_id t).mul_const (v x))
    have hterm := harg.const_mul (g x)
    convert hterm using 1 <;> ring
  convert hsum using 1
  · funext s
    rw [config_apply_eq_sum_evalMapAsym]
    apply Finset.sum_congr rfl
    intro x hx
    simp [asymCoordinateShift, evalMap_evalMapInvAsym,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- Directional derivative of the interacting action along a finite coordinate
shift.  This is an algebraic identity, independent of the interacting
measure. -/
theorem interactionFunctionalAsym_hasDerivAt_coordinateShift
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ)
    (ω : Configuration (AsymLatticeField Nt Ns))
    (v : AsymLatticeField Nt Ns) (t : ℝ) :
    HasDerivAt
      (fun s => interactionFunctionalAsym Nt Ns P a mass
        (asymCoordinateShift Nt Ns ω v s))
      (a ^ 2 * ∑ x : AsymLatticeSites Nt Ns,
        wickPolynomialDerivative P (wickConstantAsym Nt Ns a mass)
          ((evalMapAsym Nt Ns ω) x + t * v x) * v x) t := by
  have hsum : HasDerivAt
      (fun s : ℝ => ∑ x : AsymLatticeSites Nt Ns,
        wickPolynomial P (wickConstantAsym Nt Ns a mass)
          ((evalMapAsym Nt Ns ω) x + s * v x))
      (∑ x : AsymLatticeSites Nt Ns,
        wickPolynomialDerivative P (wickConstantAsym Nt Ns a mass)
          ((evalMapAsym Nt Ns ω) x + t * v x) * v x) t := by
    apply HasDerivAt.fun_sum
    intro x hx
    have harg := (hasDerivAt_const t ((evalMapAsym Nt Ns ω) x)).add
      ((hasDerivAt_id t).mul_const (v x))
    exact (wickPolynomial_hasDerivAt P (wickConstantAsym Nt Ns a mass)
      ((evalMapAsym Nt Ns ω) x + t * v x)).comp t harg
  have hscaled := hsum.const_mul (a ^ 2)
  convert hscaled using 1
  · funext s
    simp only [interactionFunctionalAsym]
    apply congrArg (fun z : ℝ => a ^ 2 * z)
    apply Finset.sum_congr rfl
    intro x hx
    rw [asymCoordinateShift_eval_delta]
  · simp only [interactionFunctionalAsym]
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    rfl

/-! ## Source exponent and tilted-density chain rule -/

/-- Directional derivative of the source exponent used by the DDJ tilt. -/
theorem sourceExponent_hasDerivAt_coordinateShift
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (g : AsymLatticeField Nt Ns)
    (ω : Configuration (AsymLatticeField Nt Ns))
    (v : AsymLatticeField Nt Ns) (t : ℝ) :
    HasDerivAt
      (fun s =>
        (asymCoordinateShift Nt Ns ω v s g) ^ P.n / (P.n : ℝ))
      (((P.n : ℝ) *
          (asymCoordinateShift Nt Ns ω v t g) ^ (P.n - 1)) /
        (P.n : ℝ) *
        (∑ x : AsymLatticeSites Nt Ns, g x * v x)) t := by
  have hpair := configuration_pairing_hasDerivAt_coordinateShift
    Nt Ns ω v g t
  have hpow := (hasDerivAt_pow P.n
      (asymCoordinateShift Nt Ns ω v t g)).comp t hpair
  have hdiv := hpow.div_const (P.n : ℝ)
  convert hdiv using 1 <;> ring

/-- Pointwise derivative of the interacting source weight relative to the
free Gaussian measure.  An actual finite-dimensional integration-by-parts
theorem still has to supply the Gaussian quadratic score and justify the
integral identity. -/
theorem asymTiltedDensityIntegrand_hasDerivAt_coordinateShift
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ)
    (g v : AsymLatticeField Nt Ns)
    (ω : Configuration (AsymLatticeField Nt Ns))
    (t : ℝ) (H : Configuration (AsymLatticeField Nt Ns) → ℝ)
    (dH : ℝ)
    (hH : HasDerivAt
      (fun s => H (asymCoordinateShift Nt Ns ω v s)) dH t) :
    HasDerivAt
      (fun s =>
        H (asymCoordinateShift Nt Ns ω v s) *
          Real.exp (
            (asymCoordinateShift Nt Ns ω v s g) ^ P.n / (P.n : ℝ) -
              interactionFunctionalAsym Nt Ns P a mass
                (asymCoordinateShift Nt Ns ω v s)))
      ((dH + H (asymCoordinateShift Nt Ns ω v t) *
          ((((P.n : ℝ) *
              (asymCoordinateShift Nt Ns ω v t g) ^ (P.n - 1)) /
            (P.n : ℝ) *
            (∑ x : AsymLatticeSites Nt Ns, g x * v x)) -
            (a ^ 2 * ∑ x : AsymLatticeSites Nt Ns,
              wickPolynomialDerivative P (wickConstantAsym Nt Ns a mass)
                ((evalMapAsym Nt Ns ω) x + t * v x) * v x))) *
        Real.exp (
          (asymCoordinateShift Nt Ns ω v t g) ^ P.n / (P.n : ℝ) -
            interactionFunctionalAsym Nt Ns P a mass
              (asymCoordinateShift Nt Ns ω v t))) t := by
  have hsource := sourceExponent_hasDerivAt_coordinateShift
    Nt Ns P g ω v t
  have hinteraction := interactionFunctionalAsym_hasDerivAt_coordinateShift
    Nt Ns P a mass ω v t
  have hexp := (hsource.sub hinteraction).exp
  have hprod := hH.mul hexp
  convert hprod using 1 <;> ring

end Pphi2
