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
              convert h using 1
              · ext y
                simp [id, wickMonomial_succ_succ]
              · simp only [wickMonomial_succ_succ, Nat.add_sub_cancel,
                  Nat.cast_add, Nat.cast_one, id]
                cases n with
                | zero => simp [wickMonomial]; ring
                | succ j =>
                    rw [wickMonomial_succ_succ j c x]
                    push_cast
                    ring

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
    convert h using 1
    · ext y
      simp [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    · simp [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
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
    convert (wickPolynomial_hasDerivAt P (wickConstantAsym Nt Ns a mass)
      ((evalMapAsym Nt Ns ω) x + t * v x)).comp t harg using 1 <;> ring
  have hscaled := hsum.const_mul (a ^ 2)
  convert hscaled using 1

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
  convert hprod using 1 <;>
    simp only [Pi.mul_apply, Pi.sub_apply] <;>
    ring

/-! ## Coordinate density and score calculus -/

/-- The finite massive quadratic form in coordinate variables. -/
def asymQuadraticForm
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (φ : AsymLatticeField Nt Ns) : ℝ :=
  ∑ x : AsymLatticeSites Nt Ns,
    φ x * (massOperatorAsym Nt Ns a mass φ) x

/-- The coordinate source pairing. -/
def asymCoordinateSourcePairing
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (g φ : AsymLatticeField Nt Ns) : ℝ :=
  ∑ x : AsymLatticeSites Nt Ns, g x * φ x

/-- The Wick interaction after passing from configurations to coordinates. -/
def asymCoordinateWickAction
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ)
    (φ : AsymLatticeField Nt Ns) : ℝ :=
  a ^ 2 * ∑ x : AsymLatticeSites Nt Ns,
    wickPolynomial P (wickConstantAsym Nt Ns a mass) (φ x)

/-- Coordinate form of the source exponent, with an explicit source strength
`κ`. -/
def asymCoordinateSourceExponent
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (κ : ℝ) (g φ : AsymLatticeField Nt Ns) : ℝ :=
  κ * (asymCoordinateSourcePairing Nt Ns g φ) ^ P.n / (P.n : ℝ)

/-- The complete finite Gaussian density after adding a Wick interaction and
the source `κ · (φ(g))^n/n`. -/
def asymGaussianSourceTiltExponent
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass κ : ℝ)
    (g φ : AsymLatticeField Nt Ns) : ℝ :=
  -(a ^ 2 / 2 : ℝ) * asymQuadraticForm Nt Ns a mass φ -
      asymCoordinateWickAction Nt Ns P a mass φ +
      asymCoordinateSourceExponent Nt Ns P κ g φ

noncomputable def asymGaussianSourceTiltDensity
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass κ : ℝ)
    (g φ : AsymLatticeField Nt Ns) : ℝ :=
  Real.exp (asymGaussianSourceTiltExponent Nt Ns P a mass κ g φ)

/-- The complete coordinate density factors into the Gaussian density, the
Wick Boltzmann factor, and the source factor. -/
theorem asymGaussianSourceTiltDensity_eq_product
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass κ : ℝ)
    (g φ : AsymLatticeField Nt Ns) :
    asymGaussianSourceTiltDensity Nt Ns P a mass κ g φ =
      gaussianDensityAsym Nt Ns a mass φ *
        Real.exp (-asymCoordinateWickAction Nt Ns P a mass φ +
          asymCoordinateSourceExponent Nt Ns P κ g φ) := by
  unfold asymGaussianSourceTiltDensity asymGaussianSourceTiltExponent
    asymQuadraticForm asymCoordinateWickAction
    gaussianDensityAsym
  rw [← Real.exp_add]
  congr 1
  ring

/-- The coordinate Wick action agrees with the existing configuration action
after applying the inverse evaluation map. -/
theorem asymCoordinateWickAction_eq_interactionFunctionalAsym
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ)
    (φ : AsymLatticeField Nt Ns) :
    asymCoordinateWickAction Nt Ns P a mass φ =
      interactionFunctionalAsym Nt Ns P a mass (evalMapAsymInv Nt Ns φ) := by
  simpa [asymCoordinateWickAction] using
    (interactionFunctionalAsym_evalMapAsymInv Nt Ns P a mass φ).symm

/-- Derivative of the coordinate source pairing along a field shift. -/
theorem asymCoordinateSourcePairing_hasDerivAt_fieldShift
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (g φ v : AsymLatticeField Nt Ns) (t : ℝ) :
    HasDerivAt
      (fun s => asymCoordinateSourcePairing Nt Ns g (φ + s • v))
      (∑ x : AsymLatticeSites Nt Ns, g x * v x) t := by
  have hsum : HasDerivAt
      (fun s : ℝ => ∑ x : AsymLatticeSites Nt Ns,
        g x * (φ x + s * v x))
      (∑ x : AsymLatticeSites Nt Ns, g x * v x) t := by
    apply HasDerivAt.fun_sum
    intro x hx
    have harg := (hasDerivAt_const t (φ x)).add
      ((hasDerivAt_id t).mul_const (v x))
    have hterm := harg.const_mul (g x)
    convert hterm using 1 <;> ring
  simpa [asymCoordinateSourcePairing, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul] using hsum

/-- Derivative of the coordinate Wick action along a field shift. -/
theorem asymCoordinateWickAction_hasDerivAt_fieldShift
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ)
    (φ v : AsymLatticeField Nt Ns) (t : ℝ) :
    HasDerivAt
      (fun s => asymCoordinateWickAction Nt Ns P a mass (φ + s • v))
      (a ^ 2 * ∑ x : AsymLatticeSites Nt Ns,
        wickPolynomialDerivative P (wickConstantAsym Nt Ns a mass)
          (φ x + t * v x) * v x) t := by
  have hsum : HasDerivAt
      (fun s : ℝ => ∑ x : AsymLatticeSites Nt Ns,
        wickPolynomial P (wickConstantAsym Nt Ns a mass) (φ x + s * v x))
      (∑ x : AsymLatticeSites Nt Ns,
        wickPolynomialDerivative P (wickConstantAsym Nt Ns a mass)
          (φ x + t * v x) * v x) t := by
    apply HasDerivAt.fun_sum
    intro x hx
    have harg := (hasDerivAt_const t (φ x)).add
      ((hasDerivAt_id t).mul_const (v x))
    convert (wickPolynomial_hasDerivAt P (wickConstantAsym Nt Ns a mass)
      (φ x + t * v x)).comp t harg using 1 <;> ring
  have hscaled := hsum.const_mul (a ^ 2)
  simpa [asymCoordinateWickAction, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul] using hscaled

/-- Derivative of the quadratic form.  The second term in the product rule is
rewritten with `massOperatorAsym_selfAdjoint`. -/
theorem asymQuadraticForm_hasDerivAt_fieldShift
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (φ v : AsymLatticeField Nt Ns) (t : ℝ) :
    HasDerivAt
      (fun s => asymQuadraticForm Nt Ns a mass (φ + s • v))
      (2 * ∑ x : AsymLatticeSites Nt Ns,
        v x * (massOperatorAsym Nt Ns a mass (φ + t • v)) x) t := by
  let Q := massOperatorAsym Nt Ns a mass
  have hsum : HasDerivAt
      (fun s : ℝ => ∑ x : AsymLatticeSites Nt Ns,
        (φ x + s * v x) *
          (Q φ x + s * (Q v) x))
      (∑ x : AsymLatticeSites Nt Ns,
        (v x * (Q φ x + t * (Q v) x) +
          (φ x + t * v x) * (Q v) x)) t := by
    apply HasDerivAt.fun_sum
    intro x hx
    have hφ := (hasDerivAt_const t (φ x)).add
      ((hasDerivAt_id t).mul_const (v x))
    have hQ := (hasDerivAt_const t (Q φ x)).add
      ((hasDerivAt_id t).mul_const (Q v x))
    convert hφ.mul hQ using 1 <;> ring
  have hself :
      ∑ x : AsymLatticeSites Nt Ns,
        (φ + t • v) x * (Q v) x =
      ∑ x : AsymLatticeSites Nt Ns,
        v x * (Q (φ + t • v)) x := by
    have h := massOperatorAsym_selfAdjoint Nt Ns a mass v (φ + t • v)
    calc
      ∑ x : AsymLatticeSites Nt Ns, (φ + t • v) x * (Q v) x =
          ∑ x : AsymLatticeSites Nt Ns, (Q v) x * (φ + t • v) x := by
            apply Finset.sum_congr rfl
            intro x hx
            ring
      _ = ∑ x : AsymLatticeSites Nt Ns,
          v x * (Q (φ + t • v)) x := h.symm
  have hscaled := hsum
  unfold asymQuadraticForm
  convert hscaled using 1
  · funext s
    simp only [Q, massOperatorAsym, map_add, map_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
  · simp only [Q, massOperatorAsym, map_add, map_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    have hself' :
        ∑ x : AsymLatticeSites Nt Ns,
          (φ x + t * v x) * (Q v) x =
        ∑ x : AsymLatticeSites Nt Ns,
          v x * (Q φ x + t * (Q v) x) := by
      simpa [Q, map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        using hself
    rw [← hself', Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring

/-- Directional derivative of the source exponent with explicit strength `κ`. -/
theorem asymCoordinateSourceExponent_hasDerivAt_fieldShift
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (κ : ℝ) (g φ v : AsymLatticeField Nt Ns)
    (t : ℝ) :
    HasDerivAt
      (fun s => asymCoordinateSourceExponent Nt Ns P κ g (φ + s • v))
      (κ * (asymCoordinateSourcePairing Nt Ns g (φ + t • v)) ^ (P.n - 1) *
        (∑ x : AsymLatticeSites Nt Ns, g x * v x)) t := by
  have hpair := asymCoordinateSourcePairing_hasDerivAt_fieldShift
    Nt Ns g φ v t
  have hpow := (hasDerivAt_pow P.n
      (asymCoordinateSourcePairing Nt Ns g (φ + t • v))).comp t hpair
  have hsource := (hpow.const_mul κ).div_const (P.n : ℝ)
  have hn_pos : 0 < (P.n : ℝ) := by
    have hn : 0 < P.n := by have := P.hn_ge; omega
    exact_mod_cast hn
  have hn_ne : (P.n : ℝ) ≠ 0 := ne_of_gt hn_pos
  unfold asymCoordinateSourceExponent
  convert hsource using 1
  · simp [asymCoordinateSourcePairing, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp [hn_ne] <;> ring

/-- Directional derivative of the full Gaussian source-tilt exponent. -/
def asymGaussianSourceTiltScore
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass κ : ℝ)
    (g φ v : AsymLatticeField Nt Ns) : ℝ :=
  -(a ^ 2) * ∑ x : AsymLatticeSites Nt Ns,
      v x * (massOperatorAsym Nt Ns a mass φ) x -
    a ^ 2 * ∑ x : AsymLatticeSites Nt Ns,
      wickPolynomialDerivative P (wickConstantAsym Nt Ns a mass) (φ x) * v x +
    κ * (asymCoordinateSourcePairing Nt Ns g φ) ^ (P.n - 1) *
      (∑ x : AsymLatticeSites Nt Ns, g x * v x)

theorem asymGaussianSourceTiltExponent_hasDerivAt_fieldShift
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass κ : ℝ)
    (g φ v : AsymLatticeField Nt Ns) (t : ℝ) :
    HasDerivAt
      (fun s => asymGaussianSourceTiltExponent Nt Ns P a mass κ g (φ + s • v))
      (asymGaussianSourceTiltScore Nt Ns P a mass κ g (φ + t • v) v) t := by
  have hQ := asymQuadraticForm_hasDerivAt_fieldShift Nt Ns a mass φ v t
  have hW := asymCoordinateWickAction_hasDerivAt_fieldShift
    Nt Ns P a mass φ v t
  have hS := asymCoordinateSourceExponent_hasDerivAt_fieldShift
    Nt Ns P κ g φ v t
  unfold asymGaussianSourceTiltExponent asymGaussianSourceTiltScore
  have h := (hQ.const_mul (-(a ^ 2 / 2 : ℝ))).sub hW
  have h := h.add hS
  convert h using 1 <;>
    simp [asymQuadraticForm, asymCoordinateWickAction, asymCoordinateSourceExponent,
      asymCoordinateSourcePairing, Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;>
    ring

/-- Directional derivative of the complete Gaussian source-tilt density. -/
theorem asymGaussianSourceTiltDensity_hasDerivAt_fieldShift
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass κ : ℝ)
    (g φ v : AsymLatticeField Nt Ns) (t : ℝ) :
    HasDerivAt
      (fun s => asymGaussianSourceTiltDensity Nt Ns P a mass κ g (φ + s • v))
      (asymGaussianSourceTiltDensity Nt Ns P a mass κ g (φ + t • v) *
        asymGaussianSourceTiltScore Nt Ns P a mass κ g (φ + t • v) v) t := by
  have h := (asymGaussianSourceTiltExponent_hasDerivAt_fieldShift
    Nt Ns P a mass κ g φ v t).exp
  unfold asymGaussianSourceTiltDensity
  convert h using 1 <;> ring

/-- Product rule for a test function times the complete source-tilt density. -/
theorem asymGaussianSourceTiltWeightedDensity_hasDerivAt_fieldShift
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass κ : ℝ)
    (g φ v : AsymLatticeField Nt Ns) (t : ℝ)
    (H : AsymLatticeField Nt Ns → ℝ) (dH : ℝ)
    (hH : HasDerivAt (fun s => H (φ + s • v)) dH t) :
    HasDerivAt
      (fun s => H (φ + s • v) *
        asymGaussianSourceTiltDensity Nt Ns P a mass κ g (φ + s • v))
      ((dH + H (φ + t • v) *
          asymGaussianSourceTiltScore Nt Ns P a mass κ g (φ + t • v) v) *
        asymGaussianSourceTiltDensity Nt Ns P a mass κ g (φ + t • v)) t := by
  have hρ := asymGaussianSourceTiltDensity_hasDerivAt_fieldShift
    Nt Ns P a mass κ g φ v t
  have h := hH.mul hρ
  convert h using 1 <;> ring

end Pphi2
