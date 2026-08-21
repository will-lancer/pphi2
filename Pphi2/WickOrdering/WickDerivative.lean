/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Pphi2.WickOrdering.WickPolynomial

/-!
# Derivatives of Wick monomials and Wick polynomials

Scalar calculus for `wickMonomial` / `wickPolynomial`, used by the finite
source-tilt score identity. This is not an integration-by-parts statement.
-/

noncomputable section

namespace Pphi2

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
  have h := htop.add hsum
  simpa [wickPolynomialDerivative, Finset.sum_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, mul_assoc] using h

end Pphi2

end
