/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Source-strength differentiation for the finite asymmetric lattice measure

This file specializes the measure-theoretic differentiation lemma from
`Pphi2.GeneralResults.TiltPartitionDerivative` to the interacting asymmetric
lattice measure.  The domination hypothesis is local in the source strength.
The finite lattice observable is kept in its normalized form
`(ω g)^P.n / (P.n : ℝ)`, so no cell-area factor is introduced here.
-/

import Pphi2.AsymTorus.AsymLatticeMeasure
import Pphi2.GeneralResults.TiltPartitionDerivative

noncomputable section

namespace Pphi2

open MeasureTheory

/-!
## Local source-strength derivative

The exponential source is `F_g = (ω g)^n / n`.  The explicit domination
hypothesis is the integrability of
`exp ((|κ| + ε) |F_g|) |F_g|` under the original interacting measure.  It
controls the derivative on a whole neighbourhood of `κ`.
-/

/--
Differentiate the logarithm of the source partition function at an arbitrary
finite source strength.  The derivative is the normalized `P.n`-th source
moment under the corresponding exponential tilt.

The assumptions `h_exp` and `h_dom` are the local analytic input.  Everything
else in this theorem is finite-measure plumbing: the source observable is
measurable, the interacting lattice measure is a probability measure, its
partition integral is positive, and the generic logarithmic differentiation
lemma applies.
-/
theorem interactingLatticeMeasureAsym_hasDerivAt_log_source_partition
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (g : AsymLatticeField Nt Ns)
    (κ ε : ℝ) (hε : 0 < ε)
    (h_exp : Integrable
      (fun ω : Configuration (AsymLatticeField Nt Ns) =>
        Real.exp (κ * ((ω g) ^ P.n / (P.n : ℝ))))
      (interactingLatticeMeasureAsym Nt Ns P a mass ha hmass))
    (h_dom : Integrable
      (fun ω : Configuration (AsymLatticeField Nt Ns) =>
        Real.exp ((|κ| + ε) * |((ω g) ^ P.n / (P.n : ℝ))|) *
          |((ω g) ^ P.n / (P.n : ℝ))|)
      (interactingLatticeMeasureAsym Nt Ns P a mass ha hmass)) :
    HasDerivAt
      (fun t : ℝ =>
        Real.log (∫ ω : Configuration (AsymLatticeField Nt Ns),
          Real.exp (t * ((ω g) ^ P.n / (P.n : ℝ)))
          ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass)))
      ((∫ ω : Configuration (AsymLatticeField Nt Ns),
          (ω g) ^ P.n ∂((interactingLatticeMeasureAsym Nt Ns P a mass ha hmass).tilted
            (fun ω => κ * ((ω g) ^ P.n / (P.n : ℝ))))) /
        (P.n : ℝ)) κ := by
  let μ := interactingLatticeMeasureAsym Nt Ns P a mass ha hmass
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact interactingLatticeMeasureAsym_isProbability Nt Ns P a mass ha hmass
  have hF_meas : Measurable
      (fun ω : Configuration (AsymLatticeField Nt Ns) =>
        (ω g) ^ P.n / (P.n : ℝ)) := by
    exact ((configuration_eval_measurable g).pow_const P.n).div measurable_const
  have hZ_pos : 0 < ∫ ω : Configuration (AsymLatticeField Nt Ns),
      Real.exp (κ * ((ω g) ^ P.n / (P.n : ℝ))) ∂μ := by
    rw [integral_pos_iff_support_of_nonneg
      (fun ω => le_of_lt (Real.exp_pos _)) h_exp]
    have hsup : Function.support
        (fun ω : Configuration (AsymLatticeField Nt Ns) =>
          Real.exp (κ * ((ω g) ^ P.n / (P.n : ℝ)))) = Set.univ := by
      ext ω
      simp [Function.mem_support, ne_of_gt (Real.exp_pos _)]
    rw [hsup]
    exact Measure.measure_univ_pos.mpr (IsProbabilityMeasure.ne_zero _)
  have hderiv :=
    hasDerivAt_log_integral_exp_mul_of_local_dom
      μ (fun ω : Configuration (AsymLatticeField Nt Ns) =>
        (ω g) ^ P.n / (P.n : ℝ)) κ ε hε hF_meas h_exp h_dom hZ_pos
  have hmoment :
      (∫ ω : Configuration (AsymLatticeField Nt Ns),
          (ω g) ^ P.n / (P.n : ℝ)
          ∂(μ.tilted (fun ω => κ * ((ω g) ^ P.n / (P.n : ℝ))))) =
        (∫ ω : Configuration (AsymLatticeField Nt Ns),
          (ω g) ^ P.n
          ∂(μ.tilted (fun ω => κ * ((ω g) ^ P.n / (P.n : ℝ))))) /
          (P.n : ℝ) := by
    rw [integral_div]
  rw [hmoment] at hderiv
  simpa [μ] using hderiv

end Pphi2
