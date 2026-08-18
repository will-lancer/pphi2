/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Local degree-n exponential moment on the finite asymmetric lattice

This file assembles two finite-volume interfaces.  The weighted source-ball
bridge supplies integrability of the degree-`P.n` source exponential.  A
source-tilted `P.n`-moment estimate then supplies the literal bound `2` via
the entropy adapter in `AsymTiltedMoment.lean`.

The tilted estimate remains an explicit hypothesis.  This declaration records
the exact finite-grid consumer for a future uniform analytic producer.
It does **not** prove Dimock–Dang–Jäkel (DDJ) 5.3/6.1.
-/

import Pphi2.AsymTorus.AsymDDJSource

noncomputable section

open MeasureTheory

namespace Pphi2

variable {Lt Ls : ℝ} [Fact (0 < Lt)] [Fact (0 < Ls)]

/--
The weighted source ball and a normalized source-tilted `P.n`-moment bound
imply the local degree-`P.n` exponential moment bound with constant `2`.

The hypothesis `h_tilted_moment` is the finite source-tilted energy input.  It
is stated against the normalized tilt of the interacting lattice measure, so
the entropy step applies without any density rewrite at this layer.
This does not prove DDJ 5.3/6.1.
-/
theorem interactingLatticeMeasureAsym_exp_moment_le_two_of_weightedLpPow_and_tiltedMoment
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (f : AsymTorusTestFunction Lt Ls)
    (hLp :
      asymWeightedLpPow
          ((P.n : ℝ) / ((P.n : ℝ) - 1)) a
          (asymRawSource a (asymLatticeTestFnIso Lt Ls Nt Ns a f)) ≤
        (1 / 2 : ℝ) ^ ((P.n : ℝ) / ((P.n : ℝ) - 1)))
    (h_tilted_moment :
      Integrable
        (fun ω : Configuration (AsymLatticeField Nt Ns) =>
          (ω (asymLatticeTestFnIso Lt Ls Nt Ns a f)) ^ P.n)
        ((interactingLatticeMeasureAsym Nt Ns P a mass ha hmass).tilted
          (fun ω : Configuration (AsymLatticeField Nt Ns) =>
            (ω (asymLatticeTestFnIso Lt Ls Nt Ns a f)) ^ P.n / (P.n : ℝ))))
    (h_tilted_moment_bound :
      (∫ ω : Configuration (AsymLatticeField Nt Ns),
          (ω (asymLatticeTestFnIso Lt Ls Nt Ns a f)) ^ P.n
        ∂((interactingLatticeMeasureAsym Nt Ns P a mass ha hmass).tilted
          (fun ω : Configuration (AsymLatticeField Nt Ns) =>
            (ω (asymLatticeTestFnIso Lt Ls Nt Ns a f)) ^ P.n / (P.n : ℝ)))) ≤
      (P.n : ℝ) * Real.log 2) :
    Integrable
        (fun ω : Configuration (AsymLatticeField Nt Ns) =>
          Real.exp ((ω (asymLatticeTestFnIso Lt Ls Nt Ns a f)) ^ P.n / (P.n : ℝ)))
        (interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) ∧
      ∫ ω : Configuration (AsymLatticeField Nt Ns),
          Real.exp ((ω (asymLatticeTestFnIso Lt Ls Nt Ns a f)) ^ P.n / (P.n : ℝ))
        ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) ≤ 2 := by
  let μ := interactingLatticeMeasureAsym Nt Ns P a mass ha hmass
  let g : AsymLatticeField Nt Ns :=
    asymLatticeTestFnIso Lt Ls Nt Ns a f
  letI : IsProbabilityMeasure μ :=
    interactingLatticeMeasureAsym_isProbability Nt Ns P a mass ha hmass
  have h_exp :
      Integrable (fun ω : Configuration (AsymLatticeField Nt Ns) =>
        Real.exp ((ω g) ^ P.n / (P.n : ℝ))) μ := by
    simpa [μ, g] using
      (interactingLatticeMeasureAsym_integrable_exp_of_weightedLpPow
        Lt Ls Nt Ns P a mass ha hmass f hLp)
  have h_two :
      (∫ ω : Configuration (AsymLatticeField Nt Ns),
          Real.exp ((ω g) ^ P.n / (P.n : ℝ)) ∂μ) ≤ 2 := by
    apply integral_exp_pow_div_nat_le_two_of_tilted_moment
      (μ := μ) (n := P.n) (hn_pos := by have := P.hn_ge; omega)
      (X := fun ω => ω g)
    · exact h_exp
    · simpa [μ, g] using h_tilted_moment
    · simpa [μ, g] using h_tilted_moment_bound
  refine ⟨?_, ?_⟩
  · simpa [μ, g] using h_exp
  · simpa [μ, g] using h_two

end Pphi2
