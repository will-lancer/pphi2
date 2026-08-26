/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Uniform source pressure and tilted moments

This file records the volume-uniform source-pressure input for the asymmetric
lattice family and proves its tilted `P.n`-moment consequence.  The pressure
constant is chosen before the temporal side, both lattice cardinalities, the
spacing, and the source.
-/

import Pphi2.AsymTorus.AsymDDJSourceBall
import Pphi2.GeneralResults.TiltPressureMoment

noncomputable section

open GaussianField MeasureTheory

namespace Pphi2

/-- A doubled-source pressure constant for the interacting Wick measure.

The same `Cpressure` applies throughout the small-spacing, fixed-spatial-side
family.  The source belongs to the deterministic ball supplied by
`asymDDJSourceBall_of_centered_decay`.
-/
def AsymDoubledSourcePressureBound
    (P : InteractionPolynomial) (mass Ls : ℝ) [Fact (0 < Ls)]
    (hmass : 0 < mass) (Cpressure : ℝ) : Prop :=
  ∀ (Lt : ℝ) [Fact (0 < Lt)], (4 : ℝ) ≤ Lt →
    ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
      (a : ℝ) (ha : 0 < a),
      (Nt : ℝ) * a = Lt →
      (Ns : ℝ) * a = Ls →
      a ≤ (1 : ℝ) →
      ∀ f : CylinderTestFunction Ls,
        let g : AsymLatticeField Nt Ns :=
          asymLatticeTestFnIso Lt Ls Nt Ns a
            (cylinderToTorusEmbed Lt Ls f)
        AsymDDJSourceBall P.n a g →
          Integrable
              (fun ω : Configuration (AsymLatticeField Nt Ns) =>
                Real.exp (2 * ((ω g) ^ P.n / (P.n : ℝ))))
              (interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) ∧
            (∫ ω : Configuration (AsymLatticeField Nt Ns),
                Real.exp (2 * ((ω g) ^ P.n / (P.n : ℝ)))
              ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass)) ≤
              Real.exp Cpressure

/-- A volume-uniform doubled-source pressure bound and its normalized tilted
`P.n` moment, with the latter bounded by `P.n * Cpressure`.

The returned source radius and seminorm depend on `P` and the spatial side.
Every displayed moment uses the interacting Wick measure.
-/
theorem asymUniformTiltedMoment_of_doubledSourcePressure
    (P : InteractionPolynomial) (mass Ls : ℝ) [Fact (0 < Ls)]
    (hmass : 0 < mass)
    (Cpressure : ℝ) (hCpressure : 0 < Cpressure)
    (hpressure :
      AsymDoubledSourcePressureBound P mass Ls hmass Cpressure) :
    ∃ (r : ℝ) (q : Seminorm ℝ (CylinderTestFunction Ls)),
      0 < r ∧ Continuous q ∧
      ∀ (Lt : ℝ) [Fact (0 < Lt)], (4 : ℝ) ≤ Lt →
        ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
          (a : ℝ) (ha : 0 < a),
          (Nt : ℝ) * a = Lt →
          (Ns : ℝ) * a = Ls →
          a ≤ (1 : ℝ) →
          ∀ f : CylinderTestFunction Ls, q f ≤ r →
            let g : AsymLatticeField Nt Ns :=
              asymLatticeTestFnIso Lt Ls Nt Ns a
                (cylinderToTorusEmbed Lt Ls f)
            (Integrable
                (fun ω : Configuration (AsymLatticeField Nt Ns) =>
                  Real.exp (2 * ((ω g) ^ P.n / (P.n : ℝ))))
                (interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) ∧
              (∫ ω : Configuration (AsymLatticeField Nt Ns),
                  Real.exp (2 * ((ω g) ^ P.n / (P.n : ℝ)))
                ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass)) ≤
                  Real.exp Cpressure) ∧
            (Integrable
                (fun ω : Configuration (AsymLatticeField Nt Ns) =>
                  (ω g) ^ P.n)
                ((interactingLatticeMeasureAsym Nt Ns P a mass ha hmass).tilted
                  (fun ω : Configuration (AsymLatticeField Nt Ns) =>
                    (ω g) ^ P.n / (P.n : ℝ))) ∧
              (∫ ω : Configuration (AsymLatticeField Nt Ns),
                  (ω g) ^ P.n
                ∂((interactingLatticeMeasureAsym Nt Ns P a mass ha hmass).tilted
                  (fun ω : Configuration (AsymLatticeField Nt Ns) =>
                    (ω g) ^ P.n / (P.n : ℝ)))) ≤
                (P.n : ℝ) * Cpressure) := by
  obtain ⟨r, q, hr, hq, hsource⟩ :=
    asymDDJSourceBall_of_centered_decay P Ls
  refine ⟨r, q, hr, hq, ?_⟩
  intro Lt _ hLt Nt Ns _ _ a ha hLtvol hLsvol ha_le f hqf
  let g : AsymLatticeField Nt Ns :=
    asymLatticeTestFnIso Lt Ls Nt Ns a
      (cylinderToTorusEmbed Lt Ls f)
  let μ : Measure (Configuration (AsymLatticeField Nt Ns)) :=
    interactingLatticeMeasureAsym Nt Ns P a mass ha hmass
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact interactingLatticeMeasureAsym_isProbability
      Nt Ns P a mass ha hmass
  have hball : AsymDDJSourceBall P.n a g := by
    simpa [g] using
      hsource Lt hLt Nt Ns a ha hLtvol hLsvol ha_le f hqf
  obtain ⟨h_exp_two, h_exp_two_bound⟩ :=
    hpressure Lt hLt Nt Ns a ha hLtvol hLsvol ha_le f hball
  have hcore :=
    integrable_tilted_pow_le_of_log_exp_two
      μ P.n (by have := P.hn_ge; omega)
      (fun ω : Configuration (AsymLatticeField Nt Ns) => ω g)
      Cpressure
      (configuration_eval_measurable g)
      (fun ω => P.hn_even.pow_nonneg (ω g))
      (by simpa [μ, g] using h_exp_two)
      (by simpa [μ, g] using h_exp_two_bound)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simpa [μ, g] using h_exp_two
  · simpa [μ, g] using h_exp_two_bound
  · simpa [μ, g] using hcore

end Pphi2

end
