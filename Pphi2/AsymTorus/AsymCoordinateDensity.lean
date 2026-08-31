/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Pphi2.AsymTorus.AsymLatticeMeasure
import GaussianField.DensityAsym

/-!
# Coordinate density of the interacting asymmetrical lattice measure

This file exposes the coordinate-density calculation used locally in
`AsymMeasureFactorization`.  The statement stops after the pushforward by
`evalMapAsym`, before the time-slice reindexing and the transfer-kernel path
density are introduced.
-/

noncomputable section

open MeasureTheory GaussianField
open scoped BigOperators ENNReal

namespace Pphi2

variable (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]

/-- Pushing a scaled with-density through a measurable equivalence.  The density on the
target is precomposed with the equivalence on the source. -/
private theorem withDensity_comp_map_measurableEquiv_coordinate
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (e : α ≃ᵐ β) (g : β → ℝ≥0∞) :
    (μ.withDensity (fun x => g (e x))).map e =
      (μ.map e).withDensity g := by
  ext s hs
  rw [MeasurableEquiv.map_apply, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs, e.restrict_map, MeasureTheory.lintegral_map_equiv]

/-- The interacting lattice measure pushed to coordinates is the explicitly normalized
Lebesgue measure with Gaussian density times the coordinate Wick Boltzmann factor. -/
theorem interactingLatticeMeasureAsym_evalMapAsym_pushforward_eq_coordinateDensity
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    (interactingLatticeMeasureAsym Nt Ns P a mass ha hmass).map (evalMapAsym Nt Ns) =
      ((ENNReal.ofReal (partitionFunctionAsym Nt Ns P a mass ha hmass))⁻¹ *
        (gaussianDensityNormConstAsym Nt Ns a mass)⁻¹) •
        (volume.withDensity
          (fun φ => ENNReal.ofReal
            (gaussianDensityAsym Nt Ns a mass φ *
              Real.exp (-(a ^ 2 * ∑ x : AsymLatticeSites Nt Ns,
                wickPolynomial P (wickConstantAsym Nt Ns a mass) (φ x)))))) := by
  classical
  let g : AsymLatticeField Nt Ns → ℝ≥0∞ := fun φ =>
    ENNReal.ofReal (Real.exp (-(a ^ 2 * ∑ x : AsymLatticeSites Nt Ns,
      wickPolynomial P (wickConstantAsym Nt Ns a mass) (φ x))))
  have hwick_cont :
      Continuous (fun y : ℝ => wickPolynomial P (wickConstantAsym Nt Ns a mass) y) :=
    (wickPolynomial_continuous₂ P).comp (continuous_const.prodMk continuous_id)
  have hg_meas : Measurable g := by
    refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_)
    exact (measurable_const.mul
      (Finset.measurable_sum _ (fun x _ =>
        hwick_cont.measurable.comp (measurable_pi_apply x)))).neg
  have hboltz :
      (fun ω => ENNReal.ofReal (boltzmannWeightAsym Nt Ns P a mass ω)) =
        fun ω => g (evalMapAsym Nt Ns ω) := by
    funext ω
    rfl

  have he : ⇑(evalMapAsymMeasurableEquiv Nt Ns) = evalMapAsym Nt Ns := rfl
  rw [interactingLatticeMeasureAsym, Measure.map_smul, hboltz, ← he,
    withDensity_comp_map_measurableEquiv_coordinate]
  rw [he]

  have hfree :
      (latticeGaussianMeasureAsym Nt Ns a mass ha hmass).map (evalMapAsym Nt Ns) =
        (gaussianDensityNormConstAsym Nt Ns a mass)⁻¹ •
          volume.withDensity (gaussianDensityWeightAsym Nt Ns a mass) := by
    show (GaussianField.measure (latticeCovarianceAsymGJ Nt Ns a mass ha hmass)).map
        (evalMapAsym Nt Ns) = _
    rw [show (GaussianField.measure (latticeCovarianceAsymGJ Nt Ns a mass ha hmass)).map
          (evalMapAsym Nt Ns) =
          latticeGaussianFieldLawAsym Nt Ns a mass ha hmass from rfl,
      latticeGaussianFieldLawAsym_eq_normalizedQuadraticGaussianMeasure,
      ← normalizedGaussianDensityMeasureAsym_eq_normalizedQuadraticGaussianMeasure]
    rfl
  have hgw : Measurable (gaussianDensityWeightAsym Nt Ns a mass) :=
    (GaussianField.gaussianDensityAsym_measurable Nt Ns a mass).ennreal_ofReal
  rw [hfree, withDensity_smul_measure, ← withDensity_mul _ hgw hg_meas]
  rw [smul_smul]
  congr 1
  apply withDensity_congr_ae
  filter_upwards with φ
  show (gaussianDensityWeightAsym Nt Ns a mass φ) * g φ =
    ENNReal.ofReal
      (gaussianDensityAsym Nt Ns a mass φ *
        Real.exp (-(a ^ 2 * ∑ x : AsymLatticeSites Nt Ns,
          wickPolynomial P (wickConstantAsym Nt Ns a mass) (φ x))))
  simp only [g]
  show ENNReal.ofReal (gaussianDensityAsym Nt Ns a mass φ) *
      ENNReal.ofReal (Real.exp (-(a ^ 2 * ∑ x : AsymLatticeSites Nt Ns,
        wickPolynomial P (wickConstantAsym Nt Ns a mass) (φ x)))) =
    ENNReal.ofReal
      (gaussianDensityAsym Nt Ns a mass φ *
        Real.exp (-(a ^ 2 * ∑ x : AsymLatticeSites Nt Ns,
          wickPolynomial P (wickConstantAsym Nt Ns a mass) (φ x))))
  rw [← ENNReal.ofReal_mul (gaussianDensityAsym_nonneg Nt Ns a mass φ)]

end Pphi2

end
