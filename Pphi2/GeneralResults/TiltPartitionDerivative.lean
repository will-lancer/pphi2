/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/

import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Measure.Tilted

/-!
# Differentiating an exponentially tilted partition function

This file gives the elementary differentiation step needed by source-strength
interpolation.  The domination hypothesis is stated at the point where it is
used: an integrable local bound for `|F| exp ((|κ| + ε) |F|)` controls the
derivative in a ball of radius `ε` around `κ`.

The second theorem rewrites the logarithmic derivative as the first moment of
`F` under the normalized tilted measure.  The source-dependent analytic or
probabilistic estimate remains an input to these purely measure-theoretic
lemmas.
-/

noncomputable section

namespace Pphi2

open MeasureTheory Filter Metric Set

/--
Differentiate an exponential partition integral under an explicit local
domination hypothesis.

The bound is uniform for the parameter in `ball κ ε`.  It is deliberately
given as an integrable function rather than inferred from a stronger moment
assumption, so this theorem can be used with whichever source estimate is
available.
-/
theorem hasDerivAt_integral_exp_mul_of_local_dom
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (κ ε : ℝ) (hε : 0 < ε)
    (hf_meas : Measurable f)
    (h_exp : Integrable (fun x => Real.exp (κ * f x)) μ)
    (h_bound :
      Integrable
        (fun x => Real.exp ((|κ| + ε) * |f x|) * |f x|) μ) :
    HasDerivAt
      (fun t => ∫ x, Real.exp (t * f x) ∂μ)
      (∫ x, f x * Real.exp (κ * f x) ∂μ) κ := by
  let G : ℝ → α → ℝ := fun t x => Real.exp (t * f x)
  let G' : ℝ → α → ℝ := fun t x => f x * Real.exp (t * f x)
  have hG_meas : ∀ᶠ t in 𝓝 κ, AEStronglyMeasurable (G t) μ := by
    exact Filter.Eventually.of_forall fun t => by
      simpa [G] using (hf_meas.const_mul t).exp.aestronglyMeasurable
  have hG'_meas : AEStronglyMeasurable (G' κ) μ := by
    simpa [G'] using
      (hf_meas.mul (hf_meas.const_mul κ).exp).aestronglyMeasurable
  have hG_int : Integrable (G κ) μ := by
    simpa [G] using h_exp
  have h_bound' :
      ∀ᵐ x ∂μ, ∀ t ∈ ball κ ε,
        ‖G' t x‖ ≤ Real.exp ((|κ| + ε) * |f x|) * |f x| := by
    refine Filter.Eventually.of_forall fun x t ht => ?_
    have ht_dist : |t - κ| < ε := by
      simpa [mem_ball, Real.dist_eq] using ht
    have ht_abs : |t| ≤ |κ| + ε := by
      calc
        |t| = |(t - κ) + κ| := by congr 1 <;> ring
        _ ≤ |t - κ| + |κ| := abs_add _ _
        _ ≤ ε + |κ| := add_le_add_right (le_of_lt ht_dist) _
        _ = |κ| + ε := by ring
    have harg : t * f x ≤ (|κ| + ε) * |f x| := by
      calc
        t * f x ≤ |t * f x| := le_abs_self _
        _ = |t| * |f x| := abs_mul _ _
        _ ≤ (|κ| + ε) * |f x| :=
          mul_le_mul_of_nonneg_right ht_abs (abs_nonneg _)
    calc
      ‖G' t x‖ = |f x * Real.exp (t * f x)| := by
        simp only [G', Real.norm_eq_abs]
      _ = |f x| * Real.exp (t * f x) := by
        rw [abs_mul, abs_of_nonneg (Real.exp_pos _).le]
      _ ≤ |f x| * Real.exp ((|κ| + ε) * |f x|) := by
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (abs_nonneg _)
      _ = Real.exp ((|κ| + ε) * |f x|) * |f x| := by
        exact mul_comm _ _
  have h_diff :
      ∀ᵐ x ∂μ, ∀ t ∈ ball κ ε, HasDerivAt (G · x) (G' t x) t := by
    refine Filter.Eventually.of_forall fun x t ht => ?_
    have hlin : HasDerivAt (fun s : ℝ => s * f x) (f x) t := by
      simpa using ((hasDerivAt_id t).mul_const (f x))
    simpa [G, G', mul_comm] using hlin.exp
  have h :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := μ) (F := G) (F' := G') (x₀ := κ) (s := ball κ ε)
      (ball_mem_nhds κ hε) hG_meas hG_int hG'_meas h_bound' h_bound h_diff
  simpa [G, G'] using h.2

/--
The logarithmic derivative of an exponential partition integral is the
normalized first moment under the corresponding tilted measure.

`hZ_pos` records the nonzero partition function needed by the logarithm and
also makes the positivity requirement explicit for arbitrary base measures.
-/
theorem hasDerivAt_log_integral_exp_mul_of_local_dom
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (κ ε : ℝ) (hε : 0 < ε)
    (hf_meas : Measurable f)
    (h_exp : Integrable (fun x => Real.exp (κ * f x)) μ)
    (h_bound :
      Integrable
        (fun x => Real.exp ((|κ| + ε) * |f x|) * |f x|) μ)
    (hZ_pos : 0 < ∫ x, Real.exp (κ * f x) ∂μ) :
    HasDerivAt
      (fun t => Real.log (∫ x, Real.exp (t * f x) ∂μ))
      (∫ x, f x ∂(μ.tilted (fun x => κ * f x))) κ := by
  have hZ_ne : (∫ x, Real.exp (κ * f x) ∂μ) ≠ 0 := ne_of_gt hZ_pos
  have hpart := hasDerivAt_integral_exp_mul_of_local_dom μ f κ ε hε hf_meas
    h_exp h_bound
  have hlog := hpart.log hZ_ne
  have htilt :
      (∫ x, f x ∂(μ.tilted (fun x => κ * f x))) =
    (∫ x, f x * Real.exp (κ * f x) ∂μ) /
          (∫ x, Real.exp (κ * f x) ∂μ) := by
    rw [integral_tilted, ← integral_div]
    congr 1
    funext x
    simp only [smul_eq_mul]
    ring
  rw [htilt]
  exact hlog

end Pphi2
