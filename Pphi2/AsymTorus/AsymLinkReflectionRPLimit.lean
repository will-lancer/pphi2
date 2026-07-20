/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Codex
-/

import Pphi2.GeneralResults.FunctionalAnalysis

/-!
# Link-reflection positivity in the UV limit

Analytic estimates for passing the finite-spacing link-reflection matrix
inequality to cylinder time reflection.
-/

open Filter GaussianField MeasureTheory

namespace Pphi2

/-- A scaled exponential-moment bound controls the absolute first moment by
the square root of its variance parameter.

The rescaling is essential: applying the exponential bound only at `t = 1`
would leave a nonzero constant when `sigmaSq` tends to zero. -/
theorem absMoment_le_of_uniform_expMoment
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (μ : Measure (Configuration E)) (h : E) (K C sigmaSq : ℝ)
    (hK : 0 < K) (hC : 0 < C) (hsigmaSq : 0 ≤ sigmaSq)
    (hExp : ∀ t : ℝ,
      Integrable (fun ω : Configuration E => Real.exp |ω (t • h)|) μ ∧
      ∫ ω : Configuration E, Real.exp |ω (t • h)| ∂μ ≤
        K * Real.exp (C * t ^ 2 * sigmaSq)) :
    Integrable (fun ω : Configuration E => |ω h|) μ ∧
    ∫ ω : Configuration E, |ω h| ∂μ ≤
      K * Real.exp 1 * Real.sqrt C * Real.sqrt sigmaSq := by
  have habs_meas : AEStronglyMeasurable
      (fun ω : Configuration E => |ω h|) μ :=
    (configuration_eval_measurable h).abs.aestronglyMeasurable
  have habs_int : Integrable (fun ω : Configuration E => |ω h|) μ := by
    refine (hExp 1).1.mono' habs_meas (ae_of_all _ fun ω => ?_)
    simpa [Real.norm_eq_abs, abs_of_nonneg] using
      ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp |ω h|))
  refine ⟨habs_int, ?_⟩
  have hscaled_abs_int : ∀ t : ℝ,
      Integrable (fun ω : Configuration E => |ω (t • h)|) μ := by
    intro t
    have hmeas : AEStronglyMeasurable
        (fun ω : Configuration E => |ω (t • h)|) μ :=
      (configuration_eval_measurable (t • h)).abs.aestronglyMeasurable
    refine (hExp t).1.mono' hmeas (ae_of_all _ fun ω => ?_)
    simpa [Real.norm_eq_abs, abs_of_nonneg] using
      ((le_add_of_nonneg_right zero_le_one).trans
        (Real.add_one_le_exp |ω (t • h)|))
  have hscaled_abs : ∀ t : ℝ,
      ∫ ω : Configuration E, |ω (t • h)| ∂μ =
        |t| * ∫ ω : Configuration E, |ω h| ∂μ := by
    intro t
    simp_rw [map_smul, smul_eq_mul, abs_mul]
    exact integral_const_mul |t| (fun ω : Configuration E => |ω h|)
  have hscaled_bound : ∀ t : ℝ,
      ∫ ω : Configuration E, |ω (t • h)| ∂μ ≤
        K * Real.exp (C * t ^ 2 * sigmaSq) := by
    intro t
    exact (integral_mono (hscaled_abs_int t) (hExp t).1
      (fun ω => (le_add_of_nonneg_right zero_le_one).trans
        (Real.add_one_le_exp _))).trans (hExp t).2
  rcases eq_or_lt_of_le hsigmaSq with hsigmaSq_zero | hsigmaSq_pos
  · subst sigmaSq
    have hmoment_nonneg : 0 ≤ ∫ ω : Configuration E, |ω h| ∂μ :=
      integral_nonneg fun _ => abs_nonneg _
    have hmoment_zero : ∫ ω : Configuration E, |ω h| ∂μ = 0 := by
      apply le_antisymm
      · by_contra hnot
        have hmoment_pos : 0 < ∫ ω : Configuration E, |ω h| ∂μ :=
          lt_of_not_ge hnot
        let t : ℝ := K / (∫ ω : Configuration E, |ω h| ∂μ) + 1
        have ht_pos : 0 < t := by
          dsimp [t]
          positivity
        have hle : t * (∫ ω : Configuration E, |ω h| ∂μ) ≤ K := by
          calc
            t * (∫ ω : Configuration E, |ω h| ∂μ) =
                ∫ ω : Configuration E, |ω (t • h)| ∂μ := by
              rw [hscaled_abs t, abs_of_pos ht_pos]
            _ ≤ K * Real.exp (C * t ^ 2 * 0) := hscaled_bound t
            _ = K := by simp
        have hlt : K < t * (∫ ω : Configuration E, |ω h| ∂μ) := by
          dsimp [t]
          field_simp [ne_of_gt hmoment_pos]
          linarith
        exact (not_lt_of_ge hle) hlt
      · exact hmoment_nonneg
    simp [hmoment_zero]
  · have hCsigmaSq_pos : 0 < C * sigmaSq := mul_pos hC hsigmaSq_pos
    have hsqrt_CsigmaSq_pos : 0 < Real.sqrt (C * sigmaSq) :=
      Real.sqrt_pos.2 hCsigmaSq_pos
    let t : ℝ := (Real.sqrt (C * sigmaSq))⁻¹
    have ht_pos : 0 < t := inv_pos.mpr hsqrt_CsigmaSq_pos
    have ht_sq_mul : t ^ 2 * (C * sigmaSq) = 1 := by
      dsimp [t]
      rw [inv_pow, Real.sq_sqrt hCsigmaSq_pos.le]
      exact inv_mul_cancel₀ (ne_of_gt hCsigmaSq_pos)
    have hdiv_bound :
        (∫ ω : Configuration E, |ω h| ∂μ) / Real.sqrt (C * sigmaSq) ≤
          K * Real.exp 1 := by
      calc
        (∫ ω : Configuration E, |ω h| ∂μ) / Real.sqrt (C * sigmaSq) =
            ∫ ω : Configuration E, |ω (t • h)| ∂μ := by
          rw [hscaled_abs t, abs_of_pos ht_pos]
          simp [t, div_eq_mul_inv, mul_comm]
        _ ≤ K * Real.exp (C * t ^ 2 * sigmaSq) := hscaled_bound t
        _ = K * Real.exp 1 := by
          congr 2
          calc
            C * t ^ 2 * sigmaSq = t ^ 2 * (C * sigmaSq) := by ring
            _ = 1 := ht_sq_mul
    have hbound := (div_le_iff₀ hsqrt_CsigmaSq_pos).mp hdiv_bound
    calc
      ∫ ω : Configuration E, |ω h| ∂μ ≤
          K * Real.exp 1 * Real.sqrt (C * sigmaSq) := hbound
      _ = K * Real.exp 1 * Real.sqrt C * Real.sqrt sigmaSq := by
        rw [Real.sqrt_mul hC.le]
        ring

end Pphi2
