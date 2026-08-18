/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Source-tilt entropy adapter

This file isolates the elementary last step in a local `P(Φ)₂` source
estimate.  The finite analytic producer supplies integrability of the source
exponential and a moment bound under its normalized exponential tilt.  The
entropy inequality from `GeneralResults/WeakLimitMoment` then gives the
literal constant `2` once the tilted moment is at most `n * log 2`.
-/

import Pphi2.GeneralResults.WeakLimitMoment

noncomputable section

namespace Pphi2

open MeasureTheory

/--
The source-tilted moment estimate used by the local degree-`n` producer.

Let `X` be the source observable and
`F = X^n / n`.  If `exp F` is integrable for the original probability
measure, and `X^n` is integrable for the normalized tilt by `F`, then the
tilted moment bound `∫ X^n ≤ n * log 2` implies
`∫ exp (X^n / n) ≤ 2`.

The separate `Integrable X^n` hypothesis is intentional.  It is the finite
source-tilted energy conclusion supplied by the analytic producer, while the
integrability of `exp F` is the finite coercivity/integrability conclusion.
-/
theorem integral_exp_pow_div_nat_le_two_of_tilted_moment
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (n : ℕ) (hn_pos : 0 < n)
    (X : α → ℝ)
    (h_exp : Integrable
      (fun x => Real.exp ((X x) ^ n / (n : ℝ))) μ)
    (h_moment : Integrable
      (fun x => (X x) ^ n)
      (μ.tilted (fun x => (X x) ^ n / (n : ℝ))))
    (h_moment_bound :
      (∫ x, (X x) ^ n ∂(μ.tilted (fun x => (X x) ^ n / (n : ℝ)))) ≤
        (n : ℝ) * Real.log 2) :
    (∫ x, Real.exp ((X x) ^ n / (n : ℝ)) ∂μ) ≤ 2 := by
  have hnR_pos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn_pos
  have hF_tilt : Integrable
      (fun x => (X x) ^ n / (n : ℝ))
      (μ.tilted (fun x => (X x) ^ n / (n : ℝ))) := by
    exact h_moment.div_const (n : ℝ)
  have h_entropy := GaussianField.integral_exp_le_exp_integral_tilted
    μ (fun x => (X x) ^ n / (n : ℝ)) h_exp hF_tilt
  have hF_bound :
      (∫ x, (X x) ^ n / (n : ℝ)
        ∂(μ.tilted (fun x => (X x) ^ n / (n : ℝ)))) ≤ Real.log 2 := by
    calc
      (∫ x, (X x) ^ n / (n : ℝ)
          ∂(μ.tilted (fun x => (X x) ^ n / (n : ℝ)))) =
          (∫ x, (X x) ^ n
            ∂(μ.tilted (fun x => (X x) ^ n / (n : ℝ)))) / (n : ℝ) := by
        rw [integral_div]
      _ ≤ Real.log 2 := by
        apply (div_le_iff₀ hnR_pos).2
        simpa [mul_comm] using h_moment_bound
  calc
    (∫ x, Real.exp ((X x) ^ n / (n : ℝ)) ∂μ) ≤
        Real.exp (∫ x, (X x) ^ n / (n : ℝ)
          ∂(μ.tilted (fun x => (X x) ^ n / (n : ℝ)))) := h_entropy
    _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hF_bound
    _ = 2 := by
      rw [Real.exp_log]
      norm_num

end Pphi2

