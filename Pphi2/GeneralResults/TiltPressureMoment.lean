/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/

import Pphi2.GeneralResults.WeakLimitMoment

/-!
# A finite exponential bound controls a normalized tilted moment

This file contains the elementary measure-theoretic adapter used when a
source estimate is available at strength two.  The proof is independent of
the lattice and of the particular interaction.  A nonnegative source
exponent `F` with an integrable `exp (2 * F)` has an integrable first moment
under the normalized tilt by `F`; the denominator of the tilt is at least
one because the base measure is a probability measure.
-/

noncomputable section

namespace Pphi2

open MeasureTheory

/-!
The abstract adapter is stated with a separate bound `B`.  Taking
`B = Real.exp C` gives the log-bound form used by source-pressure arguments.
-/

/--
An integrable exponential at source strength two controls the first moment
under the normalized exponential tilt at source strength one.

The hypotheses `hF_nonneg` and `hF_meas` are pointwise/measurable versions of
the source-exponent properties needed by the density formula.  The conclusion
is useful with `F = X^n / n` for an even power.
-/
theorem integrable_tilted_first_moment_le_of_exp_two
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (F : α → ℝ) (B : ℝ)
    (hF_meas : Measurable F)
    (hF_nonneg : ∀ x, 0 ≤ F x)
    (h_exp2 : Integrable (fun x => Real.exp (2 * F x)) μ)
    (h_exp2_bound : (∫ x, Real.exp (2 * F x) ∂μ) ≤ B) :
    Integrable F (μ.tilted F) ∧
      (∫ x, F x ∂(μ.tilted F)) ≤ B := by
  have h_exp1 : Integrable (fun x => Real.exp (F x)) μ := by
    refine Integrable.mono'
      (g := fun x => Real.exp (2 * F x)) h_exp2 ?_ ?_
    · exact hF_meas.exp.aestronglyMeasurable
    · filter_upwards [] with x
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      apply Real.exp_le_exp.mpr
      linarith [hF_nonneg x]

  have hF_tilt : Integrable F (μ.tilted F) := by
    rw [integrable_tilted_iff h_exp1 F]
    refine Integrable.mono'
      (g := fun x => Real.exp (2 * F x)) h_exp2 ?_ ?_
    · simpa only [smul_eq_mul] using
        (hF_meas.exp.mul hF_meas).aestronglyMeasurable
    · filter_upwards [] with x
      have hF_le_exp : F x ≤ Real.exp (F x) := by
        have h := Real.add_one_le_exp (F x)
        linarith
      calc
        ‖Real.exp (F x) • F x‖ = Real.exp (F x) * F x := by
          rw [smul_eq_mul, Real.norm_of_nonneg]
          exact mul_nonneg (Real.exp_pos _).le (hF_nonneg x)
        _ ≤ Real.exp (F x) * Real.exp (F x) :=
          mul_le_mul_of_nonneg_left hF_le_exp (Real.exp_pos _).le
        _ = Real.exp (2 * F x) := by
          rw [← Real.exp_add]
          ring

  have hZ_pos : 0 < ∫ x, Real.exp (F x) ∂μ := integral_exp_pos h_exp1
  have hZ_one : (1 : ℝ) ≤ ∫ x, Real.exp (F x) ∂μ := by
    calc
      (1 : ℝ) = ∫ _ : α, (1 : ℝ) ∂μ := by simp
      _ ≤ ∫ x, Real.exp (F x) ∂μ := by
        apply integral_mono (integrable_const 1) h_exp1
        exact fun x => Real.one_le_exp (hF_nonneg x)

  have h_source_nonneg :
      0 ≤ᵐ[μ] fun x =>
        (Real.exp (F x) / (∫ y, Real.exp (F y) ∂μ)) * F x :=
    ae_of_all _ (fun x =>
      mul_nonneg
        (div_nonneg (Real.exp_pos _).le hZ_pos.le)
        (hF_nonneg x))

  have h_source_le :
      (fun x =>
        (Real.exp (F x) / (∫ y, Real.exp (F y) ∂μ)) * F x) ≤ᵐ[μ]
      (fun x => Real.exp (2 * F x)) := by
    filter_upwards [] with x
    have h_exp_mul :
        Real.exp (F x) / (∫ y, Real.exp (F y) ∂μ) ≤ Real.exp (F x) := by
      apply (div_le_iff₀ hZ_pos).2
      simpa using
        (mul_le_mul_of_nonneg_left hZ_one (Real.exp_pos (F x)).le)
    have h_first :
        (Real.exp (F x) / (∫ y, Real.exp (F y) ∂μ)) * F x ≤
          Real.exp (F x) * F x := by
      exact mul_le_mul_of_nonneg_right h_exp_mul (hF_nonneg x)
    have h_second :
        Real.exp (F x) * F x ≤ Real.exp (2 * F x) := by
      calc
        Real.exp (F x) * F x ≤ Real.exp (F x) * Real.exp (F x) := by
          exact mul_le_mul_of_nonneg_left
            (by
              have h := Real.add_one_le_exp (F x)
              linarith)
            (Real.exp_pos _).le
        _ = Real.exp (2 * F x) := by
          rw [← Real.exp_add]
          ring
    exact h_first.trans h_second

  have h_source_integral_le :
      (∫ x, (Real.exp (F x) /
        (∫ y, Real.exp (F y) ∂μ)) * F x ∂μ) ≤ B := by
    calc
      (∫ x, (Real.exp (F x) /
          (∫ y, Real.exp (F y) ∂μ)) * F x ∂μ) ≤
          ∫ x, Real.exp (2 * F x) ∂μ :=
        integral_mono_of_nonneg h_source_nonneg h_exp2 h_source_le
      _ ≤ B := h_exp2_bound

  have h_tilt_integral_eq :
      (∫ x, F x ∂(μ.tilted F)) =
        ∫ x, (Real.exp (F x) /
          (∫ y, Real.exp (F y) ∂μ)) * F x ∂μ := by
    rw [integral_tilted]
    congr 1

  refine ⟨hF_tilt, ?_⟩
  rw [h_tilt_integral_eq]
  exact h_source_integral_le

/--
Sharp log-pressure form of `integrable_tilted_first_moment_le_of_exp_two`.

Jensen applied to `exp` under the tilted probability measure gives
`exp (∫ F dμ_F) ≤ Z₂ / Z₁`, where `Zᵢ = ∫ exp (i F) dμ`.  Since `F` is
nonnegative and `μ` is a probability measure, `Z₁ ≥ 1`; hence
`Z₂ ≤ exp C` implies `∫ F dμ_F ≤ C`.
-/
theorem integrable_tilted_first_moment_le_of_log_exp_two
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (F : α → ℝ) (C : ℝ)
    (hF_meas : Measurable F)
    (hF_nonneg : ∀ x, 0 ≤ F x)
    (h_exp2 : Integrable (fun x => Real.exp (2 * F x)) μ)
    (h_exp2_bound :
      (∫ x, Real.exp (2 * F x) ∂μ) ≤ Real.exp C) :
    Integrable F (μ.tilted F) ∧
      (∫ x, F x ∂(μ.tilted F)) ≤ C := by
  have h_exp1 : Integrable (fun x => Real.exp (F x)) μ := by
    refine Integrable.mono'
      (g := fun x => Real.exp (2 * F x)) h_exp2 ?_ ?_
    · exact hF_meas.exp.aestronglyMeasurable
    · filter_upwards [] with x
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      apply Real.exp_le_exp.mpr
      linarith [hF_nonneg x]

  have h_coarse := integrable_tilted_first_moment_le_of_exp_two μ F
    (Real.exp C) hF_meas hF_nonneg h_exp2 h_exp2_bound
  have hF_tilt : Integrable F (μ.tilted F) := h_coarse.1

  let ν : Measure α := μ.tilted F
  letI : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact isProbabilityMeasure_tilted h_exp1

  have h_exp_F_tilt : Integrable (fun x => Real.exp (F x)) ν := by
    rw [show ν = μ.tilted F by rfl]
    rw [integrable_tilted_iff h_exp1]
    convert h_exp2 using 1
    ext x
    simp [smul_eq_mul, ← Real.exp_add]
    ring

  have hF_tilt' : Integrable F ν := by
    simpa [ν] using hF_tilt

  have h_jensen :
      Real.exp (∫ x, F x ∂ν) ≤ ∫ x, Real.exp (F x) ∂ν := by
    have h_conv := convexOn_exp
    have h_cont := Real.continuous_exp.continuousOn (s := Set.univ)
    have h_closed := isClosed_univ (X := ℝ)
    have h_mem : ∀ᵐ x ∂ν, F x ∈ Set.univ :=
      ae_of_all _ (fun _ => Set.mem_univ _)
    exact h_conv.map_integral_le h_cont h_closed h_mem
      hF_tilt' h_exp_F_tilt

  have h_ratio :
      (∫ x, Real.exp (F x) ∂ν) =
        (∫ x, Real.exp (2 * F x) ∂μ) /
          (∫ x, Real.exp (F x) ∂μ) := by
    have h_ratio' := integral_exp_tilted (μ := μ) F F
    have hFF :
        (fun x => Real.exp ((F + F) x)) =
          (fun x => Real.exp (2 * F x)) := by
      funext x
      congr 1
      simp only [Pi.add_apply]
      ring
    dsimp [ν]
    calc
      (∫ x, Real.exp (F x) ∂(μ.tilted F)) =
          (∫ x, Real.exp ((F + F) x) ∂μ) /
            (∫ x, Real.exp (F x) ∂μ) := h_ratio'
      _ = (∫ x, Real.exp (2 * F x) ∂μ) /
            (∫ x, Real.exp (F x) ∂μ) := by rw [hFF]

  have hZ1_pos : 0 < ∫ x, Real.exp (F x) ∂μ := integral_exp_pos h_exp1
  have hZ1_one : (1 : ℝ) ≤ ∫ x, Real.exp (F x) ∂μ := by
    calc
      (1 : ℝ) = ∫ _ : α, (1 : ℝ) ∂μ := by simp
      _ ≤ ∫ x, Real.exp (F x) ∂μ := by
        apply integral_mono (integrable_const 1) h_exp1
        exact fun x => Real.one_le_exp (hF_nonneg x)

  have h_ratio_le :
      (∫ x, Real.exp (2 * F x) ∂μ) /
          (∫ x, Real.exp (F x) ∂μ) ≤ Real.exp C := by
    apply (div_le_iff₀ hZ1_pos).2
    exact h_exp2_bound.trans
      (by
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hZ1_one (Real.exp_pos C).le))

  have h_exp_integral_le : Real.exp (∫ x, F x ∂ν) ≤ Real.exp C := by
    calc
      Real.exp (∫ x, F x ∂ν) ≤ ∫ x, Real.exp (F x) ∂ν := h_jensen
      _ = (∫ x, Real.exp (2 * F x) ∂μ) /
          (∫ x, Real.exp (F x) ∂μ) := h_ratio
      _ ≤ Real.exp C := h_ratio_le

  refine ⟨?_, ?_⟩
  · simpa [ν] using hF_tilt
  · have h_le : (∫ x, F x ∂ν) ≤ C :=
      (Real.exp_le_exp).mp h_exp_integral_le
    simpa [ν] using h_le

/-- Sharp log-pressure specialization for an even-power source. -/
theorem integrable_tilted_pow_le_of_log_exp_two
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (n : ℕ) (hn_pos : 0 < n) (X : α → ℝ) (C : ℝ)
    (hX_meas : Measurable X)
    (hX_pow_nonneg : ∀ x, 0 ≤ (X x) ^ n)
    (h_exp2 : Integrable
      (fun x => Real.exp (2 * ((X x) ^ n / (n : ℝ)))) μ)
    (h_exp2_bound :
      (∫ x, Real.exp (2 * ((X x) ^ n / (n : ℝ))) ∂μ) ≤ Real.exp C) :
    Integrable (fun x => (X x) ^ n)
        (μ.tilted (fun x => (X x) ^ n / (n : ℝ))) ∧
      (∫ x, (X x) ^ n ∂(μ.tilted
        (fun x => (X x) ^ n / (n : ℝ)))) ≤ (n : ℝ) * C := by
  have hnR_pos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn_pos
  let F : α → ℝ := fun x => (X x) ^ n / (n : ℝ)
  have hF_meas : Measurable F := by
    dsimp [F]
    exact (hX_meas.pow_const n).div measurable_const
  have hF_nonneg : ∀ x, 0 ≤ F x := by
    intro x
    dsimp [F]
    exact div_nonneg (hX_pow_nonneg x) hnR_pos.le
  have hcore :=
    integrable_tilted_first_moment_le_of_log_exp_two μ F C
      hF_meas hF_nonneg (by simpa [F] using h_exp2)
      (by simpa [F] using h_exp2_bound)
  have hpow_int :
      Integrable (fun x => (X x) ^ n) (μ.tilted F) := by
    have hscaled := hcore.1.const_mul (n : ℝ)
    convert hscaled using 1
    funext x
    dsimp [F]
    field_simp [hnR_pos.ne'] <;> ring

  have hpow_integral_eq :
      (∫ x, (X x) ^ n ∂(μ.tilted F)) =
        (n : ℝ) * (∫ x, F x ∂(μ.tilted F)) := by
    calc
      (∫ x, (X x) ^ n ∂(μ.tilted F)) =
          ∫ x, (n : ℝ) * F x ∂(μ.tilted F) := by
            congr 1
            funext x
            dsimp [F]
            field_simp [hnR_pos.ne'] <;> ring
      _ = (n : ℝ) * (∫ x, F x ∂(μ.tilted F)) := by
        rw [integral_const_mul]

  refine ⟨?_, ?_⟩
  · simpa [F] using hpow_int
  · rw [hpow_integral_eq]
    exact mul_le_mul_of_nonneg_left hcore.2 hnR_pos.le

end Pphi2
