/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Codex
-/

import Pphi2.AsymTorus.AsymLinkReflectionRP

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

/-- Bounded-continuous convergence on torus configurations gives
characteristic-functional convergence after cylinder pullback. -/
theorem cylinderPullbackMeasure_cexp_tendsto_of_tendsto_bc
    (Lt Ls : ℝ) [Fact (0 < Lt)] [Fact (0 < Ls)]
    (μseq : ℕ → Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    (hμseq_prob : ∀ k, IsProbabilityMeasure (μseq k))
    (hμ_prob : IsProbabilityMeasure μ)
    (hbc : ∀ (g : Configuration (AsymTorusTestFunction Lt Ls) → ℝ),
      Continuous g → (∃ B, ∀ x, |g x| ≤ B) →
      Tendsto (fun k => ∫ ω, g ω ∂(μseq k)) atTop (nhds (∫ ω, g ω ∂μ)))
    (f : CylinderTestFunction Ls) :
    Tendsto
      (fun k => ∫ ω, Complex.exp (Complex.I * ↑(ω f))
        ∂(cylinderPullbackMeasure Lt Ls (μseq k)))
      atTop
      (nhds (∫ ω, Complex.exp (Complex.I * ↑(ω f))
        ∂(cylinderPullbackMeasure Lt Ls μ))) := by
  let F : AsymTorusTestFunction Lt Ls := cylinderToTorusEmbed Lt Ls f
  have hcos : Tendsto
      (fun k => ∫ ω, Real.cos (ω F) ∂(μseq k))
      atTop (nhds (∫ ω, Real.cos (ω F) ∂μ)) :=
    hbc (fun ω => Real.cos (ω F))
      (Real.continuous_cos.comp (WeakDual.eval_continuous F))
      ⟨1, fun ω => Real.abs_cos_le_one (ω F)⟩
  have hsin : Tendsto
      (fun k => ∫ ω, Real.sin (ω F) ∂(μseq k))
      atTop (nhds (∫ ω, Real.sin (ω F) ∂μ)) :=
    hbc (fun ω => Real.sin (ω F))
      (Real.continuous_sin.comp (WeakDual.eval_continuous F))
      ⟨1, fun ω => Real.abs_sin_le_one (ω F)⟩
  have hre : Tendsto
      (fun k => (∫ ω, Complex.exp (Complex.I * ↑(ω F)) ∂(μseq k)).re)
      atTop (nhds ((∫ ω, Complex.exp (Complex.I * ↑(ω F)) ∂μ).re)) := by
    have hseq :
        (fun k => (∫ ω, Complex.exp (Complex.I * ↑(ω F)) ∂(μseq k)).re) =
          fun k => ∫ ω, Real.cos (ω F) ∂(μseq k) := by
      funext k
      letI := hμseq_prob k
      exact configuration_expIntegral_re_eq_integral_cos (μseq k) F
    have hlim : (∫ ω, Complex.exp (Complex.I * ↑(ω F)) ∂μ).re =
        ∫ ω, Real.cos (ω F) ∂μ := by
      letI := hμ_prob
      exact configuration_expIntegral_re_eq_integral_cos μ F
    rw [hseq, hlim]
    exact hcos
  have him : Tendsto
      (fun k => (∫ ω, Complex.exp (Complex.I * ↑(ω F)) ∂(μseq k)).im)
      atTop (nhds ((∫ ω, Complex.exp (Complex.I * ↑(ω F)) ∂μ).im)) := by
    have hseq :
        (fun k => (∫ ω, Complex.exp (Complex.I * ↑(ω F)) ∂(μseq k)).im) =
          fun k => ∫ ω, Real.sin (ω F) ∂(μseq k) := by
      funext k
      letI := hμseq_prob k
      exact configuration_expIntegral_im_eq_integral_sin (μseq k) F
    have hlim : (∫ ω, Complex.exp (Complex.I * ↑(ω F)) ∂μ).im =
        ∫ ω, Real.sin (ω F) ∂μ := by
      letI := hμ_prob
      exact configuration_expIntegral_im_eq_integral_sin μ F
    rw [hseq, hlim]
    exact hsin
  have htorus : Tendsto
      (fun k => ∫ ω, Complex.exp (Complex.I * ↑(ω F)) ∂(μseq k))
      atTop (nhds (∫ ω, Complex.exp (Complex.I * ↑(ω F)) ∂μ)) := by
    have hpair := hre.prodMk_nhds him
    have hcomplex := (Complex.equivRealProdCLM.symm.continuous.tendsto
      (((∫ ω, Complex.exp (Complex.I * ↑(ω F)) ∂μ).re),
       ((∫ ω, Complex.exp (Complex.I * ↑(ω F)) ∂μ).im))).comp hpair
    simpa [Complex.equivRealProdCLM_symm_apply, Complex.re_add_im] using hcomplex
  have hmap : ∀ ν : Measure (Configuration (AsymTorusTestFunction Lt Ls)),
      ∫ ω, Complex.exp (Complex.I * ↑(ω f))
          ∂(cylinderPullbackMeasure Lt Ls ν) =
        ∫ ω, Complex.exp (Complex.I * ↑(ω F)) ∂ν := by
    intro ν
    unfold cylinderPullbackMeasure
    have hmeas : Measurable (cylinderPullback Lt Ls) :=
      configuration_measurable_of_eval_measurable _
        (fun φ => configuration_eval_measurable _)
    have hsm : StronglyMeasurable
        (fun ω : Configuration (CylinderTestFunction Ls) =>
          Complex.exp (Complex.I * ↑(ω f))) :=
      (Complex.measurable_exp.comp (measurable_const.mul
        (Complex.measurable_ofReal.comp
          (configuration_eval_measurable f)))).stronglyMeasurable
    rw [integral_map_of_stronglyMeasurable
      hmeas hsm]
    simp [F, cylinderPullback_eval]
  simpa only [hmap] using htorus

/-- The characteristic integrand is pointwise Lipschitz in its real source. -/
theorem configuration_cexp_eval_dist_le_abs_eval_sub
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (f g : E) (ω : Configuration E) :
    configuration_cexp_eval_dist f g ω ≤ |ω (g - f)| := by
  change ‖Complex.exp (Complex.I * ↑(ω g)) -
    Complex.exp (Complex.I * ↑(ω f))‖ ≤ |ω (g - f)|
  have hfactor :
      Complex.exp (Complex.I * ↑(ω g)) - Complex.exp (Complex.I * ↑(ω f)) =
        Complex.exp (Complex.I * ↑(ω f)) *
          (Complex.exp (Complex.I * ↑(ω g - ω f)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
  rw [hfactor, norm_mul, mul_comm Complex.I (↑(ω f) : ℂ),
    Complex.norm_exp_ofReal_mul_I, one_mul,
    Complex.norm_exp_I_mul_ofReal_sub_one]
  calc
    ‖2 * Real.sin ((ω g - ω f) / 2)‖ =
        2 * |Real.sin ((ω g - ω f) / 2)| := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ 2 * |(ω g - ω f) / 2| :=
      mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by norm_num)
    _ = |ω g - ω f| := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      ring
    _ = |ω (g - f)| := by rw [map_sub]

/-- Joint weak-measure and link-reflection limit for one fixed cylinder RP
matrix. The finite matrices may use a moving link reflection, provided their
quadratic moment controls vanish on every test-function sequence tending to
zero. -/
theorem cylinderRPMatrixNonnegative_of_link_limit
    (Lt Ls : ℝ) [Fact (0 < Lt)] [Fact (0 < Ls)]
    (μseq : ℕ → Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    (hμseq_prob : ∀ k, IsProbabilityMeasure (μseq k))
    (hμ_prob : IsProbabilityMeasure μ)
    (hbc : ∀ (g : Configuration (AsymTorusTestFunction Lt Ls) → ℝ),
      Continuous g → (∃ B, ∀ x, |g x| ≤ B) →
      Tendsto (fun k => ∫ ω, g ω ∂(μseq k)) atTop (nhds (∫ ω, g ω ∂μ)))
    (a : ℕ → ℝ) (ha0 : Tendsto a atTop (nhds 0))
    (sigmaSq : ℕ → CylinderTestFunction Ls → ℝ)
    (K C : ℝ) (hK : 0 < K) (hC : 0 < C)
    (hsigmaSq_nonneg : ∀ k h, 0 ≤ sigmaSq k h)
    (hsigmaSq_smul : ∀ k t h, sigmaSq k (t • h) = t ^ 2 * sigmaSq k h)
    (hsigmaSq_zero : ∀ hseq : ℕ → CylinderTestFunction Ls,
      Tendsto hseq atTop (nhds 0) →
      Tendsto (fun k => sigmaSq k (hseq k)) atTop (nhds 0))
    (hExp : ∀ k h,
      Integrable (fun ω : Configuration (CylinderTestFunction Ls) =>
        Real.exp |ω h|) (cylinderPullbackMeasure Lt Ls (μseq k)) ∧
      ∫ ω : Configuration (CylinderTestFunction Ls), Real.exp |ω h|
          ∂(cylinderPullbackMeasure Lt Ls (μseq k)) ≤
        K * Real.exp (C * sigmaSq k h))
    (n : ℕ) (f : Fin n → ↥(cylinderPositiveTimeSubmodule Ls))
    (c : Fin n → ℂ)
    (hlink : ∀ k, CylinderLinkRPMatrixNonnegative Ls
      (cylinderPullbackMeasure Lt Ls (μseq k)) (a k) n f c) :
    CylinderRPMatrixNonnegative Ls (cylinderPullbackMeasure Lt Ls μ) n f c := by
  have hcf : ∀ g : CylinderTestFunction Ls,
      Tendsto
        (fun k => ∫ ω, Complex.exp (Complex.I * ↑(ω g))
          ∂(cylinderPullbackMeasure Lt Ls (μseq k)))
        atTop
        (nhds (∫ ω, Complex.exp (Complex.I * ↑(ω g))
          ∂(cylinderPullbackMeasure Lt Ls μ))) :=
    cylinderPullbackMeasure_cexp_tendsto_of_tendsto_bc
      Lt Ls μseq μ hμseq_prob hμ_prob hbc
  have hentry : ∀ i j : Fin n,
      Tendsto
        (fun k => ∫ ω, Complex.exp (Complex.I *
          ↑(ω ((f i : CylinderTestFunction Ls) -
            cylinderLinkReflection Ls (a k) (f j : CylinderTestFunction Ls))))
          ∂(cylinderPullbackMeasure Lt Ls (μseq k)))
        atTop
        (nhds (∫ ω, Complex.exp (Complex.I *
          ↑(ω ((f i : CylinderTestFunction Ls) -
            cylinderTimeReflection Ls (f j : CylinderTestFunction Ls))))
          ∂(cylinderPullbackMeasure Lt Ls μ))) := by
    intro i j
    let gtime : CylinderTestFunction Ls :=
      (f i : CylinderTestFunction Ls) -
        cylinderTimeReflection Ls (f j : CylinderTestFunction Ls)
    let glink : ℕ → CylinderTestFunction Ls := fun k =>
      (f i : CylinderTestFunction Ls) -
        cylinderLinkReflection Ls (a k) (f j : CylinderTestFunction Ls)
    let d : ℕ → CylinderTestFunction Ls := fun k =>
      cylinderTimeReflection Ls (f j : CylinderTestFunction Ls) -
        cylinderLinkReflection Ls (a k) (f j : CylinderTestFunction Ls)
    have href_tend : Tendsto
        (fun k => cylinderLinkReflection Ls (a k) (f j : CylinderTestFunction Ls))
        atTop (nhds (cylinderTimeReflection Ls (f j : CylinderTestFunction Ls))) :=
      (cylinderLinkReflection_tendsto_timeReflection
        (Ls := Ls) (f j : CylinderTestFunction Ls)).comp ha0
    have hd_tend : Tendsto d atTop (nhds 0) := by
      have hsub := Filter.Tendsto.const_sub
        (cylinderTimeReflection Ls (f j : CylinderTestFunction Ls)) href_tend
      simpa [d] using hsub
    have hsigma_tend : Tendsto (fun k => sigmaSq k (d k)) atTop (nhds 0) :=
      hsigmaSq_zero d hd_tend
    have hsqrt_tend : Tendsto (fun k => Real.sqrt (sigmaSq k (d k)))
        atTop (nhds 0) := by
      simpa using Real.continuous_sqrt.continuousAt.tendsto.comp hsigma_tend
    have hupper_tend : Tendsto
        (fun k => K * Real.exp 1 * Real.sqrt C * Real.sqrt (sigmaSq k (d k)))
        atTop (nhds 0) := by
      simpa [mul_assoc] using hsqrt_tend.const_mul (K * Real.exp 1 * Real.sqrt C)
    have hdiff : Tendsto
        (fun k =>
          (∫ ω, Complex.exp (Complex.I * ↑(ω (glink k)))
              ∂(cylinderPullbackMeasure Lt Ls (μseq k))) -
            ∫ ω, Complex.exp (Complex.I * ↑(ω gtime))
              ∂(cylinderPullbackMeasure Lt Ls (μseq k)))
        atTop (nhds 0) := by
      apply squeeze_zero_norm
      · intro k
        letI : IsProbabilityMeasure (μseq k) := hμseq_prob k
        haveI : IsProbabilityMeasure (cylinderPullbackMeasure Lt Ls (μseq k)) := by
          unfold cylinderPullbackMeasure
          have hmeas : Measurable (cylinderPullback Lt Ls) :=
            configuration_measurable_of_eval_measurable _
              (fun φ => configuration_eval_measurable _)
          exact Measure.isProbabilityMeasure_map
            hmeas.aemeasurable
        have hExp_scaled : ∀ t : ℝ,
            Integrable (fun ω : Configuration (CylinderTestFunction Ls) =>
              Real.exp |ω (t • d k)|) (cylinderPullbackMeasure Lt Ls (μseq k)) ∧
            ∫ ω : Configuration (CylinderTestFunction Ls), Real.exp |ω (t • d k)|
                ∂(cylinderPullbackMeasure Lt Ls (μseq k)) ≤
              K * Real.exp (C * t ^ 2 * sigmaSq k (d k)) := by
          intro t
          obtain ⟨hint, hle⟩ := hExp k (t • d k)
          refine ⟨hint, ?_⟩
          rw [hsigmaSq_smul k t (d k)] at hle
          simpa [mul_assoc] using hle
        obtain ⟨hd_int, hd_bound⟩ := absMoment_le_of_uniform_expMoment
          (cylinderPullbackMeasure Lt Ls (μseq k)) (d k) K C
          (sigmaSq k (d k)) hK hC (hsigmaSq_nonneg k (d k)) hExp_scaled
        have hdist_int : Integrable
            (configuration_cexp_eval_dist gtime (glink k))
            (cylinderPullbackMeasure Lt Ls (μseq k)) := by
          have hglink_int := configuration_cexp_eval_integrable
            (cylinderPullbackMeasure Lt Ls (μseq k)) (glink k)
          have hgtime_int := configuration_cexp_eval_integrable
            (cylinderPullbackMeasure Lt Ls (μseq k)) gtime
          simpa [configuration_cexp_eval_dist,
            configuration_cexp_eval_sub_integrand] using
              (hglink_int.sub hgtime_int).norm
        calc
          ‖(∫ ω, Complex.exp (Complex.I * ↑(ω (glink k)))
                ∂(cylinderPullbackMeasure Lt Ls (μseq k))) -
              ∫ ω, Complex.exp (Complex.I * ↑(ω gtime))
                ∂(cylinderPullbackMeasure Lt Ls (μseq k))‖
              ≤ ∫ ω, configuration_cexp_eval_dist gtime (glink k) ω
                  ∂(cylinderPullbackMeasure Lt Ls (μseq k)) :=
            norm_configuration_expIntegral_sub_le_integral_cexp_eval_dist
              (cylinderPullbackMeasure Lt Ls (μseq k)) gtime (glink k)
          _ ≤ ∫ ω, |ω (d k)| ∂(cylinderPullbackMeasure Lt Ls (μseq k)) := by
            apply integral_mono hdist_int hd_int
            intro ω
            simpa [gtime, glink, d] using
              configuration_cexp_eval_dist_le_abs_eval_sub gtime (glink k) ω
          _ ≤ K * Real.exp 1 * Real.sqrt C * Real.sqrt (sigmaSq k (d k)) :=
            hd_bound
      · exact hupper_tend
    have htime := hcf gtime
    have hadd := htime.add hdiff
    simpa [gtime, glink, add_sub_cancel_left] using hadd
  have hsum_tend : Tendsto
      (fun k =>
        (∑ i, ∑ j, c i * starRingEnd ℂ (c j) *
          ∫ ω, Complex.exp (Complex.I *
            ↑(ω ((f i : CylinderTestFunction Ls) -
              cylinderLinkReflection Ls (a k) (f j : CylinderTestFunction Ls))))
            ∂(cylinderPullbackMeasure Lt Ls (μseq k))).re)
      atTop
      (nhds ((∑ i, ∑ j, c i * starRingEnd ℂ (c j) *
        ∫ ω, Complex.exp (Complex.I *
          ↑(ω ((f i : CylinderTestFunction Ls) -
            cylinderTimeReflection Ls (f j : CylinderTestFunction Ls))))
          ∂(cylinderPullbackMeasure Lt Ls μ)).re)) := by
    apply Complex.continuous_re.continuousAt.tendsto.comp
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      Filter.Tendsto.const_mul (c i * starRingEnd ℂ (c j)) (hentry i j)
  unfold CylinderRPMatrixNonnegative
  exact ge_of_tendsto hsum_tend
    (Filter.Eventually.of_forall fun k => by
      simpa [CylinderLinkRPMatrixNonnegative] using hlink k)

end Pphi2
