/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# IR Tightness: Prokhorov Extraction for Lt → ∞

Proves tightness of the cylinder pullback measures as Lt → ∞ and
extracts a convergent subsequence via Prokhorov's theorem.

The structure follows `AsymTorusInteractingLimit.lean` exactly:
uniform second moments → Mitoma-Chebyshev → tightness → Prokhorov.

## Main result

- `cylinderIRLimit_exists` — existence of an IR-limit subsequence, conditional
  on the explicit eventual Green-controlled moment input
  `AsymTorusSequenceHasUniformGreenMomentBound`.

## References

- Simon, *The P(φ)₂ Euclidean QFT*, Ch. VIII
- Glimm-Jaffe, *Quantum Physics*, §19
-/

import Pphi2.IRLimit.GreenFunctionComparison
import Pphi2.IRLimit.UniformExponentialMoment
import GaussianField.Tightness
import GaussianField.ConfigurationEmbedding

noncomputable section

namespace Pphi2

open GaussianField MeasureTheory Filter

variable (Ls : ℝ) [hLs : Fact (0 < Ls)]

/-! ## Uniform Green-moment input for the IR family -/

/-- The remaining volume-uniform analytic input for Route B′.

Eventually, every asymmetric-torus measure in the family has the
Green-controlled exponential moment bound with the same constants `KG, CG`.
This is the precise tail hypothesis needed for cylinder tightness and OS0; the
finite initial segment is irrelevant to the IR limit and is therefore not
included in the predicate. The separate assumption `Lt → ∞` supplies `Lt ≥ 1`
on a tail when consumers need the method-of-images bound. -/
def AsymTorusSequenceHasUniformGreenMomentBound
    (mass : ℝ) (hmass : 0 < mass) (KG CG : ℝ)
    (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
    (μ : ∀ n, Measure (Configuration (AsymTorusTestFunction (Lt n) Ls))) : Prop :=
  ∀ᶠ n in atTop,
    @MeasureHasGreenMomentBound Ls _ (Lt n) (hLt n) mass hmass KG CG (μ n)

/-- A pointwise Green-moment bound is, in particular, the eventual sequence
input used by the IR-limit tightness theorem. -/
theorem AsymTorusSequenceHasUniformGreenMomentBound.of_forall
    (mass : ℝ) (hmass : 0 < mass) (KG CG : ℝ)
    (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
    (μ : ∀ n, Measure (Configuration (AsymTorusTestFunction (Lt n) Ls)))
    (h : ∀ n,
      @MeasureHasGreenMomentBound Ls _ (Lt n) (hLt n) mass hmass KG CG (μ n)) :
    AsymTorusSequenceHasUniformGreenMomentBound Ls mass hmass KG CG Lt hLt μ :=
  Filter.Eventually.of_forall h

/-- The previous stronger `Lt ≥ 1`-indexed shape implies the honest eventual
Green-moment input once the periods tend to infinity. -/
theorem AsymTorusSequenceHasUniformGreenMomentBound.of_forall_ge_one
    (mass : ℝ) (hmass : 0 < mass) (KG CG : ℝ)
    (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
    (hLt_tend : Tendsto Lt atTop atTop)
    (μ : ∀ n, Measure (Configuration (AsymTorusTestFunction (Lt n) Ls)))
    (h : ∀ n, 1 ≤ Lt n →
      @MeasureHasGreenMomentBound Ls _ (Lt n) (hLt n) mass hmass KG CG (μ n)) :
    AsymTorusSequenceHasUniformGreenMomentBound Ls mass hmass KG CG Lt hLt μ :=
  (tendsto_atTop.1 hLt_tend 1).mono h

/-- An eventual exponential-moment bound stated directly for a sequence of
cylinder measures.  The constants and seminorm are fixed before the eventual
quantifier. -/
def CylinderSequenceHasUniformExponentialMomentBound
    (K C : ℝ) (q : Seminorm ℝ (CylinderTestFunction Ls))
    (νseq : ℕ → Measure (Configuration (CylinderTestFunction Ls))) : Prop :=
  ∀ᶠ n in atTop,
    ∀ f : CylinderTestFunction Ls,
      Integrable (fun ω : Configuration (CylinderTestFunction Ls) =>
        Real.exp (|ω f|)) (νseq n) ∧
      ∫ ω : Configuration (CylinderTestFunction Ls),
        Real.exp (|ω f|) ∂(νseq n) ≤ K * Real.exp (C * q f ^ 2)

/-- The direct cylinder exponential-moment input for an asymmetric-torus
family.  Unlike the Green wrapper, this predicate carries no mass parameter
and imposes no lower bound on the period. -/
def AsymTorusSequenceHasUniformCylinderExpMomentBound
    (K C : ℝ) (q : Seminorm ℝ (CylinderTestFunction Ls))
    (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
    (μ : ∀ n, Measure (Configuration (AsymTorusTestFunction (Lt n) Ls))) : Prop :=
  ∀ᶠ n in atTop,
    @MeasureHasCylinderExpMomentBound Ls _ (Lt n) (hLt n) K C q (μ n)

/-- Eventual local degree-`n` exponential control for an asymmetric-torus
family, expressed after pullback to the fixed cylinder.  The period-dependent
`Fact` instance is kept in the predicate so that the eventual statement has
the same elaborated shape as the direct exponential-moment input. -/
def AsymTorusSequenceHasUniformLocalCylinderNthExpMomentBound
    (n : ℕ) (r : ℝ) (q : Seminorm ℝ (CylinderTestFunction Ls))
    (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
    (μ : ∀ n, Measure (Configuration (AsymTorusTestFunction (Lt n) Ls))) : Prop :=
  ∀ᶠ k in atTop,
    @MeasureHasLocalCylinderNthExpMomentBound Ls _ n r q
      (@cylinderPullbackMeasure (Lt k) Ls (hLt k) hLs (μ k))

/-- A local degree-`n` bound yields the fixed quadratic exponential interface
pointwise along the same eventual torus family.  The constants are those of
`measureHasCylinderExpMomentBound_of_localNth`, and therefore are fixed before
the eventual filter is taken. -/
theorem AsymTorusSequenceHasUniformCylinderExpMomentBound.of_localNth
    (n : ℕ) (hn_even : Even n) (hn4 : 4 ≤ n)
    (r : ℝ) (hr : 0 < r)
    (q : Seminorm ℝ (CylinderTestFunction Ls))
    (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
    (μ : ∀ n, Measure (Configuration (AsymTorusTestFunction (Lt n) Ls)))
    (hlocal : AsymTorusSequenceHasUniformLocalCylinderNthExpMomentBound
      Ls n r q Lt hLt μ) :
    AsymTorusSequenceHasUniformCylinderExpMomentBound Ls
      (2 * Real.exp ((n : ℝ) / 4 + 1 / (n : ℝ)))
      ((n : ℝ) / (4 * r ^ 2)) q Lt hLt μ := by
  change ∀ᶠ k in atTop,
    @MeasureHasCylinderExpMomentBound Ls _ (Lt k) (hLt k)
      (2 * Real.exp ((n : ℝ) / 4 + 1 / (n : ℝ)))
      ((n : ℝ) / (4 * r ^ 2)) q (μ k)
  change ∀ᶠ k in atTop,
    @MeasureHasLocalCylinderNthExpMomentBound Ls _ n r q
      (@cylinderPullbackMeasure (Lt k) Ls (hLt k) hLs (μ k)) at hlocal
  exact hlocal.mono (fun k hk =>
    letI : Fact (0 < Lt k) := hLt k
    measureHasCylinderExpMomentBound_of_localNth Ls n hn_even hn4 r hr q
      (μ k) hk)

private lemma cylinderExpEval_integrable
    (μ : Measure (Configuration (CylinderTestFunction Ls)))
    [IsProbabilityMeasure μ] (g : CylinderTestFunction Ls) :
    Integrable (fun ω : Configuration (CylinderTestFunction Ls) =>
      Complex.exp (Complex.I * ↑(ω g))) μ := by
  apply (integrable_const (1 : ℂ)).mono
  · exact (Complex.continuous_exp.measurable.comp
      (measurable_const.mul (Complex.continuous_ofReal.measurable.comp
        (configuration_eval_measurable g)))).aestronglyMeasurable
  · apply ae_of_all
    intro ω
    simp only [norm_one]
    rw [show Complex.I * ↑(ω g) = ↑(ω g) * Complex.I from mul_comm _ _]
    exact le_of_eq (Complex.norm_exp_ofReal_mul_I (ω g))

private lemma cylinderExpIntegral_re_eq_integral_cos
    (μ : Measure (Configuration (CylinderTestFunction Ls)))
    [IsProbabilityMeasure μ] (g : CylinderTestFunction Ls) :
    (∫ ω, Complex.exp (Complex.I * ↑(ω g)) ∂μ).re =
    ∫ ω : Configuration (CylinderTestFunction Ls), Real.cos (ω g) ∂μ := by
  simpa using configuration_expIntegral_re_eq_integral_cos μ g

private lemma cylinderExpIntegral_im_eq_integral_sin
    (μ : Measure (Configuration (CylinderTestFunction Ls)))
    [IsProbabilityMeasure μ] (g : CylinderTestFunction Ls) :
    (∫ ω, Complex.exp (Complex.I * ↑(ω g)) ∂μ).im =
    ∫ ω : Configuration (CylinderTestFunction Ls), Real.sin (ω g) ∂μ := by
  simpa using configuration_expIntegral_im_eq_integral_sin μ g

/-! ## IR Limit Existence

Given a sequence of time periods `Lt_n → ∞` and measures `μ_n` on
`AsymTorusTestFunction Lt_n Ls` satisfying the explicit eventual Green-moment
input, the pulled-back cylinder measures are tight and have a convergent
subsequence. -/

/-- Prokhorov extraction from an eventual direct exponential-moment bound on
a sequence of cylinder measures.  This is the source-independent core of the
IR construction. -/
theorem cylinderIRLimit_exists_of_eventual_expMoment
    (K C : ℝ) (hK : 0 < K) (hC : 0 < C)
    (q : Seminorm ℝ (CylinderTestFunction Ls))
    (νseq : ℕ → Measure (Configuration (CylinderTestFunction Ls)))
    (hν_prob : ∀ n, IsProbabilityMeasure (νseq n))
    (hν_exp : CylinderSequenceHasUniformExponentialMomentBound Ls K C q νseq) :
    ∃ (φ : ℕ → ℕ) (ν : Measure (Configuration (CylinderTestFunction Ls))),
    StrictMono φ ∧ IsProbabilityMeasure ν ∧
    (∀ (g : Configuration (CylinderTestFunction Ls) → ℝ),
      Continuous g → (∃ B, ∀ x, |g x| ≤ B) →
      Tendsto (fun n => ∫ ω, g ω ∂(νseq (φ n)))
        atTop (nhds (∫ ω, g ω ∂ν))) ∧
    (∀ f : CylinderTestFunction Ls,
      Tendsto (fun n =>
        ∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂(νseq (φ n)))
        atTop (nhds (∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂ν))) := by
  rcases eventually_atTop.1 hν_exp with ⟨N0, hN0⟩
  let νtail : ℕ → Measure (Configuration (CylinderTestFunction Ls)) :=
    fun n => νseq (n + N0)
  have hνtail_prob : ∀ n, IsProbabilityMeasure (νtail n) :=
    fun n => hν_prob (n + N0)
  have hνtail_second :
      ∀ (f : CylinderTestFunction Ls) (n : ℕ),
        Integrable (fun ω : Configuration (CylinderTestFunction Ls) =>
          (ω f) ^ 2) (νtail n) ∧
        ∫ ω : Configuration (CylinderTestFunction Ls),
          (ω f) ^ 2 ∂(νtail n) ≤
          (2 * K * C * Real.exp 1) * q f ^ 2 +
            (2 * K * C * Real.exp 1) := by
    intro f n
    exact cylinder_uniform_second_moment_of_expMoment Ls K C hK hC q
      (νtail n) (hN0 (n + N0) (Nat.le_add_left _ _)) f
  have hνtail_int :
      ∀ (f : CylinderTestFunction Ls) (n : ℕ),
        Integrable (fun ω : Configuration (CylinderTestFunction Ls) =>
          (ω f) ^ 2) (νtail n) :=
    fun f n => (hνtail_second f n).1
  have hνtail_moments :
      ∀ f : CylinderTestFunction Ls, ∃ B : ℝ, ∀ n,
        ∫ ω : Configuration (CylinderTestFunction Ls),
          (ω f) ^ 2 ∂(νtail n) ≤ B := by
    intro f
    exact ⟨(2 * K * C * Real.exp 1) * q f ^ 2 +
      (2 * K * C * Real.exp 1), fun n => (hνtail_second f n).2⟩
  have hνtail_tight : ∀ ε : ℝ, 0 < ε →
      ∃ A : Set (Configuration (CylinderTestFunction Ls)), IsCompact A ∧
        ∀ n, 1 - ε ≤ ((νtail n) A).toReal := by
    intro ε hε
    exact configuration_tight_of_uniform_second_moments
      νtail hνtail_prob hνtail_int hνtail_moments ε hε
  obtain ⟨φtail, ν, hφtail, hν_lim_prob, hconv⟩ :=
    prokhorov_configuration νtail hνtail_prob hνtail_tight
  have hcf_tail : ∀ (f : CylinderTestFunction Ls),
      Tendsto (fun n =>
        ∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂(νtail (φtail n)))
      atTop (nhds (∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂ν)) := by
    intro f
    have hcos : Tendsto
        (fun n => ∫ ω, Real.cos (ω f) ∂(νtail (φtail n)))
        atTop (nhds (∫ ω, Real.cos (ω f) ∂ν)) :=
      hconv (fun ω => Real.cos (ω f))
        (Real.continuous_cos.comp (WeakDual.eval_continuous f))
        ⟨1, fun ω => Real.abs_cos_le_one (ω f)⟩
    have hsin : Tendsto
        (fun n => ∫ ω, Real.sin (ω f) ∂(νtail (φtail n)))
        atTop (nhds (∫ ω, Real.sin (ω f) ∂ν)) :=
      hconv (fun ω => Real.sin (ω f))
        (Real.continuous_sin.comp (WeakDual.eval_continuous f))
        ⟨1, fun ω => Real.abs_sin_le_one (ω f)⟩
    have h_re : Tendsto
        (fun n => (∫ ω, Complex.exp (Complex.I * ↑(ω f))
          ∂(νtail (φtail n))).re)
        atTop (nhds ((∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂ν).re)) := by
      have h_re_eq :
          (fun n => (∫ ω, Complex.exp (Complex.I * ↑(ω f))
            ∂(νtail (φtail n))).re) =
          fun n => ∫ ω, Real.cos (ω f) ∂(νtail (φtail n)) := by
        funext n
        haveI : IsProbabilityMeasure (νtail (φtail n)) := hνtail_prob (φtail n)
        exact cylinderExpIntegral_re_eq_integral_cos Ls (νtail (φtail n)) f
      have h_re_lim :
          (∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂ν).re =
          ∫ ω, Real.cos (ω f) ∂ν := by
        haveI : IsProbabilityMeasure ν := hν_lim_prob
        exact cylinderExpIntegral_re_eq_integral_cos Ls ν f
      rw [h_re_eq, h_re_lim]
      exact hcos
    have h_im : Tendsto
        (fun n => (∫ ω, Complex.exp (Complex.I * ↑(ω f))
          ∂(νtail (φtail n))).im)
        atTop (nhds ((∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂ν).im)) := by
      have h_im_eq :
          (fun n => (∫ ω, Complex.exp (Complex.I * ↑(ω f))
            ∂(νtail (φtail n))).im) =
          fun n => ∫ ω, Real.sin (ω f) ∂(νtail (φtail n)) := by
        funext n
        haveI : IsProbabilityMeasure (νtail (φtail n)) := hνtail_prob (φtail n)
        exact cylinderExpIntegral_im_eq_integral_sin Ls (νtail (φtail n)) f
      have h_im_lim :
          (∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂ν).im =
          ∫ ω, Real.sin (ω f) ∂ν := by
        haveI : IsProbabilityMeasure ν := hν_lim_prob
        exact cylinderExpIntegral_im_eq_integral_sin Ls ν f
      rw [h_im_eq, h_im_lim]
      exact hsin
    have h_pair : Tendsto
        (fun n =>
          ((∫ ω, Complex.exp (Complex.I * ↑(ω f))
              ∂(νtail (φtail n))).re,
           (∫ ω, Complex.exp (Complex.I * ↑(ω f))
              ∂(νtail (φtail n))).im))
        atTop
        (nhds
          (((∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂ν).re),
           ((∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂ν).im))) :=
      h_re.prodMk_nhds h_im
    have h_complex : Tendsto
        (fun n => Complex.equivRealProdCLM.symm
          ((∫ ω, Complex.exp (Complex.I * ↑(ω f))
              ∂(νtail (φtail n))).re,
           (∫ ω, Complex.exp (Complex.I * ↑(ω f))
              ∂(νtail (φtail n))).im))
        atTop
        (nhds (Complex.equivRealProdCLM.symm
          (((∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂ν).re),
           ((∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂ν).im)))) :=
      (Complex.equivRealProdCLM.symm.continuous.tendsto
        (((∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂ν).re),
         ((∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂ν).im))).comp h_pair
    simpa [Complex.equivRealProdCLM_symm_apply, Complex.re_add_im] using h_complex
  let φ : ℕ → ℕ := fun n => φtail n + N0
  have hφ : StrictMono φ := by
    intro a b hab
    exact Nat.add_lt_add_right (hφtail hab) N0
  refine ⟨φ, ν, hφ, hν_lim_prob, ?_, ?_⟩
  · intro g hg_cont hg_bdd
    simpa [φ, νtail] using hconv g hg_cont hg_bdd
  · intro f
    simpa [φ, νtail] using hcf_tail f

/-- Specialization of the direct extraction core to pullbacks of an
asymmetric-torus family. -/
theorem cylinderIRLimit_exists_of_uniform_cylinderExpMoment
    (K C : ℝ) (hK : 0 < K) (hC : 0 < C)
    (q : Seminorm ℝ (CylinderTestFunction Ls))
    (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
    (μ : ∀ n, Measure (Configuration (AsymTorusTestFunction (Lt n) Ls)))
    (hμ_prob : ∀ n, IsProbabilityMeasure (μ n))
    (hμ_exp : AsymTorusSequenceHasUniformCylinderExpMomentBound
      Ls K C q Lt hLt μ) :
    ∃ (φ : ℕ → ℕ) (ν : Measure (Configuration (CylinderTestFunction Ls))),
    StrictMono φ ∧ IsProbabilityMeasure ν ∧
    (∀ (g : Configuration (CylinderTestFunction Ls) → ℝ),
      Continuous g → (∃ B, ∀ x, |g x| ≤ B) →
      Tendsto (fun n =>
        ∫ ω, g ω ∂(@cylinderPullbackMeasure (Lt (φ n)) Ls
          (hLt (φ n)) hLs (μ (φ n))))
        atTop (nhds (∫ ω, g ω ∂ν))) ∧
    (∀ f : CylinderTestFunction Ls,
      Tendsto (fun n =>
        ∫ ω, Complex.exp (Complex.I * ↑(ω f))
          ∂(@cylinderPullbackMeasure (Lt (φ n)) Ls
            (hLt (φ n)) hLs (μ (φ n))))
        atTop (nhds (∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂ν))) := by
  let νseq : ℕ → Measure (Configuration (CylinderTestFunction Ls)) := fun n =>
    @cylinderPullbackMeasure (Lt n) Ls (hLt n) hLs (μ n)
  have hν_prob : ∀ n, IsProbabilityMeasure (νseq n) := by
    intro n
    dsimp [νseq]
    haveI : Fact (0 < Lt n) := hLt n
    haveI : IsProbabilityMeasure (μ n) := hμ_prob n
    have hmeas : Measurable (cylinderPullback (Lt n) Ls) :=
      configuration_measurable_of_eval_measurable _
        (fun φ => configuration_eval_measurable _)
    exact Measure.isProbabilityMeasure_map hmeas.aemeasurable
  have hν_exp : CylinderSequenceHasUniformExponentialMomentBound
      Ls K C q νseq := by
    simpa [AsymTorusSequenceHasUniformCylinderExpMomentBound,
      CylinderSequenceHasUniformExponentialMomentBound,
      MeasureHasCylinderExpMomentBound, νseq] using hμ_exp
  simpa [νseq] using
    (cylinderIRLimit_exists_of_eventual_expMoment Ls K C hK hC q
      νseq hν_prob hν_exp)

/-- The IR limit measure on the cylinder S¹_{Ls} × ℝ exists.

Given a sequence of time periods `Lt : ℕ → ℝ` with `Lt n → ∞`, measures `μ_n`
on the corresponding asymmetric tori, and an eventual Green-controlled
exponential moment bound, the pulled-back cylinder measures
`cylinderPullbackMeasure (Lt n) Ls (μ n)` have a weakly convergent subsequence.

The Green input is converted to a cylinder exponential-moment bound by
`cylinderIR_uniform_exponential_moment`; the source-independent extractor
`cylinderIRLimit_exists_of_uniform_cylinderExpMoment` then supplies tightness
and bounded-continuous / characteristic-functional convergence. -/
theorem cylinderIRLimit_exists
    (mass : ℝ) (hmass : 0 < mass)
    (KG CG : ℝ) (hKG_pos : 0 < KG) (hCG_pos : 0 < CG)
    (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
    (hLt_tend : Tendsto Lt atTop atTop)
    (μ : ∀ n, Measure (Configuration (AsymTorusTestFunction (Lt n) Ls)))
    (hμ_prob : ∀ n, IsProbabilityMeasure (μ n))
    (hμ_green : AsymTorusSequenceHasUniformGreenMomentBound Ls mass hmass KG CG Lt hLt μ) :
    ∃ (φ : ℕ → ℕ) (ν : Measure (Configuration (CylinderTestFunction Ls))),
    StrictMono φ ∧ IsProbabilityMeasure ν ∧
    -- Bounded-continuous convergence (full weak convergence)
    (∀ (g : Configuration (CylinderTestFunction Ls) → ℝ),
      Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
      Tendsto (fun n =>
        ∫ ω, g ω ∂(@cylinderPullbackMeasure (Lt (φ n)) Ls
          (hLt (φ n)) hLs (μ (φ n))))
        atTop (nhds (∫ ω, g ω ∂ν))) ∧
    -- Characteristic functional convergence
    (∀ (f : CylinderTestFunction Ls),
    Tendsto (fun n =>
      ∫ ω, Complex.exp (Complex.I * ↑(ω f))
        ∂(@cylinderPullbackMeasure (Lt (φ n)) Ls
          (hLt (φ n)) hLs (μ (φ n))))
      atTop (nhds (∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂ν))) := by
  obtain ⟨K, C, q, hK, hC, hq_cont, hbound⟩ :=
    cylinderIR_uniform_exponential_moment Ls mass hmass KG CG hKG_pos hCG_pos
  have hLt_ge_one : ∀ᶠ n in atTop, 1 ≤ Lt n := tendsto_atTop.1 hLt_tend 1
  have hμ_green_raw : ∀ᶠ n in atTop,
      @MeasureHasGreenMomentBound Ls _ (Lt n) (hLt n)
        mass hmass KG CG (μ n) := by
    simpa [AsymTorusSequenceHasUniformGreenMomentBound] using hμ_green
  have hμ_exp : AsymTorusSequenceHasUniformCylinderExpMomentBound
      Ls K C q Lt hLt μ := by
    rw [AsymTorusSequenceHasUniformCylinderExpMomentBound]
    filter_upwards [hLt_ge_one, hμ_green_raw] with n hLt_one hgreen
    haveI : Fact (0 < Lt n) := hLt n
    haveI : IsProbabilityMeasure (μ n) := hμ_prob n
    exact hbound (Lt n) hLt_one (μ n) hgreen
  exact cylinderIRLimit_exists_of_uniform_cylinderExpMoment
    Ls K C hK hC q Lt hLt μ hμ_prob hμ_exp

end Pphi2
