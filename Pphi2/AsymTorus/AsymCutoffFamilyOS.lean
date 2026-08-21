/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/

import Pphi2.AsymTorus.AsymContinuumLimit
import Pphi2.AsymTorus.AsymIsoOS
import Pphi2.AsymTorus.AsymSamplingBridge
import Pphi2.AsymTorus.AsymLinkReflectionRPLimit
import Pphi2.AsymTorus.MomentBoundOS1
import Pphi2.IRLimit.IRTightness
import Pphi2.IRLimit.CylinderOS

/-!
# Cutoff-family OS assembly for the isotropic cylinder route

Even-time UV constructions, infrared families, no-wrap reflection positivity,
the volume-uniform interacting exponential-moment axiom, and the quartic
headline `cylinderIso_OS_of_RP_OS2`.
-/


noncomputable section

open MeasureTheory GaussianField Filter

namespace Pphi2

variable (Lt Ls : ℝ) [hLt : Fact (0 < Lt)] [hLs : Fact (0 < Ls)]

/-- The even-time UV construction transfers a direct cylinder-seminorm
exponential-moment estimate to the torus weak limit.  It also retains the two
OS2 symmetries and no-wrap cylinder reflection positivity.

The estimate is required only along the selected cutoff sequence. -/
theorem asymTorusIso_measureHasCylinderExpMomentBound_of_cutoff_withNoWrapRP
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (K C : ℝ) (hK_pos : 0 < K) (hC_pos : 0 < C)
    (q : Seminorm ℝ (CylinderTestFunction Ls)) (hq : Continuous q)
    (M Ns : ℕ → ℕ) (a : ℕ → ℝ)
    (hM : ∀ k, NeZero (M k)) (hNs : ∀ k, NeZero (Ns k))
    (ha : ∀ k, 0 < a k)
    (hvolt : ∀ k, ((2 * M k : ℕ) : ℝ) * a k = Lt)
    (hvols : ∀ k, (Ns k : ℝ) * a k = Ls)
    (ha0 : Filter.Tendsto a Filter.atTop (nhds 0))
    (hcutoff : ∀ k,
      letI : NeZero (M k) := hM k
      letI : NeZero (Ns k) := hNs k
      ∀ f : CylinderTestFunction Ls,
        Integrable (fun ω : Configuration (CylinderTestFunction Ls) =>
          Real.exp (|ω f|))
          (cylinderPullbackMeasure Lt Ls
            (asymTorusInteractingMeasureIso Lt Ls (2 * M k) (Ns k) (a k)
              P mass (ha k) hmass)) ∧
        ∫ ω : Configuration (CylinderTestFunction Ls),
          Real.exp (|ω f|) ∂(cylinderPullbackMeasure Lt Ls
            (asymTorusInteractingMeasureIso Lt Ls (2 * M k) (Ns k) (a k)
              P mass (ha k) hmass)) ≤
          K * Real.exp (C * q f ^ 2)) :
    ∃ μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)),
      IsProbabilityMeasure μ ∧
      MeasureHasCylinderExpMomentBound Ls K C q μ ∧
      (∀ hμ_prob : IsProbabilityMeasure μ,
        @AsymTorusOS2_TranslationInvariance Lt Ls hLt hLs μ hμ_prob ∧
        @AsymTorusOS2_TimeReflectionInvariance Lt Ls hLt hLs μ hμ_prob) ∧
      CylinderMeasureNoWrapReflectionPositive Lt Ls
        (cylinderPullbackMeasure Lt Ls μ) := by
  have hNt : ∀ k, NeZero (2 * M k) := fun k => by
    letI := hM k
    infer_instance
  obtain ⟨μ, hμ_prob, φ, hφ_mono, hconv⟩ :=
    asymTorusIso_interacting_limit_exists Lt Ls P mass hmass
      (fun k => 2 * M k) Ns a hNt hNs ha hvolt hvols ha0
  haveI : IsProbabilityMeasure μ := hμ_prob
  set ν : ℕ → Measure (Configuration (AsymTorusTestFunction Lt Ls)) := fun n =>
    haveI := hM (φ n)
    haveI := hNs (φ n)
    asymTorusInteractingMeasureIso Lt Ls (2 * M (φ n)) (Ns (φ n)) (a (φ n))
      P mass (ha (φ n)) hmass with hν_def
  have hν_prob : ∀ n, IsProbabilityMeasure (ν n) := fun n => by
    haveI := hM (φ n)
    haveI := hNs (φ n)
    exact asymTorusInteractingMeasureIso_isProbability Lt Ls
      (2 * M (φ n)) (Ns (φ n)) (a (φ n)) P mass (ha (φ n)) hmass
  have hφ_atTop : Filter.Tendsto φ Filter.atTop Filter.atTop :=
    hφ_mono.tendsto_atTop
  have hbc : ∀ (g : Configuration (AsymTorusTestFunction Lt Ls) → ℝ),
      Continuous g → (∃ D, ∀ x, |g x| ≤ D) →
      Filter.Tendsto (fun n => ∫ ω, g ω ∂(ν n)) Filter.atTop
        (nhds (∫ ω, g ω ∂μ)) := by
    intro g hg hg_bound
    simpa [ν] using hconv g hg hg_bound
  have hμ_exp : MeasureHasCylinderExpMomentBound Ls K C q μ := by
    intro f
    apply cylinderPullbackMeasure_exponential_moment_of_tendsto_bc
      Lt Ls ν μ hν_prob hμ_prob hbc f
      (fun _ => K * Real.exp (C * q f ^ 2))
      (K * Real.exp (C * q f ^ 2)) tendsto_const_nhds
    intro n
    haveI := hM (φ n)
    haveI := hNs (φ n)
    simpa [ν] using hcutoff (φ n) f
  have hμ_os2 := asymTorusIso_limit_satisfies_OS2 Lt Ls P mass hmass
    (fun k => 2 * M k) Ns a hNt hNs ha hvolt hvols ha0 μ φ hφ_mono hconv
  refine ⟨μ, hμ_prob, hμ_exp, (fun _ => hμ_os2), ?_⟩
  intro R hR hLtR n f c hf
  let sigmaSq : ℕ → CylinderTestFunction Ls → ℝ := fun _ h => q h ^ 2
  apply cylinderRPMatrixNonnegative_of_link_limit Lt Ls ν μ hν_prob hμ_prob hbc
    (fun k => a (φ k)) (ha0.comp hφ_atTop) sigmaSq K C hK_pos hC_pos
  · intro k h
    exact sq_nonneg (q h)
  · intro k t h
    dsimp [sigmaSq]
    rw [SeminormClass.map_smul_eq_mul, mul_pow, Real.norm_eq_abs, sq_abs]
  · intro hseq hseq0
    have hq0 : Filter.Tendsto (fun k => q (hseq k)) Filter.atTop (nhds 0) := by
      have h := hq.continuousAt.tendsto.comp hseq0
      simpa using h
    simpa [sigmaSq] using hq0.pow 2
  · intro k h
    haveI := hM (φ k)
    haveI := hNs (φ k)
    simpa [ν, sigmaSq] using hcutoff (φ k) h
  · intro k
    haveI := hM (φ k)
    haveI := hNs (φ k)
    exact asymTorusInteractingMeasureIso_cylinderLinkRPMatrix_span_noWrap
      Lt Ls P (a (φ k)) mass (ha (φ k)) hmass (M (φ k)) (Ns (φ k))
      (hvolt (φ k)) (hvols (φ k)) R hR hLtR n f c hf

/-- Apply the direct cutoff-to-limit construction at every period in an
explicit infrared family.  The same constants and cylinder seminorm are fixed
before both the infrared and ultraviolet indices. -/
theorem asymTorusIso_cylinderUniformCylinderExpMomentBound_of_cutoffFamily
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (K C : ℝ) (hK_pos : 0 < K) (hC_pos : 0 < C)
    (q : Seminorm ℝ (CylinderTestFunction Ls)) (hq : Continuous q)
    (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
    (M Ns : ℕ → ℕ → ℕ) (a : ℕ → ℕ → ℝ)
    (hM : ∀ n k, NeZero (M n k)) (hNs : ∀ n k, NeZero (Ns n k))
    (ha : ∀ n k, 0 < a n k)
    (hvolt : ∀ n k, ((2 * M n k : ℕ) : ℝ) * a n k = Lt n)
    (hvols : ∀ n k, (Ns n k : ℝ) * a n k = Ls)
    (ha0 : ∀ n, Filter.Tendsto (a n) Filter.atTop (nhds 0))
    (hcutoff : ∀ n k,
      letI : NeZero (M n k) := hM n k
      letI : NeZero (Ns n k) := hNs n k
      ∀ f : CylinderTestFunction Ls,
        Integrable (fun ω : Configuration (CylinderTestFunction Ls) =>
          Real.exp (|ω f|))
          (@cylinderPullbackMeasure (Lt n) Ls (hLt n) hLs
            (asymTorusInteractingMeasureIso (Lt n) Ls
              (2 * M n k) (Ns n k) (a n k) P mass (ha n k) hmass)) ∧
        ∫ ω : Configuration (CylinderTestFunction Ls),
          Real.exp (|ω f|)
            ∂(@cylinderPullbackMeasure (Lt n) Ls (hLt n) hLs
              (asymTorusInteractingMeasureIso (Lt n) Ls
                (2 * M n k) (Ns n k) (a n k) P mass (ha n k) hmass)) ≤
          K * Real.exp (C * q f ^ 2)) :
    ∃ μ : ∀ n, Measure (Configuration (AsymTorusTestFunction (Lt n) Ls)),
      (∀ n, IsProbabilityMeasure (μ n)) ∧
      AsymTorusSequenceHasUniformCylinderExpMomentBound Ls K C q Lt hLt μ ∧
      AsymTorusSequenceHasCylinderOS2Symmetry Ls Lt hLt μ ∧
      (∀ n,
        CylinderMeasureNoWrapReflectionPositive (Lt n) Ls
          (@cylinderPullbackMeasure (Lt n) Ls (hLt n) hLs (μ n))) := by
  have hbound : ∀ n,
      letI : Fact (0 < Lt n) := hLt n
      ∃ μ : Measure (Configuration (AsymTorusTestFunction (Lt n) Ls)),
        IsProbabilityMeasure μ ∧
        MeasureHasCylinderExpMomentBound Ls K C q μ ∧
        (∀ hμ_prob : IsProbabilityMeasure μ,
          @AsymTorusOS2_TranslationInvariance (Lt n) Ls (hLt n) hLs μ hμ_prob ∧
          @AsymTorusOS2_TimeReflectionInvariance (Lt n) Ls (hLt n) hLs μ hμ_prob) ∧
        CylinderMeasureNoWrapReflectionPositive (Lt n) Ls
          (@cylinderPullbackMeasure (Lt n) Ls (hLt n) hLs μ) := by
    intro n
    letI : Fact (0 < Lt n) := hLt n
    exact asymTorusIso_measureHasCylinderExpMomentBound_of_cutoff_withNoWrapRP
      (Lt n) Ls P mass hmass K C hK_pos hC_pos q hq
      (M n) (Ns n) (a n) (hM n) (hNs n) (ha n) (hvolt n) (hvols n) (ha0 n)
      (fun k => by
        letI : NeZero (M n k) := hM n k
        letI : NeZero (Ns n k) := hNs n k
        intro f
        exact hcutoff n k f)
  choose μ hμ_prob hμ_exp hμ_os2 hμ_rp using hbound
  have hμ_exp_seq : AsymTorusSequenceHasUniformCylinderExpMomentBound
      Ls K C q Lt hLt μ := by
    exact Filter.Eventually.of_forall fun n => by
      letI : Fact (0 < Lt n) := hLt n
      simpa [MeasureHasCylinderExpMomentBound] using hμ_exp n
  have hμ_os2_seq : AsymTorusSequenceHasCylinderOS2Symmetry Ls Lt hLt μ := by
    constructor
    · intro n
      letI : Fact (0 < Lt n) := hLt n
      haveI : IsProbabilityMeasure (μ n) := hμ_prob n
      intro v f
      simpa [AsymTorusOS2_TranslationInvariance, asymTorusGeneratingFunctional] using
        (hμ_os2 n (hμ_prob n)).1 v f
    · intro n
      letI : Fact (0 < Lt n) := hLt n
      haveI : IsProbabilityMeasure (μ n) := hμ_prob n
      intro f
      simpa [AsymTorusOS2_TimeReflectionInvariance, asymTorusGeneratingFunctional] using
        (hμ_os2 n (hμ_prob n)).2 f
  exact ⟨μ, hμ_prob, hμ_exp_seq, hμ_os2_seq, hμ_rp⟩

/-- Route B' from an explicit two-scale cutoff family carrying one direct
cylinder exponential-moment bound. -/
theorem routeBPrimeIso_cylinder_OS_of_cutoffFamily
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (K C : ℝ) (hK_pos : 0 < K) (hC_pos : 0 < C)
    (q : Seminorm ℝ (CylinderTestFunction Ls)) (hq : Continuous q)
    (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
    (hLt_tend : Filter.Tendsto Lt Filter.atTop Filter.atTop)
    (M Ns : ℕ → ℕ → ℕ) (a : ℕ → ℕ → ℝ)
    (hM : ∀ n k, NeZero (M n k)) (hNs : ∀ n k, NeZero (Ns n k))
    (ha : ∀ n k, 0 < a n k)
    (hvolt : ∀ n k, ((2 * M n k : ℕ) : ℝ) * a n k = Lt n)
    (hvols : ∀ n k, (Ns n k : ℝ) * a n k = Ls)
    (ha0 : ∀ n, Filter.Tendsto (a n) Filter.atTop (nhds 0))
    (hcutoff : ∀ n k,
      letI : NeZero (M n k) := hM n k
      letI : NeZero (Ns n k) := hNs n k
      ∀ f : CylinderTestFunction Ls,
        Integrable (fun ω : Configuration (CylinderTestFunction Ls) =>
          Real.exp (|ω f|))
          (@cylinderPullbackMeasure (Lt n) Ls (hLt n) hLs
            (asymTorusInteractingMeasureIso (Lt n) Ls
              (2 * M n k) (Ns n k) (a n k) P mass (ha n k) hmass)) ∧
        ∫ ω : Configuration (CylinderTestFunction Ls),
          Real.exp (|ω f|)
            ∂(@cylinderPullbackMeasure (Lt n) Ls (hLt n) hLs
              (asymTorusInteractingMeasureIso (Lt n) Ls
                (2 * M n k) (Ns n k) (a n k) P mass (ha n k) hmass)) ≤
          K * Real.exp (C * q f ^ 2)) :
    ∃ ν : Measure (Configuration (CylinderTestFunction Ls)),
      IsProbabilityMeasure ν ∧
      (∀ (n : ℕ) (J : Fin n → CylinderTestFunction Ls),
        AnalyticOnNhd ℂ (fun z : Fin n → ℂ =>
          ∫ ω, Complex.exp (∑ i, Complex.I * z i * ↑(ω (J i))) ∂ν) Set.univ) ∧
      (∀ f : CylinderTestFunction Ls,
        ∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂ν =
        ∫ ω, Complex.exp (Complex.I * ↑(ω (cylinderTimeReflection Ls f))) ∂ν) ∧
      (∀ (τ : ℝ) (f : CylinderTestFunction Ls),
        ∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂ν =
        ∫ ω, Complex.exp (Complex.I * ↑(ω (cylinderTranslation Ls 0 τ f))) ∂ν) ∧
      (∀ (v : ℝ) (f : CylinderTestFunction Ls),
        ∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂ν =
        ∫ ω, Complex.exp (Complex.I * ↑(ω (cylinderSpatialTranslation Ls v f))) ∂ν) ∧
      (∀ (n : ℕ) (f : Fin n → ↥(cylinderPositiveTimeSubmodule Ls)) (c : Fin n → ℂ),
        0 ≤ (∑ i, ∑ j, c i * starRingEnd ℂ (c j) *
          ∫ ω, Complex.exp (Complex.I *
            ↑(ω ((f i : CylinderTestFunction Ls) -
              cylinderTimeReflection Ls (f j : CylinderTestFunction Ls)))) ∂ν).re) := by
  obtain ⟨μ, hμ_prob, hμ_exp, hμ_os2, hμ_noWrap⟩ :=
    asymTorusIso_cylinderUniformCylinderExpMomentBound_of_cutoffFamily
      Ls P mass hmass K C hK_pos hC_pos q hq Lt hLt
      M Ns a hM hNs ha hvolt hvols ha0 hcutoff
  exact routeBPrime_cylinder_OS_of_uniform_cylinderExpMoment Ls K C
    hK_pos hC_pos q hq Lt hLt hLt_tend μ hμ_prob hμ_exp
    (fun φ ν hν_prob hφ hcf K' C' q' hK' hC' hq' hExp => by
      letI : IsProbabilityMeasure ν := hν_prob
      exact cylinderMeasureReflectionPositive_of_noWrap_limit Ls
        (fun k => Lt (φ k)) (hLt_tend.comp hφ.tendsto_atTop)
        (fun k => @cylinderPullbackMeasure (Lt (φ k)) Ls
          (hLt (φ k)) hLs (μ (φ k)))
        ν hcf (fun k => hμ_noWrap (φ k)) K' C' hK' hC' q' hq' hExp)
    hμ_os2


theorem asymTorusIso_measureHasGreenMomentBound_of_cutoff_withNoWrapRP_withUV
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (K C : ℝ) (hK_pos : 0 < K) (hC_pos : 0 < C)
    (hcutoff : ∀ (f : AsymTorusTestFunction Lt Ls) (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
      (a : ℝ) (ha : 0 < a), (Nt : ℝ) * a = Lt → (Ns : ℝ) * a = Ls →
      Integrable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
        Real.exp (|ω f|)) (asymTorusInteractingMeasureIso Lt Ls Nt Ns a P mass ha hmass) ∧
      ∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
        Real.exp (|ω f|) ∂(asymTorusInteractingMeasureIso Lt Ls Nt Ns a P mass ha hmass) ≤
      K * Real.exp (C * ∫ ω : Configuration (AsymLatticeField Nt Ns),
        (ω (asymLatticeTestFnIso Lt Ls Nt Ns a f)) ^ 2
        ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass)))
    (M Ns : ℕ → ℕ) (a : ℕ → ℝ)
    (hM : ∀ k, NeZero (M k)) (hNs : ∀ k, NeZero (Ns k)) (ha : ∀ k, 0 < a k)
    (hvolt : ∀ k, ((2 * M k : ℕ) : ℝ) * a k = Lt)
    (hvols : ∀ k, (Ns k : ℝ) * a k = Ls)
    (ha0 : Filter.Tendsto a Filter.atTop (nhds 0)) :
    ∃ (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls))),
      IsProbabilityMeasure μ ∧
      MeasureHasGreenMomentBound Ls mass hmass K C μ ∧
      (∀ hμ_prob : IsProbabilityMeasure μ,
        @AsymSatisfiesTorusOS Lt Ls hLt hLs μ hμ_prob) ∧
      CylinderMeasureNoWrapReflectionPositive Lt Ls
        (cylinderPullbackMeasure Lt Ls μ) ∧
      (∃ (φ : ℕ → ℕ), StrictMono φ ∧
        (∀ (F : Configuration (AsymTorusTestFunction Lt Ls) → ℝ),
          Continuous F → (∃ D, ∀ x, |F x| ≤ D) →
          Filter.Tendsto
            (fun n => ∫ ω, F ω ∂(haveI := hM (φ n); haveI := hNs (φ n)
              asymTorusInteractingMeasureIso Lt Ls (2 * M (φ n)) (Ns (φ n))
                (a (φ n)) P mass (ha (φ n)) hmass))
            Filter.atTop (nhds (∫ ω, F ω ∂μ)))) := by
  have hNt : ∀ k, NeZero (2 * M k) := fun k => by
    letI := hM k
    infer_instance
  obtain ⟨μ, hμ_prob, φ, hφ_mono, hconv⟩ :=
    asymTorusIso_interacting_limit_exists Lt Ls P mass hmass
      (fun k => 2 * M k) Ns a hNt hNs ha hvolt hvols ha0
  haveI := hμ_prob
  set ν : ℕ → Measure (Configuration (AsymTorusTestFunction Lt Ls)) := fun n =>
    haveI := hM (φ n)
    haveI := hNs (φ n)
    asymTorusInteractingMeasureIso Lt Ls (2 * M (φ n)) (Ns (φ n)) (a (φ n))
      P mass (ha (φ n)) hmass with hν_def
  have hν_prob : ∀ n, IsProbabilityMeasure (ν n) := fun n => by
    haveI := hM (φ n)
    haveI := hNs (φ n)
    exact asymTorusInteractingMeasureIso_isProbability Lt Ls
      (2 * M (φ n)) (Ns (φ n)) (a (φ n)) P mass (ha (φ n)) hmass
  have hφ_atTop : Filter.Tendsto φ Filter.atTop Filter.atTop := hφ_mono.tendsto_atTop
  have hbc : ∀ (g : Configuration (AsymTorusTestFunction Lt Ls) → ℝ),
      Continuous g → (∃ D, ∀ x, |g x| ≤ D) →
      Filter.Tendsto (fun n => ∫ ω, g ω ∂(ν n)) Filter.atTop
        (nhds (∫ ω, g ω ∂μ)) := by
    intro g hg_cont hg_bdd
    simpa [ν] using hconv g hg_cont hg_bdd
  have hμ_green : MeasureHasGreenMomentBound Ls mass hmass K C μ := by
    intro f
    set B : ℕ → ℝ := fun n => K * Real.exp (C *
      haveI := hM (φ n)
      haveI := hNs (φ n)
      ∫ ω : Configuration (AsymLatticeField (2 * M (φ n)) (Ns (φ n))),
        (ω (asymLatticeTestFnIso Lt Ls (2 * M (φ n)) (Ns (φ n)) (a (φ n)) f)) ^ 2
        ∂(latticeGaussianMeasureAsym (2 * M (φ n)) (Ns (φ n)) (a (φ n))
          mass (ha (φ n)) hmass)) with hB_def
    have hσ2_full : Filter.Tendsto (fun k =>
        haveI := hM k
        haveI := hNs k
        ∫ ω : Configuration (AsymLatticeField (2 * M k) (Ns k)),
          (ω (asymLatticeTestFnIso Lt Ls (2 * M k) (Ns k) (a k) f)) ^ 2
          ∂(latticeGaussianMeasureAsym (2 * M k) (Ns k) (a k) mass (ha k) hmass))
        Filter.atTop (nhds (asymTorusContinuumGreen Lt Ls mass hmass f f)) := by
      have heq : (fun k =>
          haveI := hM k
          haveI := hNs k
          ∫ ω : Configuration (AsymLatticeField (2 * M k) (Ns k)),
            (ω (asymLatticeTestFnIso Lt Ls (2 * M k) (Ns k) (a k) f)) ^ 2
            ∂(latticeGaussianMeasureAsym (2 * M k) (Ns k) (a k) mass (ha k) hmass)) =
          fun k =>
            haveI := hM k
            haveI := hNs k
            covariance (latticeCovarianceAsymGJ (2 * M k) (Ns k) (a k)
              mass (ha k) hmass)
              (asymLatticeTestFnIso Lt Ls (2 * M k) (Ns k) (a k) f)
              (asymLatticeTestFnIso Lt Ls (2 * M k) (Ns k) (a k) f) := by
        funext k
        haveI := hM k
        haveI := hNs k
        exact second_moment_eq_covariance _ _
      rw [heq]
      exact second_moment_asym_tendsto Lt Ls mass hmass
        (fun k => 2 * M k) Ns a hNt hNs ha hvolt hvols ha0 f f
    have hB_tendsto : Filter.Tendsto B Filter.atTop
        (nhds (K * Real.exp (C * asymTorusContinuumGreen Lt Ls mass hmass f f))) := by
      rw [hB_def]
      exact ((Real.continuous_exp.tendsto _).comp
        (((hσ2_full.comp hφ_atTop).const_mul C))).const_mul K
    have h_unif : ∀ n, Integrable (fun ω => Real.exp (|ω f|)) (ν n) ∧
        ∫ ω, Real.exp (|ω f|) ∂(ν n) ≤ B n := fun n => by
      haveI := hM (φ n)
      haveI := hNs (φ n)
      exact hcutoff f (2 * M (φ n)) (Ns (φ n)) (a (φ n)) (ha (φ n))
        (hvolt (φ n)) (hvols (φ n))
    exact weakLimit_exponential_moment ν hν_prob μ hbc f B
      (K * Real.exp (C * asymTorusContinuumGreen Lt Ls mass hmass f f))
      hB_tendsto h_unif
  have hμ_os : AsymSatisfiesTorusOS Lt Ls μ :=
    asymTorusIso_limit_satisfies_OS Lt Ls P mass hmass K C hK_pos hC_pos
      (fun k => 2 * M k) Ns a hNt hNs ha hvolt hvols ha0 μ φ hφ_mono hconv hμ_green
  refine ⟨μ, hμ_prob, hμ_green, (fun _ => hμ_os), ?_, ?_⟩
  · intro R hR hLtR n f c hf
    let sigmaSq : ℕ → CylinderTestFunction Ls → ℝ := fun k h =>
      haveI := hM (φ k)
      haveI := hNs (φ k)
      ∫ ω : Configuration (AsymLatticeField (2 * M (φ k)) (Ns (φ k))),
        (ω (asymLatticeTestFnIso Lt Ls (2 * M (φ k)) (Ns (φ k)) (a (φ k))
          (cylinderToTorusEmbed Lt Ls h))) ^ 2
        ∂(latticeGaussianMeasureAsym (2 * M (φ k)) (Ns (φ k)) (a (φ k))
          mass (ha (φ k)) hmass)
    apply cylinderRPMatrixNonnegative_of_link_limit Lt Ls ν μ hν_prob hμ_prob hbc
      (fun k => a (φ k)) (ha0.comp hφ_atTop) sigmaSq K C hK_pos hC_pos
    · intro k h
      dsimp [sigmaSq]
      exact integral_nonneg fun _ => sq_nonneg _
    · intro k t h
      dsimp [sigmaSq]
      exact asymCylinderLatticeSecondMoment_smul Lt Ls
        (2 * M (φ k)) (Ns (φ k)) (a (φ k)) mass (ha (φ k)) hmass t h
    · intro hseq hseq0
      simpa [sigmaSq] using
        (asymCylinderLatticeSecondMoment_tendsto_zero_of_tendsto Lt Ls mass hmass
          (fun k => 2 * M (φ k)) (fun k => Ns (φ k)) (fun k => a (φ k))
          (fun k => by letI := hM (φ k); infer_instance)
          (fun k => hNs (φ k)) (fun k => ha (φ k)) hseq hseq0)
    · intro k h
      haveI := hM (φ k)
      haveI := hNs (φ k)
      obtain ⟨hint_torus, hle_torus⟩ := hcutoff
        (cylinderToTorusEmbed Lt Ls h) (2 * M (φ k)) (Ns (φ k))
        (a (φ k)) (ha (φ k)) (hvolt (φ k)) (hvols (φ k))
      obtain ⟨hint_cyl, heq⟩ := cylinderPullback_expMoment_eq Ls Lt (ν k) h hint_torus
      exact ⟨hint_cyl, heq.le.trans hle_torus⟩
    · intro k
      haveI := hM (φ k)
      haveI := hNs (φ k)
      exact asymTorusInteractingMeasureIso_cylinderLinkRPMatrix_span_noWrap
        Lt Ls P (a (φ k)) mass (ha (φ k)) hmass (M (φ k)) (Ns (φ k))
        (hvolt (φ k)) (hvols (φ k)) R hR hLtR n f c hf
  · exact ⟨φ, hφ_mono, hconv⟩

/-- Compatibility wrapper for the fixed-period UV construction.  The richer
certificate is available from
`asymTorusIso_measureHasGreenMomentBound_of_cutoff_withNoWrapRP_withUV`. -/
theorem asymTorusIso_measureHasGreenMomentBound_of_cutoff_withNoWrapRP
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (K C : ℝ) (hK_pos : 0 < K) (hC_pos : 0 < C)
    (hcutoff : ∀ (f : AsymTorusTestFunction Lt Ls) (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
      (a : ℝ) (ha : 0 < a), (Nt : ℝ) * a = Lt → (Ns : ℝ) * a = Ls →
      Integrable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
        Real.exp (|ω f|)) (asymTorusInteractingMeasureIso Lt Ls Nt Ns a P mass ha hmass) ∧
      ∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
        Real.exp (|ω f|) ∂(asymTorusInteractingMeasureIso Lt Ls Nt Ns a P mass ha hmass) ≤
      K * Real.exp (C * ∫ ω : Configuration (AsymLatticeField Nt Ns),
        (ω (asymLatticeTestFnIso Lt Ls Nt Ns a f)) ^ 2
        ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass)))
    (M Ns : ℕ → ℕ) (a : ℕ → ℝ)
    (hM : ∀ k, NeZero (M k)) (hNs : ∀ k, NeZero (Ns k)) (ha : ∀ k, 0 < a k)
    (hvolt : ∀ k, ((2 * M k : ℕ) : ℝ) * a k = Lt)
    (hvols : ∀ k, (Ns k : ℝ) * a k = Ls)
    (ha0 : Filter.Tendsto a Filter.atTop (nhds 0)) :
    ∃ (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls))),
      IsProbabilityMeasure μ ∧
      MeasureHasGreenMomentBound Ls mass hmass K C μ ∧
      (∀ hμ_prob : IsProbabilityMeasure μ,
        @AsymSatisfiesTorusOS Lt Ls hLt hLs μ hμ_prob) ∧
      CylinderMeasureNoWrapReflectionPositive Lt Ls
        (cylinderPullbackMeasure Lt Ls μ) := by
  obtain ⟨μ, hμ_prob, hμ_green, hμ_os, hμ_rp, _⟩ :=
    asymTorusIso_measureHasGreenMomentBound_of_cutoff_withNoWrapRP_withUV
      Lt Ls P mass hmass K C hK_pos hC_pos hcutoff M Ns a hM hNs ha hvolt hvols ha0
  exact ⟨μ, hμ_prob, hμ_green, hμ_os, hμ_rp⟩


theorem asymTorusIso_cylinderUniformGreenBound
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (K C : ℝ) (hK_pos : 0 < K) (hC_pos : 0 < C)
    (hUnif : ∀ (L : ℝ) [Fact (0 < L)] (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (ha : 0 < a),
      (Nt : ℝ) * a = L → (Ns : ℝ) * a = Ls → ∀ f : AsymTorusTestFunction L Ls,
      Integrable (fun ω : Configuration (AsymTorusTestFunction L Ls) =>
        Real.exp (|ω f|)) (asymTorusInteractingMeasureIso L Ls Nt Ns a P mass ha hmass) ∧
      ∫ ω : Configuration (AsymTorusTestFunction L Ls),
        Real.exp (|ω f|) ∂(asymTorusInteractingMeasureIso L Ls Nt Ns a P mass ha hmass) ≤
      K * Real.exp (C * ∫ ω : Configuration (AsymLatticeField Nt Ns),
        (ω (asymLatticeTestFnIso L Ls Nt Ns a f)) ^ 2
        ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass))) :
    ∃ (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
      (μ : ∀ n, Measure (Configuration (AsymTorusTestFunction (Lt n) Ls))),
      Filter.Tendsto Lt Filter.atTop Filter.atTop ∧
      (∀ n, IsProbabilityMeasure (μ n)) ∧
      AsymTorusSequenceHasUniformGreenMomentBound Ls mass hmass K C Lt hLt μ ∧
      AsymTorusSequenceHasCylinderOS2Symmetry Ls Lt hLt μ ∧
      (∀ n,
        CylinderMeasureNoWrapReflectionPositive (Lt n) Ls
          (@cylinderPullbackMeasure (Lt n) Ls (hLt n) hLs (μ n))) := by
  have hLs_pos : 0 < Ls := hLs.out
  set Lt : ℕ → ℝ := fun n => ((n : ℝ) + 1) * Ls with hLt_def
  have hLt_pos : ∀ n, 0 < Lt n := fun n => by rw [hLt_def]; positivity
  have hLtfact : ∀ n, Fact (0 < Lt n) := fun n => ⟨hLt_pos n⟩
  -- For each IR period Lt n, the UV continuum measure with the uniform Green bound
  have hbound : ∀ n, ∃ μ : Measure (Configuration (AsymTorusTestFunction (Lt n) Ls)),
      IsProbabilityMeasure μ ∧
      @MeasureHasGreenMomentBound Ls _ (Lt n) (hLtfact n) mass hmass K C μ ∧
      (∀ hμ_prob : IsProbabilityMeasure μ,
        @AsymSatisfiesTorusOS (Lt n) Ls (hLtfact n) hLs μ hμ_prob) ∧
      CylinderMeasureNoWrapReflectionPositive (Lt n) Ls
        (@cylinderPullbackMeasure (Lt n) Ls (hLtfact n) hLs μ) := by
    intro n
    haveI := hLtfact n
    -- Exactly-isotropic sequence with BOTH lattice extents even (Nt_k = 2(n+1)(k+1),
    -- Ns_k = 2(k+1), a_k = Ls/(2(k+1))): even time extent Nt is required for lattice reflection
    -- positivity (the reflection plane sits cleanly between sites), keeping Lt n = (n+1)·Ls fixed.
    exact asymTorusIso_measureHasGreenMomentBound_of_cutoff_withNoWrapRP
      (Lt n) Ls P mass hmass K C hK_pos hC_pos
      (fun f Nt Ns _ _ b hb hvt hvs => hUnif (Lt n) Nt Ns b hb hvt hvs f)
      (fun k => (n + 1) * (k + 1)) (fun k => 2 * (k + 1))
      (fun k => Ls / (2 * ((k : ℝ) + 1)))
      (fun k => ⟨by positivity⟩) (fun k => ⟨by positivity⟩) (fun k => by positivity)
      (fun k => by rw [hLt_def]; push_cast; field_simp)
      (fun k => by push_cast; field_simp)
      (by
        have h2 : Filter.Tendsto (fun k : ℕ => (Ls / 2) * (1 / ((k : ℝ) + 1)))
            Filter.atTop (nhds 0) := by
          simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (Ls / 2)
        have heq : (fun k : ℕ => Ls / (2 * ((k : ℝ) + 1))) =
            fun k : ℕ => (Ls / 2) * (1 / ((k : ℝ) + 1)) := by
          ext k; rw [mul_one_div, div_div]
        rw [heq]; exact h2)
  choose μ hμ_prob hμ_green hμ_os hμ_rp using hbound
  have hμ_os2 : AsymTorusSequenceHasCylinderOS2Symmetry Ls Lt hLtfact μ :=
    AsymTorusSequenceHasCylinderOS2Symmetry.of_torusOS
      Ls Lt hLtfact μ hμ_prob (fun n => hμ_os n (hμ_prob n))
  refine ⟨Lt, hLtfact, μ, ?_, hμ_prob, ?_, hμ_os2, hμ_rp⟩
  · -- Lt n = (n+1)·Ls → ∞
    rw [hLt_def]
    exact Filter.Tendsto.atTop_mul_const hLs_pos
      ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds)
  · exact AsymTorusSequenceHasUniformGreenMomentBound.of_forall Ls mass hmass
      K C Lt hLtfact μ hμ_green

/-- The uniform Green construction with its UV certificates retained.  The
selected measure `μ n` and the UV subsequence `φ n` are produced together, so
the bounded-continuous convergence certificate refers to the same measures
used by the Green, OS2, and no-wrap fields. -/
theorem asymTorusIso_cylinderUniformGreenBound_withUVFamily
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (K C : ℝ) (hK_pos : 0 < K) (hC_pos : 0 < C)
    (hUnif : ∀ (L : ℝ) [Fact (0 < L)] (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (ha : 0 < a),
      (Nt : ℝ) * a = L → (Ns : ℝ) * a = Ls → ∀ f : AsymTorusTestFunction L Ls,
      Integrable (fun ω : Configuration (AsymTorusTestFunction L Ls) =>
        Real.exp (|ω f|)) (asymTorusInteractingMeasureIso L Ls Nt Ns a P mass ha hmass) ∧
      ∫ ω : Configuration (AsymTorusTestFunction L Ls),
        Real.exp (|ω f|) ∂(asymTorusInteractingMeasureIso L Ls Nt Ns a P mass ha hmass) ≤
      K * Real.exp (C * ∫ ω : Configuration (AsymLatticeField Nt Ns),
        (ω (asymLatticeTestFnIso L Ls Nt Ns a f)) ^ 2
        ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass))) :
    ∃ (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
      (μ : ∀ n, Measure (Configuration (AsymTorusTestFunction (Lt n) Ls))),
      Filter.Tendsto Lt Filter.atTop Filter.atTop ∧
      (∀ n, IsProbabilityMeasure (μ n)) ∧
      AsymTorusSequenceHasUniformGreenMomentBound Ls mass hmass K C Lt hLt μ ∧
      AsymTorusSequenceHasCylinderOS2Symmetry Ls Lt hLt μ ∧
      (∀ n,
        CylinderMeasureNoWrapReflectionPositive (Lt n) Ls
          (@cylinderPullbackMeasure (Lt n) Ls (hLt n) hLs (μ n))) ∧
      (∃ (Nt Ns : ℕ → ℕ → ℕ) (a : ℕ → ℕ → ℝ) (φ : ℕ → ℕ → ℕ)
          (hNt : ∀ n k, NeZero (Nt n k))
          (hNs : ∀ n k, NeZero (Ns n k))
          (ha : ∀ n k, 0 < a n k),
        (∀ n k, (Nt n k : ℝ) * a n k = Lt n) ∧
        (∀ n k, (Ns n k : ℝ) * a n k = Ls) ∧
        (∀ n, Filter.Tendsto (a n) Filter.atTop (nhds 0)) ∧
        (∀ n, StrictMono (φ n)) ∧
        (∀ n
          (F : Configuration (AsymTorusTestFunction (Lt n) Ls) → ℝ),
          Continuous F → (∃ D, ∀ x, |F x| ≤ D) →
          Filter.Tendsto
            (fun j => ∫ ω, F ω ∂(
              letI : Fact (0 < Lt n) := hLt n
              letI : NeZero (Nt n (φ n j)) := hNt n (φ n j)
              letI : NeZero (Ns n (φ n j)) := hNs n (φ n j)
              asymTorusInteractingMeasureIso (Lt n) Ls
                (Nt n (φ n j)) (Ns n (φ n j)) (a n (φ n j))
                P mass (ha n (φ n j)) hmass))
            Filter.atTop (nhds (∫ ω, F ω ∂(μ n))))) := by
  have hLs_pos : 0 < Ls := hLs.out
  set Lt : ℕ → ℝ := fun n => ((n : ℝ) + 1) * Ls with hLt_def
  have hLt_pos : ∀ n, 0 < Lt n := fun n => by rw [hLt_def]; positivity
  have hLtfact : ∀ n, Fact (0 < Lt n) := fun n => ⟨hLt_pos n⟩
  let M : ℕ → ℕ → ℕ := fun n k => (n + 1) * (k + 1)
  let Nt : ℕ → ℕ → ℕ := fun n k => 2 * M n k
  let Ns : ℕ → ℕ → ℕ := fun _ k => 2 * (k + 1)
  let a : ℕ → ℕ → ℝ := fun _ k => Ls / (2 * ((k : ℝ) + 1))
  have hM : ∀ n k, NeZero (M n k) := by
    intro n k
    dsimp [M]
    exact ⟨by positivity⟩
  have hNs : ∀ n k, NeZero (Ns n k) := by
    intro n k
    dsimp [Ns]
    exact ⟨by positivity⟩
  have ha : ∀ n k, 0 < a n k := by
    intro n k
    dsimp [a]
    positivity
  have hscale_t : ∀ n k, (Nt n k : ℝ) * a n k = Lt n := by
    intro n k
    dsimp [Nt, M, a]
    rw [hLt_def]
    push_cast
    field_simp
  have hscale_s : ∀ n k, (Ns n k : ℝ) * a n k = Ls := by
    intro n k
    dsimp [Ns, a]
    push_cast
    field_simp
  have ha0 : ∀ n, Filter.Tendsto (a n) Filter.atTop (nhds 0) := by
    intro n
    dsimp [a]
    have h2 : Filter.Tendsto
        (fun k : ℕ => (Ls / 2) * (1 / ((k : ℝ) + 1)))
        Filter.atTop (nhds 0) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (Ls / 2)
    have heq : (fun k : ℕ => Ls / (2 * ((k : ℝ) + 1))) =
        fun k : ℕ => (Ls / 2) * (1 / ((k : ℝ) + 1)) := by
      ext k
      rw [mul_one_div, div_div]
    rw [heq]
    exact h2
  have hbound : ∀ n, ∃ μ : Measure (Configuration (AsymTorusTestFunction (Lt n) Ls)),
      IsProbabilityMeasure μ ∧
      @MeasureHasGreenMomentBound Ls _ (Lt n) (hLtfact n) mass hmass K C μ ∧
      (∀ hμ_prob : IsProbabilityMeasure μ,
        @AsymSatisfiesTorusOS (Lt n) Ls (hLtfact n) hLs μ hμ_prob) ∧
      CylinderMeasureNoWrapReflectionPositive (Lt n) Ls
        (@cylinderPullbackMeasure (Lt n) Ls (hLtfact n) hLs μ) ∧
      (∃ (ψ : ℕ → ℕ), StrictMono ψ ∧
        (∀ (F : Configuration (AsymTorusTestFunction (Lt n) Ls) → ℝ),
          Continuous F → (∃ D, ∀ x, |F x| ≤ D) →
          Filter.Tendsto
            (fun j => ∫ ω, F ω ∂(
              haveI := hLtfact n
              haveI := hM n (ψ j)
              haveI := hNs n (ψ j)
              asymTorusInteractingMeasureIso (Lt n) Ls
                (2 * M n (ψ j)) (Ns n (ψ j)) (a n (ψ j))
                  P mass (ha n (ψ j)) hmass))
            Filter.atTop (nhds (∫ ω, F ω ∂μ)))) := by
    intro n
    haveI := hLtfact n
    exact asymTorusIso_measureHasGreenMomentBound_of_cutoff_withNoWrapRP_withUV
      (Lt n) Ls P mass hmass K C hK_pos hC_pos
      (fun f Nt' Ns' _ _ b hb hvt hvs => hUnif (Lt n) Nt' Ns' b hb hvt hvs f)
      (fun k => M n k) (fun k => Ns n k) (fun k => a n k)
      (fun k => hM n k) (fun k => hNs n k) (fun k => ha n k)
      (fun k => hscale_t n k) (fun k => hscale_s n k) (ha0 n)
  choose μ hμ_prob hμ_green hμ_os hμ_rp hψ using hbound
  choose φ hφ hconv using hψ
  have hμ_os2 : AsymTorusSequenceHasCylinderOS2Symmetry Ls Lt hLtfact μ :=
    AsymTorusSequenceHasCylinderOS2Symmetry.of_torusOS
      Ls Lt hLtfact μ hμ_prob (fun n => hμ_os n (hμ_prob n))
  have hLt_tend : Filter.Tendsto Lt Filter.atTop Filter.atTop := by
    rw [hLt_def]
    exact Filter.Tendsto.atTop_mul_const hLs_pos
      ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds)
  have hφ_ne : ∀ n, StrictMono (φ n) := fun n => hφ n
  have hconv' : ∀ n
      (F : Configuration (AsymTorusTestFunction (Lt n) Ls) → ℝ),
      Continuous F → (∃ D, ∀ x, |F x| ≤ D) →
      Filter.Tendsto
        (fun j => ∫ ω, F ω ∂(
          haveI := hLtfact n
          haveI := hM n (φ n j)
          haveI := hNs n (φ n j)
          asymTorusInteractingMeasureIso (Lt n) Ls
            (2 * M n (φ n j)) (Ns n (φ n j)) (a n (φ n j))
              P mass (ha n (φ n j)) hmass))
        Filter.atTop (nhds (∫ ω, F ω ∂(μ n))) := by
    intro n F hF hD
    exact hconv n F hF hD
  refine ⟨Lt, hLtfact, μ, hLt_tend, hμ_prob,
    AsymTorusSequenceHasUniformGreenMomentBound.of_forall Ls mass hmass
      K C Lt hLtfact μ hμ_green, hμ_os2, hμ_rp, ?_⟩
  have hNt_global : ∀ n k, NeZero (Nt n k) := by
    intro n k
    dsimp [Nt]
    exact ⟨by positivity⟩
  refine ⟨Nt, Ns, a, φ, hNt_global, hNs, ha, ?_, ?_, ?_, hφ_ne, hconv'⟩
  · exact hscale_t
  · exact hscale_s
  · exact ha0

/-- **Route-B′ cylinder OS0/OS1/OS2/OS3 from a volume-uniform interacting exp-moment** (isotropic
construction).

The complete conditional closure: given the single volume-uniform interacting exp-moment bound
(the cluster-expansion input — see `asymTorusIso_cylinderUniformGreenBound`), the isotropic
`Z_Nt × Z_Ns` construction yields a cylinder `S¹(Ls) × ℝ` measure satisfying OS0 (analyticity),
OS2 (Euclidean invariance), and OS3 (reflection positivity). The uniform Green-moment bound — the
crux that the metric-mismatched square construction never supplied — and no-wrap RP are produced by
`asymTorusIso_cylinderUniformGreenBound`; its OS2 symmetry is proved from finite-lattice
translation/time-reflection equivariance, and compact-span RP is density-extended at the IR limit. -/
theorem routeBPrimeIso_cylinder_OS
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (K C : ℝ) (hK_pos : 0 < K) (hC_pos : 0 < C)
    (hUnif : ∀ (L : ℝ) [Fact (0 < L)] (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (ha : 0 < a),
      (Nt : ℝ) * a = L → (Ns : ℝ) * a = Ls → ∀ f : AsymTorusTestFunction L Ls,
      Integrable (fun ω : Configuration (AsymTorusTestFunction L Ls) =>
        Real.exp (|ω f|)) (asymTorusInteractingMeasureIso L Ls Nt Ns a P mass ha hmass) ∧
      ∫ ω : Configuration (AsymTorusTestFunction L Ls),
        Real.exp (|ω f|) ∂(asymTorusInteractingMeasureIso L Ls Nt Ns a P mass ha hmass) ≤
      K * Real.exp (C * ∫ ω : Configuration (AsymLatticeField Nt Ns),
        (ω (asymLatticeTestFnIso L Ls Nt Ns a f)) ^ 2
        ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass)))
    : ∃ (ν : Measure (Configuration (CylinderTestFunction Ls))),
    IsProbabilityMeasure ν ∧
    (∀ (n : ℕ) (J : Fin n → CylinderTestFunction Ls),
      AnalyticOnNhd ℂ (fun z : Fin n → ℂ =>
        ∫ ω, Complex.exp (∑ i, Complex.I * z i * ↑(ω (J i))) ∂ν) Set.univ) ∧
    (∀ (f : CylinderTestFunction Ls),
      ∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂ν =
      ∫ ω, Complex.exp (Complex.I * ↑(ω (cylinderTimeReflection Ls f))) ∂ν) ∧
    (∀ (τ : ℝ) (f : CylinderTestFunction Ls),
      ∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂ν =
      ∫ ω, Complex.exp (Complex.I * ↑(ω (cylinderTranslation Ls 0 τ f))) ∂ν) ∧
    (∀ (v : ℝ) (f : CylinderTestFunction Ls),
      ∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂ν =
      ∫ ω, Complex.exp (Complex.I * ↑(ω (cylinderSpatialTranslation Ls v f))) ∂ν) ∧
    (∀ (n : ℕ) (f : Fin n → ↥(cylinderPositiveTimeSubmodule Ls)) (c : Fin n → ℂ),
      0 ≤ (∑ i, ∑ j, c i * starRingEnd ℂ (c j) *
        ∫ ω, Complex.exp (Complex.I *
          ↑(ω ((f i : CylinderTestFunction Ls) -
            cylinderTimeReflection Ls (f j : CylinderTestFunction Ls)))) ∂ν).re) := by
  obtain ⟨Lt, hLt, μ, hLt_tend, hμ_prob, hμ_green, hμ_os2, hμ_noWrap⟩ :=
    asymTorusIso_cylinderUniformGreenBound Ls P mass hmass K C hK_pos hC_pos hUnif
  exact routeBPrime_cylinder_OS Ls mass hmass K C
    hK_pos hC_pos Lt hLt hLt_tend μ hμ_prob hμ_green
    (fun φ ν hν_prob hφ hcf K' C' q hK' hC' hq hExp => by
      letI : IsProbabilityMeasure ν := hν_prob
      exact cylinderMeasureReflectionPositive_of_noWrap_limit Ls
        (fun k => Lt (φ k)) (hLt_tend.comp hφ.tendsto_atTop)
        (fun k => @cylinderPullbackMeasure (Lt (φ k)) Ls
          (hLt (φ k)) hLs (μ (φ k)))
        ν hcf (fun k => hμ_noWrap (φ k)) K' C' hK' hC' q hq hExp)
    hμ_os2

/-- **Volume-uniform interacting exponential moment — quartic only.**

Restricted to `P.n = 4`. The all-`InteractionPolynomial` type is **false**:
the intended Newman producer `asymInteracting_mgf_gaussianDominated` fails for
an admissible one-site sextic, and the 2026-07-13 sign restriction does not
save `n ≥ 6`. Do **not** discharge this axiom. Do not restore the all-`P`
quantifier.

There exist constants `K, C > 0` (depending on `P`, `mass`, `Ls`, but **uniform in the time period
`L` and in the lattice `(Nt, Ns, a)`**) such that every isotropic-lattice interacting measure
`μ_int` on `Z_Nt × Z_Ns` (with `Nt·a = L`, `Ns·a = Ls`), pushed to the torus, has

  `∫ exp(|ω f|) dμ_int ≤ K · exp(C · σ²(f))`,    `σ²(f) = ∫ (ω·asymLatticeTestFnIso f)² dμ_{GFF}`.

This is retained as the `hUnif` input of `asymTorusIso_cylinderUniformGreenBound` /
`routeBPrimeIso_cylinder_OS`. It is not a textbook Newman instance on general even `P`.

Layer A (`asymInteracting_mgf_gaussianDominated`) is quartic-only; Layer B2
(`asymInteractingVariance_le_freeVariance_Lt_uniform`) is a torus wrapper of a
lattice axiom, not a discharge. The Layer C assembly in `AsymSignedSplit.lean`
inherits both and does not make this axiom a theorem.

    UPDATE 2026-07-13: the entrywise nonnegativity is now PROVED
    (`latticeCovarianceAsymGJ_pairing_nonneg`) and the thresholded
    `|f|`-form is a THEOREM
    (`asymInteracting_expMoment_volume_uniform_absForm_thresholded`, both in
    `AsymCovariancePositivity.lean`). That theorem still inherits the quartic
    Layer A axiom. This axiom's exact `C · Var_free(f)` form for signed `f`
    remains unrecovered; consumers should not treat either as a Newman
    discharge. -/
axiom asymInteracting_expMoment_volume_uniform
    (P : InteractionPolynomial) (hP : P.n = 4) (mass : ℝ) (hmass : 0 < mass) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ (L : ℝ) [Fact (0 < L)] (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (ha : 0 < a),
        (Nt : ℝ) * a = L → (Ns : ℝ) * a = Ls → ∀ f : AsymTorusTestFunction L Ls,
        Integrable (fun ω : Configuration (AsymTorusTestFunction L Ls) =>
          Real.exp (|ω f|)) (asymTorusInteractingMeasureIso L Ls Nt Ns a P mass ha hmass) ∧
        ∫ ω : Configuration (AsymTorusTestFunction L Ls),
          Real.exp (|ω f|) ∂(asymTorusInteractingMeasureIso L Ls Nt Ns a P mass ha hmass) ≤
        K * Real.exp (C * ∫ ω : Configuration (AsymLatticeField Nt Ns),
          (ω (asymLatticeTestFnIso L Ls Nt Ns a f)) ^ 2
          ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass))

/-- **Cylinder OS0/OS1/OS2/OS3 for the isotropic quartic P(φ)₂ construction.**

Quartic-only (`P.n = 4`). Consumes `asymInteracting_expMoment_volume_uniform`
at that restriction. This is not a Newman or DDJ producer; the historical
theorem name is retained for downstream compatibility. The all-`P` form would
call an inapplicable axiom (sextic counterexample). OS2 is
proved from the heterogeneous lattice construction, and reflection positivity
is carried through the no-wrap limit. -/
theorem cylinderIso_OS_of_RP_OS2
    (P : InteractionPolynomial) (hP : P.n = 4) (mass : ℝ) (hmass : 0 < mass) :
    ∃ (ν : Measure (Configuration (CylinderTestFunction Ls))),
    IsProbabilityMeasure ν ∧
    (∀ (n : ℕ) (J : Fin n → CylinderTestFunction Ls),
      AnalyticOnNhd ℂ (fun z : Fin n → ℂ =>
        ∫ ω, Complex.exp (∑ i, Complex.I * z i * ↑(ω (J i))) ∂ν) Set.univ) ∧
    (∀ (f : CylinderTestFunction Ls),
      ∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂ν =
      ∫ ω, Complex.exp (Complex.I * ↑(ω (cylinderTimeReflection Ls f))) ∂ν) ∧
    (∀ (τ : ℝ) (f : CylinderTestFunction Ls),
      ∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂ν =
      ∫ ω, Complex.exp (Complex.I * ↑(ω (cylinderTranslation Ls 0 τ f))) ∂ν) ∧
    (∀ (v : ℝ) (f : CylinderTestFunction Ls),
      ∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂ν =
      ∫ ω, Complex.exp (Complex.I * ↑(ω (cylinderSpatialTranslation Ls v f))) ∂ν) ∧
    (∀ (n : ℕ) (f : Fin n → ↥(cylinderPositiveTimeSubmodule Ls)) (c : Fin n → ℂ),
      0 ≤ (∑ i, ∑ j, c i * starRingEnd ℂ (c j) *
        ∫ ω, Complex.exp (Complex.I *
          ↑(ω ((f i : CylinderTestFunction Ls) -
            cylinderTimeReflection Ls (f j : CylinderTestFunction Ls)))) ∂ν).re) := by
  obtain ⟨K, C, hK_pos, hC_pos, hUnif⟩ :=
    asymInteracting_expMoment_volume_uniform Ls P hP mass hmass
  exact routeBPrimeIso_cylinder_OS Ls P mass hmass K C hK_pos hC_pos hUnif


end Pphi2

end
