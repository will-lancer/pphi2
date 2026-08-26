/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# UV continuum limit of the isotropic interacting measure (heterogeneous lattice)

The continuum (`a → 0`) limit of the isotropic-lattice interacting measures, pushed to the
asymmetric torus, at fixed `(Lt, Ls)`. This is the heterogeneous analogue of the square-via-
geometric-mean construction in `AsymTorus/AsymTorusInteractingLimit.lean`, now metric-correct.

## Main results (this file, in progress)

- `asymTorusIso_interacting_second_moment_density_transfer` — interacting `2`nd moment bounded
  by the free Gaussian `2`nd moment (Cauchy–Schwarz density transfer + Gaussian `4`th moment).

## Reference

Simon, *The P(φ)₂ Euclidean QFT*, Ch. VIII; Glimm–Jaffe, *Quantum Physics*, §19.
-/

import Pphi2.AsymTorus.AsymCutoffBound
import Pphi2.AsymTorus.AsymDDJSource
import Pphi2.AsymTorus.AsymDDJLocalMoment
import Pphi2.AsymTorus.AsymDDJSourceSampling
import Pphi2.AsymTorus.AsymDDJSourceLp
import Pphi2.AsymTorus.AsymDDJSourceBall
import Pphi2.AsymTorus.AsymDDJTiltedIntegrability
import Pphi2.AsymTorus.AsymDDJWeightedDecay
import Pphi2.AsymTorus.AsymIsoOS
import Pphi2.AsymTorus.AsymLinkReflectionRPLimit
import Pphi2.AsymTorus.AsymCovariancePositivity
import Pphi2.AsymTorus.AsymTiltedIBP
import Pphi2.AsymTorus.MomentBoundOS1
import Pphi2.IRLimit.IRTightness
import Pphi2.IRLimit.CylinderOS
import Pphi2.IRLimit.DDJSchwartzSecondDifference
import Pphi2.GeneralResults.WeakLimitMoment
import GaussianField.HypercontractiveNat
import GaussianField.Tightness
import GaussianField.ConfigurationEmbedding

noncomputable section

open MeasureTheory GaussianField

namespace Pphi2

variable (Lt Ls : ℝ) [hLt : Fact (0 < Lt)] [hLs : Fact (0 < Ls)]

/-- **Interacting second moment ≤ free Gaussian second moment** (heterogeneous lattice).

For each torus test function `f` and lattice `(Nt, Ns, a)` with `Nt·a = Lt`, `Ns·a = Ls`,

  `∫ (ω f)² dμ̃_int ≤ C · ∫ (ω g)² dμ_{GFF,asym}`,    `g = asymLatticeTestFnIso f`,

with `C = 3√K` (`K` the uniform Nelson constant). Cauchy–Schwarz density transfer
(`density_transfer_bound_iso`) plus the Gaussian `4`th-moment bound `∫(ωg)⁴ ≤ 9(∫(ωg)²)²`
(`gaussian_hypercontractive`). Heterogeneous analogue of
`asymTorus_interacting_second_moment_density_transfer`. -/
theorem asymTorusIso_interacting_second_moment_density_transfer
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : AsymTorusTestFunction Lt Ls) (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
      (a : ℝ) (ha : 0 < a), (Nt : ℝ) * a = Lt → (Ns : ℝ) * a = Ls →
    ∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
      (ω f) ^ 2 ∂(asymTorusInteractingMeasureIso Lt Ls Nt Ns a P mass ha hmass) ≤
    C * ∫ ω : Configuration (AsymLatticeField Nt Ns),
      (ω (asymLatticeTestFnIso Lt Ls Nt Ns a f)) ^ 2
        ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) := by
  obtain ⟨K, hK_pos, hK_bound⟩ :=
    asymNelson_exponential_estimate_iso P mass hmass Lt Ls hLt.out hLs.out
  refine ⟨3 * Real.sqrt K, mul_pos (by norm_num : (0 : ℝ) < 3)
    (Real.sqrt_pos_of_pos hK_pos), ?_⟩
  intro f Nt Ns _ _ a ha hvolt hvols
  set μ_int := interactingLatticeMeasureAsym Nt Ns P a mass ha hmass
  set μ_GFF := latticeGaussianMeasureAsym Nt Ns a mass ha hmass
  set ι := asymTorusEmbedLiftIso Lt Ls Nt Ns a
  set g := asymLatticeTestFnIso Lt Ls Nt Ns a f
  set T := latticeCovarianceAsymGJ Nt Ns a mass ha hmass
  have hμ_eq : μ_GFF = GaussianField.measure T := rfl
  have hι_meas : AEMeasurable ι μ_int :=
    (asymTorusEmbedLiftIso_measurable Lt Ls Nt Ns a).aemeasurable
  change ∫ ω, (ω f) ^ 2 ∂(Measure.map ι μ_int) ≤
    3 * Real.sqrt K * ∫ ω : Configuration (AsymLatticeField Nt Ns), (ω g) ^ 2 ∂μ_GFF
  rw [integral_map hι_meas
    ((configuration_eval_measurable f).pow_const 2).aestronglyMeasurable]
  have h_eval : ∀ ω : Configuration (AsymLatticeField Nt Ns),
      (ι ω) f = ω g := fun ω => asymTorusEmbedLiftIso_eval_eq Lt Ls Nt Ns a f ω
  simp_rw [h_eval]
  have hZ_ge_one := partitionFunctionAsym_ge_one Nt Ns P a mass ha hmass
  have hF_nn : ∀ ω : Configuration (AsymLatticeField Nt Ns), 0 ≤ (ω g) ^ 2 :=
    fun ω => sq_nonneg _
  have hF_meas : AEStronglyMeasurable (fun ω : Configuration (AsymLatticeField Nt Ns) =>
      (ω g) ^ 2) μ_GFF :=
    ((configuration_eval_measurable g).pow_const 2).aestronglyMeasurable
  have hF_sq_int : Integrable (fun ω : Configuration (AsymLatticeField Nt Ns) =>
      ((ω g) ^ 2) ^ 2) μ_GFF := by
    have h4 : MemLp (fun ω : Configuration (AsymLatticeField Nt Ns) => ω g) 4 μ_GFF := by
      exact_mod_cast pairing_memLp T g 4
    have hmem := h4.norm_rpow (p := (4 : ENNReal))
      (by norm_num : (4 : ENNReal) ≠ 0) (by norm_num : (4 : ENNReal) ≠ ⊤)
    rw [memLp_one_iff_integrable] at hmem
    have h_int : Integrable (fun ω : Configuration (AsymLatticeField Nt Ns) =>
        ‖ω g‖ ^ (4 : ℕ)) μ_GFF := by
      refine hmem.congr (Filter.Eventually.of_forall fun ω => ?_)
      simp [ENNReal.toReal_ofNat]
    exact h_int.congr (Filter.Eventually.of_forall fun ω => by
      dsimp only
      rw [Real.norm_eq_abs]
      conv_rhs => rw [show ω g ^ 2 = |ω g| ^ 2 from (sq_abs _).symm]
      ring)
  have h_dt := density_transfer_bound_iso Nt Ns P a mass ha hmass K hK_pos
    (hK_bound Nt Ns a ha hvolt hvols)
    hZ_ge_one (fun ω => (ω g) ^ 2) hF_nn hF_meas hF_sq_int
  have h_int_rpow_eq : ∫ ω, (fun ω => (ω g) ^ 2) ω ^ (2 : ℝ) ∂μ_GFF =
      ∫ ω, ((ω g) ^ 2) ^ 2 ∂μ_GFF := by
    congr 1; ext ω; exact Real.rpow_natCast ((ω g) ^ 2) 2
  have h_second_nn : 0 ≤ ∫ ω, (ω g) ^ 2 ∂μ_GFF :=
    integral_nonneg fun ω => sq_nonneg _
  have h_fourth_le : ∫ ω, ((ω g) ^ 2) ^ 2 ∂μ_GFF ≤
      9 * (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ 2 := by
    have h_eq4 : ∀ ω : Configuration (AsymLatticeField Nt Ns),
        ((ω g) ^ 2) ^ 2 = |ω g| ^ 4 := by
      intro ω; rw [show ω g ^ 2 = |ω g| ^ 2 from (sq_abs _).symm]; ring
    simp_rw [h_eq4]
    have h_hyper := gaussian_hypercontractive T g 1 4
      (by norm_num : (2 : ℝ) ≤ 4) 2 (by norm_num : 1 ≤ 2)
      (by norm_num : (4 : ℝ) = 2 * ↑2)
    have h_lhs_eq : ∫ ω, |ω g| ^ 4 ∂μ_GFF =
        ∫ ω, |ω g| ^ ((4 : ℝ) * ↑(1 : ℕ)) ∂(GaussianField.measure T) := by
      rw [hμ_eq]; congr 1; ext ω
      simp only [Nat.cast_one, mul_one]; exact (Real.rpow_natCast _ 4).symm
    rw [h_lhs_eq]
    have h_coeff : ((4 : ℝ) - 1) ^ ((4 : ℝ) * ↑(1 : ℕ) / 2) = 9 := by
      simp only [Nat.cast_one, mul_one]
      rw [show (4 : ℝ) / 2 = ↑(2 : ℕ) from by norm_num, Real.rpow_natCast]; norm_num
    have h_exp_eq' : (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ ((4 : ℝ) / 2) =
        (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ 2 := by
      rw [show (4 : ℝ) / 2 = ↑(2 : ℕ) from by norm_num, Real.rpow_natCast]
    have h_int_2_eq : ∫ ω, |ω g| ^ (2 * 1) ∂(GaussianField.measure T) =
        ∫ ω, (ω g) ^ 2 ∂μ_GFF := by
      rw [hμ_eq]; congr 1; ext ω; simp [sq_abs]
    have h_hyper' : ∫ ω, |ω g| ^ ((4 : ℝ) * ↑(1 : ℕ)) ∂(GaussianField.measure T) ≤
        ((4 : ℝ) - 1) ^ ((4 : ℝ) * ↑(1 : ℕ) / 2) *
        (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ ((4 : ℝ) / 2) := by
      have := h_hyper; rwa [h_int_2_eq] at this
    calc ∫ ω, |ω g| ^ ((4 : ℝ) * ↑(1 : ℕ)) ∂(GaussianField.measure T)
        ≤ ((4 : ℝ) - 1) ^ ((4 : ℝ) * ↑(1 : ℕ) / 2) *
          (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ ((4 : ℝ) / 2) := h_hyper'
      _ = 9 * (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ 2 := by rw [h_coeff, h_exp_eq']
  have h_fourth_nn : (0 : ℝ) ≤ ∫ ω, ((ω g) ^ 2) ^ 2 ∂μ_GFF :=
    integral_nonneg fun ω => by positivity
  have h_4th_bound : (∫ ω, (fun ω => (ω g) ^ 2) ω ^ (2 : ℝ) ∂μ_GFF) ^ (1 / 2 : ℝ) ≤
      3 * ∫ ω, (ω g) ^ 2 ∂μ_GFF := by
    rw [h_int_rpow_eq]
    calc (∫ ω, ((ω g) ^ 2) ^ 2 ∂μ_GFF) ^ (1 / 2 : ℝ)
        ≤ (9 * (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ 2) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow h_fourth_nn h_fourth_le (by norm_num : (0 : ℝ) ≤ 1 / 2)
      _ = 3 * ∫ ω, (ω g) ^ 2 ∂μ_GFF := by
          rw [show 9 * (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ 2 =
            (3 * ∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ 2 from by ring]
          rw [← Real.sqrt_eq_rpow, Real.sqrt_sq
            (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) h_second_nn)]
  have hK_sqrt : K ^ (1 / 2 : ℝ) = Real.sqrt K := (Real.sqrt_eq_rpow K).symm
  calc ∫ ω, (ω g) ^ 2 ∂μ_int
      ≤ K ^ (1 / 2 : ℝ) * (∫ ω, (fun ω => (ω g) ^ 2) ω ^ (2 : ℝ) ∂μ_GFF) ^ (1 / 2 : ℝ) := h_dt
    _ ≤ K ^ (1 / 2 : ℝ) * (3 * ∫ ω, (ω g) ^ 2 ∂μ_GFF) :=
        mul_le_mul_of_nonneg_left h_4th_bound (Real.rpow_nonneg hK_pos.le _)
    _ = Real.sqrt K * (3 * ∫ ω, (ω g) ^ 2 ∂μ_GFF) := by rw [hK_sqrt]
    _ = 3 * Real.sqrt K * ∫ ω, (ω g) ^ 2 ∂μ_GFF := by ring

/-- **Uniform second moment along an isotropic sequence.** For any test function `f` and any
isotropic lattice sequence `(Nt k, Ns k, a k)` with `Nt k·a k = Lt`, `Ns k·a k = Ls`, `a k → 0`,
the interacting second moment `∫ (ω f)² dμ̃_int,k` is bounded uniformly in `k`.

The free Gaussian second moment `∫ (ω g_k)² dμ_{GFF,k} = ⟪T_k g_k, T_k g_k⟫` *converges* (to
`asymTorusContinuumGreen f f`, by `second_moment_asym_tendsto`) hence is bounded; the density
transfer then bounds the interacting moment by `3√K` times it. -/
theorem asymTorusIso_interacting_second_moment_uniform
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (Nt Ns : ℕ → ℕ) (a : ℕ → ℝ)
    (hNt : ∀ k, NeZero (Nt k)) (hNs : ∀ k, NeZero (Ns k)) (ha : ∀ k, 0 < a k)
    (hvolt : ∀ k, (Nt k : ℝ) * a k = Lt) (hvols : ∀ k, (Ns k : ℝ) * a k = Ls)
    (ha0 : Filter.Tendsto a Filter.atTop (nhds 0))
    (f : AsymTorusTestFunction Lt Ls) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ,
      ∫ ω, (ω f) ^ 2 ∂(haveI := hNt k; haveI := hNs k
        asymTorusInteractingMeasureIso Lt Ls (Nt k) (Ns k) (a k) P mass (ha k) hmass) ≤ C := by
  obtain ⟨Cdt, hCdt_pos, hCdt⟩ :=
    asymTorusIso_interacting_second_moment_density_transfer Lt Ls P mass hmass
  -- The free Gaussian second moment along the sequence
  set σ2 : ℕ → ℝ := fun k => haveI := hNt k; haveI := hNs k
    ∫ ω : Configuration (AsymLatticeField (Nt k) (Ns k)),
      (ω (asymLatticeTestFnIso Lt Ls (Nt k) (Ns k) (a k) f)) ^ 2
      ∂(latticeGaussianMeasureAsym (Nt k) (Ns k) (a k) mass (ha k) hmass) with hσ2_def
  -- σ2 k = covariance(T_k) g_k g_k → converges, hence bounded
  have hσ2_eq : σ2 = fun k => haveI := hNt k; haveI := hNs k
      covariance (latticeCovarianceAsymGJ (Nt k) (Ns k) (a k) mass (ha k) hmass)
        (asymLatticeTestFnIso Lt Ls (Nt k) (Ns k) (a k) f)
        (asymLatticeTestFnIso Lt Ls (Nt k) (Ns k) (a k) f) := by
    funext k; haveI := hNt k; haveI := hNs k
    rw [hσ2_def]
    exact second_moment_eq_covariance _ _
  have hσ2_tendsto : Filter.Tendsto σ2 Filter.atTop
      (nhds (asymTorusContinuumGreen Lt Ls mass hmass f f)) := by
    rw [hσ2_eq]
    exact second_moment_asym_tendsto Lt Ls mass hmass Nt Ns a hNt hNs ha hvolt hvols ha0 f f
  obtain ⟨Cg, hCg⟩ := hσ2_tendsto.bddAbove_range
  have hσ2_le : ∀ k, σ2 k ≤ Cg := fun k => hCg (Set.mem_range_self k)
  have hσ2_nn : ∀ k, 0 ≤ σ2 k := by
    intro k; rw [hσ2_def]; exact integral_nonneg fun ω => sq_nonneg _
  have hCg_nn : 0 ≤ Cg := le_trans (hσ2_nn 0) (hσ2_le 0)
  refine ⟨Cdt * Cg + 1, by positivity, fun k => ?_⟩
  haveI := hNt k; haveI := hNs k
  calc ∫ ω, (ω f) ^ 2
        ∂(asymTorusInteractingMeasureIso Lt Ls (Nt k) (Ns k) (a k) P mass (ha k) hmass)
      ≤ Cdt * σ2 k := hCdt f (Nt k) (Ns k) (a k) (ha k) (hvolt k) (hvols k)
    _ ≤ Cdt * Cg := mul_le_mul_of_nonneg_left (hσ2_le k) hCdt_pos.le
    _ ≤ Cdt * Cg + 1 := by linarith

/-- The isotropic-lattice interacting measure pushed to the torus is a probability measure. -/
theorem asymTorusInteractingMeasureIso_isProbability (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a : ℝ) (P : InteractionPolynomial) (mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    IsProbabilityMeasure (asymTorusInteractingMeasureIso Lt Ls Nt Ns a P mass ha hmass) := by
  haveI := interactingLatticeMeasureAsym_isProbability Nt Ns P a mass ha hmass
  exact Measure.isProbabilityMeasure_map
    (asymTorusEmbedLiftIso_measurable Lt Ls Nt Ns a).aemeasurable

/-- The squared evaluation `(ω f)²` is integrable under the isotropic interacting torus measure.
Pushes through the embedding to `(ω g)²` under `interactingLatticeMeasureAsym`, then bounds the
Boltzmann-weighted Gaussian integral via `pairing_memLp` + bounded-below interaction. -/
theorem asymTorusInteractingMeasureIso_sq_integrable (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a : ℝ) (P : InteractionPolynomial) (mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f : AsymTorusTestFunction Lt Ls) :
    Integrable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) => (ω f) ^ 2)
      (asymTorusInteractingMeasureIso Lt Ls Nt Ns a P mass ha hmass) := by
  unfold asymTorusInteractingMeasureIso
  rw [integrable_map_measure
    ((configuration_eval_measurable f).pow_const 2).aestronglyMeasurable
    (asymTorusEmbedLiftIso_measurable Lt Ls Nt Ns a).aemeasurable]
  have h_eq : (fun ω : Configuration (AsymTorusTestFunction Lt Ls) => (ω f) ^ 2) ∘
      (asymTorusEmbedLiftIso Lt Ls Nt Ns a) =
      fun ω : Configuration (AsymLatticeField Nt Ns) =>
        (ω (asymLatticeTestFnIso Lt Ls Nt Ns a f)) ^ 2 := by
    ext ω; simp [Function.comp, asymTorusEmbedLiftIso_eval_eq Lt Ls Nt Ns a f ω]
  rw [h_eq]
  set g := asymLatticeTestFnIso Lt Ls Nt Ns a f
  set μ_GFF := latticeGaussianMeasureAsym Nt Ns a mass ha hmass
  set bw := boltzmannWeightAsym Nt Ns P a mass
  obtain ⟨B, hB⟩ := interactionFunctionalAsym_bounded_below Nt Ns P a mass ha hmass
  have hZ := partitionFunctionAsym_pos Nt Ns P a mass ha hmass
  suffices h : Integrable (fun ω : Configuration (AsymLatticeField Nt Ns) => (ω g) ^ 2)
      (μ_GFF.withDensity (fun ω => ENNReal.ofReal (bw ω))) by
    unfold interactingLatticeMeasureAsym
    exact h.smul_measure (ENNReal.inv_ne_top.mpr ((ENNReal.ofReal_pos.mpr hZ).ne'))
  have hf_meas : Measurable (fun ω : Configuration (AsymLatticeField Nt Ns) =>
      ENNReal.ofReal (bw ω)) :=
    ENNReal.measurable_ofReal.comp
      ((interactionFunctionalAsym_measurable Nt Ns P a mass).neg.exp)
  apply (integrable_withDensity_iff hf_meas
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
  have hbw_simp : ∀ ω : Configuration (AsymLatticeField Nt Ns),
      (ENNReal.ofReal (bw ω)).toReal = bw ω :=
    fun ω => ENNReal.toReal_ofReal (le_of_lt (boltzmannWeightAsym_pos Nt Ns P a mass ω))
  simp_rw [hbw_simp]
  have h_sq_int : Integrable (fun ω : Configuration (AsymLatticeField Nt Ns) => (ω g) ^ 2) μ_GFF :=
    (pairing_memLp (latticeCovarianceAsymGJ Nt Ns a mass ha hmass) g 2).integrable_sq
  apply (h_sq_int.mul_const (Real.exp B)).mono
  · exact ((configuration_eval_measurable g).pow_const 2).aestronglyMeasurable.mul
      (Measurable.aestronglyMeasurable
        (interactionFunctionalAsym_measurable Nt Ns P a mass).neg.exp)
  · exact Filter.Eventually.of_forall fun ω => by
      simp only [Real.norm_eq_abs]
      have h1 : 0 ≤ (ω g) ^ 2 := sq_nonneg _
      have h2 : 0 < bw ω := boltzmannWeightAsym_pos Nt Ns P a mass ω
      have h3 : bw ω ≤ Real.exp B := by
        change Real.exp (-interactionFunctionalAsym Nt Ns P a mass ω) ≤ Real.exp B
        exact Real.exp_le_exp_of_le (by linarith [hB ω])
      rw [abs_of_nonneg (mul_nonneg h1 (le_of_lt h2)),
          abs_of_nonneg (mul_nonneg h1 (le_of_lt (Real.exp_pos B)))]
      exact mul_le_mul_of_nonneg_left h3 h1

/-- **Existence of the isotropic UV continuum limit.** Along any isotropic lattice sequence
`(Nt k, Ns k, a k)` with `Nt k·a k = Lt`, `Ns k·a k = Ls`, `a k → 0`, a subsequence of the
interacting torus measures converges weakly to a probability measure `μ` on
`Configuration (AsymTorusTestFunction Lt Ls)`.

Tightness from the uniform second moment (`asymTorusIso_interacting_second_moment_uniform`) via
Mitoma–Chebyshev (`configuration_tight_of_uniform_second_moments`), then Prokhorov extraction.
Heterogeneous analogue of `asymTorusInteractingLimit_exists`. -/
theorem asymTorusIso_interacting_limit_exists
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (Nt Ns : ℕ → ℕ) (a : ℕ → ℝ)
    (hNt : ∀ k, NeZero (Nt k)) (hNs : ∀ k, NeZero (Ns k)) (ha : ∀ k, 0 < a k)
    (hvolt : ∀ k, (Nt k : ℝ) * a k = Lt) (hvols : ∀ k, (Ns k : ℝ) * a k = Ls)
    (ha0 : Filter.Tendsto a Filter.atTop (nhds 0)) :
    ∃ (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
      (_ : IsProbabilityMeasure μ) (φ : ℕ → ℕ) (_ : StrictMono φ),
    ∀ (F : Configuration (AsymTorusTestFunction Lt Ls) → ℝ),
      Continuous F → (∃ C, ∀ x, |F x| ≤ C) →
        Filter.Tendsto (fun n => ∫ ω, F ω ∂(haveI := hNt (φ n); haveI := hNs (φ n)
            asymTorusInteractingMeasureIso Lt Ls (Nt (φ n)) (Ns (φ n)) (a (φ n)) P mass
              (ha (φ n)) hmass))
          Filter.atTop (nhds (∫ ω, F ω ∂μ)) := by
  set ν : ℕ → Measure (Configuration (AsymTorusTestFunction Lt Ls)) := fun k =>
    haveI := hNt k; haveI := hNs k
    asymTorusInteractingMeasureIso Lt Ls (Nt k) (Ns k) (a k) P mass (ha k) hmass with hν_def
  have hν_prob : ∀ k, IsProbabilityMeasure (ν k) := fun k => by
    haveI := hNt k; haveI := hNs k
    exact asymTorusInteractingMeasureIso_isProbability Lt Ls (Nt k) (Ns k) (a k) P mass (ha k) hmass
  obtain ⟨φ, μ, hφ_mono, hμ_prob, hconv⟩ := prokhorov_configuration ν hν_prob
    (fun ε hε => by
      refine configuration_tight_of_uniform_second_moments ν hν_prob
        (fun f k => by
          haveI := hNt k; haveI := hNs k
          exact asymTorusInteractingMeasureIso_sq_integrable Lt Ls (Nt k) (Ns k) (a k)
            P mass (ha k) hmass f)
        (fun f => by
          obtain ⟨C, _, hC⟩ := asymTorusIso_interacting_second_moment_uniform Lt Ls P mass hmass
            Nt Ns a hNt hNs ha hvolt hvols ha0 f
          exact ⟨C, fun k => hC k⟩)
        ε hε)
  exact ⟨μ, hμ_prob, φ, hφ_mono, hconv⟩

/-- Bounded-continuous convergence on asymmetric-torus configurations transfers
an exponential-moment estimate directly to the cylinder pullback measures.

This is the source-independent weak-limit adapter used by the direct cylinder
route.  Its bound may vary with the cutoff index; no comparison with a torus
Green function is required. -/
theorem cylinderPullbackMeasure_exponential_moment_of_tendsto_bc
    (μseq : ℕ → Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    (hμseq_prob : ∀ k, IsProbabilityMeasure (μseq k))
    (hμ_prob : IsProbabilityMeasure μ)
    (hbc : ∀ (g : Configuration (AsymTorusTestFunction Lt Ls) → ℝ),
      Continuous g → (∃ B, ∀ x, |g x| ≤ B) →
      Filter.Tendsto (fun k ⇒ ∫ ω, g ω ∂(μseq k)) Filter.atTop
        (nhds (∫ ω, g ω ∂μ)))
    (f : CylinderTestFunction Ls)
    (B : ℕ → ℝ) (Binf : ℝ)
    (hB : Filter.Tendsto B Filter.atTop (nhds Binf))
    (h_unif : ∀ k,
      Integrable (fun ω : Configuration (CylinderTestFunction Ls) ⇒
        Real.exp (|ω f|)) (cylinderPullbackMeasure Lt Ls (μseq k)) ∧
      ∫ ω : Configuration (CylinderTestFunction Ls),
        Real.exp (|ω f|) ∂(cylinderPullbackMeasure Lt Ls (μseq k)) ≤ B k) :
    Integrable (fun ω : Configuration (CylinderTestFunction Ls) ⇒
      Real.exp (|ω f|)) (cylinderPullbackMeasure Lt Ls μ) ∧
    ∫ ω : Configuration (CylinderTestFunction Ls),
      Real.exp (|ω f|) ∂(cylinderPullbackMeasure Lt Ls μ) ≤ Binf := by
  letI : IsProbabilityMeasure μ := hμ_prob
  let F : AsymTorusTestFunction Lt Ls := cylinderToTorusEmbed Lt Ls f
  have hmeas : Measurable (cylinderPullback Lt Ls) :=
    configuration_measurable_of_eval_measurable _
      (fun φ ⇒ configuration_eval_measurable _)
  have hexp_sm : StronglyMeasurable
      (fun ω : Configuration (CylinderTestFunction Ls) ⇒ Real.exp (|ω f|)) :=
    (Real.measurable_exp.comp
      (configuration_eval_measurable f).abs).stronglyMeasurable
  have h_unif_torus : ∀ k,
      Integrable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) ⇒
        Real.exp (|ω F|)) (μseq k) ∧
      ∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
        Real.exp (|ω F|) ∂(μseq k) ≤ B k := by
    intro k
    obtain ⟨hint_cyl, hle_cyl⟩ := h_unif k
    have hint_comp : Integrable
        ((fun ω : Configuration (CylinderTestFunction Ls) ⇒ Real.exp (|ω f|)) ∘
          cylinderPullback Lt Ls) (μseq k) := by
      rw [← integrable_map_measure hexp_sm.aestronglyMeasurable hmeas.aemeasurable]
      exact hint_cyl
    have hint_torus : Integrable
        (fun ω : Configuration (AsymTorusTestFunction Lt Ls) ⇒
          Real.exp (|ω F|)) (μseq k) := by
      refine hint_comp.congr (Filter.Eventually.of_forall fun ω ⇒ ?_)
      simp [F, Function.comp_def, cylinderPullback_eval]
    have heq :
        ∫ ω : Configuration (CylinderTestFunction Ls),
            Real.exp (|ω f|) ∂(cylinderPullbackMeasure Lt Ls (μseq k)) =
          ∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
            Real.exp (|ω F|) ∂(μseq k) := by
      unfold cylinderPullbackMeasure
      rw [integral_map_of_stronglyMeasurable hmeas hexp_sm]
      simp [F, Function.comp_def, cylinderPullback_eval]
    refine ⟨hint_torus, ?_⟩
    calc
      ∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
          Real.exp (|ω F|) ∂(μseq k) =
          ∫ ω : Configuration (CylinderTestFunction Ls),
            Real.exp (|ω f|) ∂(cylinderPullbackMeasure Lt Ls (μseq k)) := heq.symm
      _ ≤ B k := hle_cyl
  obtain ⟨hint_torus, hle_torus⟩ := weakLimit_exponential_moment
    μseq hμseq_prob μ hbc F B Binf hB h_unif_torus
  obtain ⟨hint_cyl, heq⟩ :=
    cylinderPullback_expMoment_eq Ls Lt μ f hint_torus
  exact ⟨hint_cyl, heq.le.trans hle_torus⟩

/-! ## Bridge: raw fixed-period sampling bound ⟹ cylinder bound -/

/-! ### Raw finite-grid sampling -/

private theorem asym_zmod_sum_eq_range (N : ℕ) [NeZero N] (g : ℕ → ℝ) :
    ∑ x : ZMod N, g (ZMod.val x) = ∑ n ∈ Finset.range N, g n := by
  rw [show ∑ x : ZMod N, g (ZMod.val x) = ∑ n : Fin N, g n.val
    from Fintype.sum_bijective
      (fun (x : ZMod N) =>
        (⟨ZMod.val x, ZMod.val_lt x⟩ : Fin N))
      ⟨fun a b h => ZMod.val_injective N (Fin.mk.inj h),
       fun ⟨n, hn⟩ =>
        ⟨(n : ZMod N), by
          ext; exact ZMod.val_natCast_of_lt hn⟩⟩
      _ _ (fun _ => rfl),
    ← Finset.sum_range (f := g)]

private theorem asym_circleRestriction_inner_tendsto
    (L : ℝ) [Fact (0 < L)]
    (N : ℕ → ℕ) (hN : ∀ k, NeZero (N k))
    (hNtop : Tendsto N atTop atTop)
    (f g : SmoothMap_Circle L ℝ) :
    Tendsto
      (fun k =>
        letI : NeZero (N k) := hN k
        ∑ z : ZMod (N k),
          circleRestriction L (N k) f z * circleRestriction L (N k) g z)
      atTop (nhds (∫ x in Set.Icc 0 L, f x * g x)) := by
  have hN1 : Tendsto (fun k => N k - 1) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    obtain ⟨K, hK⟩ := tendsto_atTop_atTop.mp hNtop (b + 1)
    exact ⟨K, fun k hk => by
      have hkb := hK k hk
      omega⟩
  have hNsucc : ∀ k, (N k - 1) + 1 = N k := fun k =>
    Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (hN k).out)
  let hfg : ℝ → ℝ := fun x => f x * g x
  have hfg_cont : Continuous hfg := f.continuous.mul g.continuous
  have hfg_per : Function.Periodic hfg L := f.periodic.mul g.periodic
  have hriem := riemann_sum_periodic_tendsto L hfg hfg_cont hfg_per
  have hcomp := hriem.comp hN1
  have hrewrite :
      (fun k =>
        letI : NeZero (N k) := hN k
        ∑ z : ZMod (N k),
          circleRestriction L (N k) f z * circleRestriction L (N k) g z) =
      (fun k =>
        ∑ n ∈ Finset.range (N k - 1 + 1),
          (L / (↑(N k - 1 + 1) : ℝ)) *
            hfg ((n : ℝ) * L / (↑(N k - 1 + 1) : ℝ))) := by
    funext k
    letI : NeZero (N k) := hN k
    rw [hNsucc k]
    calc
      ∑ z : ZMod (N k),
          circleRestriction L (N k) f z * circleRestriction L (N k) g z =
          ∑ z : ZMod (N k),
            (L / (N k : ℝ)) *
              (f (circlePoint L (N k) z) * g (circlePoint L (N k) z)) := by
        apply Finset.sum_congr rfl
        intro z hz
        simp only [circleRestriction_apply, circleSpacing_eq]
        have hLN : 0 ≤ L / (N k : ℝ) :=
          (div_pos (Fact.out : (0 : ℝ) < L)
            (Nat.cast_pos.mpr (NeZero.pos (N k)))).le
        rw [show Real.sqrt (L / (N k : ℝ)) * f (circlePoint L (N k) z) *
              (Real.sqrt (L / (N k : ℝ)) * g (circlePoint L (N k) z)) =
            (Real.sqrt (L / (N k : ℝ)) * Real.sqrt (L / (N k : ℝ))) *
              (f (circlePoint L (N k) z) * g (circlePoint L (N k) z)) by ring,
          Real.mul_self_sqrt hLN]
      _ = ∑ n ∈ Finset.range (N k),
          (L / (N k : ℝ)) *
            hfg ((n : ℝ) * L / (N k : ℝ)) := by
        rw [asym_zmod_sum_eq_range]
        apply Finset.sum_congr rfl
        intro n hn
        simp [hfg, circlePoint]
      _ = ∑ n ∈ Finset.range (N k - 1 + 1),
          (L / (↑(N k - 1 + 1) : ℝ)) *
            hfg ((n : ℝ) * L / (↑(N k - 1 + 1) : ℝ)) := by
        rw [hNsucc k]
  rw [hrewrite]
  simpa only [Function.comp_def] using hcomp

private theorem asym_basis_pair_tendsto
    (Lt Ls : ℝ) [Fact (0 < Lt)] [Fact (0 < Ls)]
    (Nt Ns : ℕ → ℕ) (a : ℕ → ℝ)
    (hNt : ∀ k, NeZero (Nt k)) (hNs : ∀ k, NeZero (Ns k))
    (hNt_top : Tendsto Nt atTop atTop)
    (hNs_top : Tendsto Ns atTop atTop)
    (m n : ℕ) :
    Tendsto
      (fun k =>
        letI : NeZero (Nt k) := hNt k
        letI : NeZero (Ns k) := hNs k
        ∑ x : AsymLatticeSites (Nt k) (Ns k),
          evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x
              (RapidDecaySeq.basisVec m) *
            evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x
              (RapidDecaySeq.basisVec n))
      atTop (nhds (if m = n then 1 else 0)) := by
  let mt := (Nat.unpair m).1
  let ms := (Nat.unpair m).2
  let nt := (Nat.unpair n).1
  let ns := (Nat.unpair n).2
  let bt : SmoothMap_Circle Lt ℝ := DyninMityaginSpace.basis mt
  let bs : SmoothMap_Circle Ls ℝ := DyninMityaginSpace.basis ms
  let ct : SmoothMap_Circle Lt ℝ := DyninMityaginSpace.basis nt
  let cs : SmoothMap_Circle Ls ℝ := DyninMityaginSpace.basis ns
  have htime0 :
      (∫ x in Set.Icc 0 Lt, bt x * ct x) =
        if mt = nt then 1 else 0 := by
    rw [show bt = SmoothMap_Circle.fourierBasis mt from
          dm_basis_eq_fourierBasis (L := Lt) mt,
      show ct = SmoothMap_Circle.fourierBasis nt from
          dm_basis_eq_fourierBasis (L := Lt) nt]
    rw [show (∫ x in Set.Icc 0 Lt,
        SmoothMap_Circle.fourierBasis mt x *
          SmoothMap_Circle.fourierBasis nt x) =
        ∫ x in Set.Icc 0 Lt,
          SmoothMap_Circle.fourierBasis nt x *
            SmoothMap_Circle.fourierBasis mt x by
          congr 1; funext x; ring]
    exact SmoothMap_Circle.fourierCoeffReal_fourierBasis (L := Lt) mt nt
  have hspace0 :
      (∫ x in Set.Icc 0 Ls, bs x * cs x) =
        if ms = ns then 1 else 0 := by
    rw [show bs = SmoothMap_Circle.fourierBasis ms from
          dm_basis_eq_fourierBasis (L := Ls) ms,
      show cs = SmoothMap_Circle.fourierBasis ns from
          dm_basis_eq_fourierBasis (L := Ls) ns]
    rw [show (∫ x in Set.Icc 0 Ls,
        SmoothMap_Circle.fourierBasis ms x *
          SmoothMap_Circle.fourierBasis ns x) =
        ∫ x in Set.Icc 0 Ls,
          SmoothMap_Circle.fourierBasis ns x *
            SmoothMap_Circle.fourierBasis ms x by
          congr 1; funext x; ring]
    exact SmoothMap_Circle.fourierCoeffReal_fourierBasis (L := Ls) ms ns
  have htime := asym_circleRestriction_inner_tendsto Lt Nt hNt hNt_top bt ct
  have hspace := asym_circleRestriction_inner_tendsto Ls Ns hNs hNs_top bs cs
  have htime' : Tendsto
      (fun k =>
        letI : NeZero (Nt k) := hNt k
        ∑ z : ZMod (Nt k), circleRestriction Lt (Nt k) bt z *
          circleRestriction Lt (Nt k) ct z)
      atTop (nhds (if mt = nt then 1 else 0)) := by
    simpa [htime0] using htime
  have hspace' : Tendsto
      (fun k =>
        letI : NeZero (Ns k) := hNs k
        ∑ z : ZMod (Ns k), circleRestriction Ls (Ns k) bs z *
          circleRestriction Ls (Ns k) cs z)
      atTop (nhds (if ms = ns then 1 else 0)) := by
    simpa [hspace0] using hspace
  have hprod :
      (fun k =>
        letI : NeZero (Nt k) := hNt k
        letI : NeZero (Ns k) := hNs k
        ∑ x : AsymLatticeSites (Nt k) (Ns k),
          evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x
              (RapidDecaySeq.basisVec m) *
            evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x
              (RapidDecaySeq.basisVec n)) =
      (fun k =>
        (letI : NeZero (Nt k) := hNt k
         ∑ z : ZMod (Nt k), circleRestriction Lt (Nt k) bt z *
           circleRestriction Lt (Nt k) ct z) *
        (letI : NeZero (Ns k) := hNs k
         ∑ z : ZMod (Ns k), circleRestriction Ls (Ns k) bs z *
           circleRestriction Ls (Ns k) cs z)) := by
    funext k
    letI : NeZero (Nt k) := hNt k
    letI : NeZero (Ns k) := hNs k
    simp_rw [evalAsymTorusAtSite_basisVec]
    rw [Fintype.sum_prod_type]
    calc
      (∑ x : ZMod (Nt k), ∑ y : ZMod (Ns k),
          (circleRestriction Lt (Nt k) bt x * circleRestriction Ls (Ns k) bs y) *
            (circleRestriction Lt (Nt k) ct x * circleRestriction Ls (Ns k) cs y)) =
        ∑ x : ZMod (Nt k), ∑ y : ZMod (Ns k),
          (circleRestriction Lt (Nt k) bt x * circleRestriction Lt (Nt k) ct x) *
            (circleRestriction Ls (Ns k) bs y * circleRestriction Ls (Ns k) cs y) := by
              apply Finset.sum_congr rfl
              intro x hx
              apply Finset.sum_congr rfl
              intro y hy
              ring
      _ = (∑ x : ZMod (Nt k),
          circleRestriction Lt (Nt k) bt x * circleRestriction Lt (Nt k) ct x) *
          (∑ y : ZMod (Ns k),
          circleRestriction Ls (Ns k) bs y * circleRestriction Ls (Ns k) cs y) := by
            rw [Finset.sum_mul_sum]
  rw [hprod]
  have hdelta :
      (if mt = nt then 1 else 0) * (if ms = ns then 1 else 0) =
        (if m = n then 1 else 0) := by
    by_cases hmn : m = n
    · subst n
      simp
    by_cases hmt : mt = nt
    · by_cases hms : ms = ns
      · have hmn' : m = n := by
          rw [← Nat.pair_unpair m, ← Nat.pair_unpair n, hmt, hms]
        simp [hmn']
      · simp [hmt, hms, hmn]
    · simp [hmt, hmn]
  convert htime'.mul hspace' using 1 <;> simp [hdelta]

theorem asymTorusSiteEval_sq_tendsto
    (Lt Ls : ℝ) [Fact (0 < Lt)] [Fact (0 < Ls)]
    (Nt Ns : ℕ → ℕ) (a : ℕ → ℝ)
    (hNt : ∀ k, NeZero (Nt k)) (hNs : ∀ k, NeZero (Ns k))
    (ha : ∀ k, 0 < a k)
    (hLt : ∀ k, (Nt k : ℝ) * a k = Lt)
    (hLs : ∀ k, (Ns k : ℝ) * a k = Ls)
    (ha0 : Tendsto a atTop (nhds 0))
    (f : AsymTorusTestFunction Lt Ls) :
    Tendsto
      (fun k =>
        letI : NeZero (Nt k) := hNt k
        letI : NeZero (Ns k) := hNs k
        ∑ x : AsymLatticeSites (Nt k) (Ns k),
          (evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x f) ^ 2)
      atTop (nhds (l2InnerProduct f f)) := by
  have ha0' : Tendsto a atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within a ha0
      (Filter.Eventually.of_forall fun k => ha k)
  have hinv : Tendsto (fun k => (a k)⁻¹) atTop atTop :=
    tendsto_inv_nhdsGT_zero.comp ha0'
  have hNt_top : Tendsto Nt atTop atTop := by
    rw [← tendsto_natCast_atTop_iff (R := ℝ)]
    refine (hinv.const_mul_atTop (Fact.out : (0 : ℝ) < Lt)).congr fun k => ?_
    rw [← div_eq_mul_inv, div_eq_iff (ne_of_gt (ha k))]
    exact (hLt k).symm
  have hNs_top : Tendsto Ns atTop atTop := by
    rw [← tendsto_natCast_atTop_iff (R := ℝ)]
    refine (hinv.const_mul_atTop (Fact.out : (0 : ℝ) < Ls)).congr fun k => ?_
    rw [← div_eq_mul_inv, div_eq_iff (ne_of_gt (ha k))]
    exact (hLs k).symm
  let fN : ℕ → AsymTorusTestFunction Lt Ls := fun N =>
    ∑ m ∈ Finset.range N,
      DyninMityaginSpace.coeff m f • RapidDecaySeq.basisVec m
  have hfN : Tendsto fN atTop (nhds f) := by
    simpa [fN] using
      (DyninMityaginSpace.hasSum_basis (E := AsymTorusTestFunction Lt Ls) f).tendsto_sum_nat
  have hcoeff_fN : ∀ (N r : ℕ),
      DyninMityaginSpace.coeff r (fN N) =
        if r ∈ Finset.range N then DyninMityaginSpace.coeff r f else 0 := by
    intro N r
    simp [fN, map_sum, map_smul,
      DyninMityaginSpace.HasBiorthogonalBasis.coeff_basis]
  have hl2_fN : ∀ N,
      l2InnerProduct (fN N) (fN N) =
        ∑ m ∈ Finset.range N, (DyninMityaginSpace.coeff m f) ^ 2 := by
    intro N
    rw [l2InnerProduct]
    have houtside : ∀ r, r ∉ Finset.range N →
        DyninMityaginSpace.coeff r (fN N) *
            DyninMityaginSpace.coeff r (fN N) = 0 := by
      intro r hr
      simp [hcoeff_fN, hr]
    change (∑' r, DyninMityaginSpace.coeff r (fN N) *
      DyninMityaginSpace.coeff r (fN N)) = _
    rw [tsum_eq_sum (s := Finset.range N) houtside]
    apply Finset.sum_congr rfl
    intro r hr
    simp [hcoeff_fN, hr]
  have hl2_tendsto : Tendsto
      (fun N => l2InnerProduct (fN N) (fN N)) atTop
      (nhds (l2InnerProduct f f)) := by
    have hs := (l2InnerProduct_summable f f).hasSum.tendsto_sum_nat
    have hfun : (fun N => l2InnerProduct (fN N) (fN N)) =
        fun N => ∑ m ∈ Finset.range N, (DyninMityaginSpace.coeff m f) ^ 2 :=
      funext hl2_fN
    rw [hfun]
    have hsq :
        (fun N => ∑ m ∈ Finset.range N, (DyninMityaginSpace.coeff m f) ^ 2) =
          fun N => ∑ m ∈ Finset.range N,
            DyninMityaginSpace.coeff m f * DyninMityaginSpace.coeff m f := by
      ext N
      refine Finset.sum_congr rfl fun m _ => (pow_two _).symm
    rw [hsq]
    -- `l2InnerProduct` is defeq to the bilinear tsum; do not unfold it
    -- (the expansion is a private name).
    change Tendsto
        (fun N => ∑ m ∈ Finset.range N,
          DyninMityaginSpace.coeff m f * DyninMityaginSpace.coeff m f)
        atTop
        (nhds
          (∑' r, DyninMityaginSpace.coeff r f *
            DyninMityaginSpace.coeff r f))
    exact hs
  let S : ℕ → AsymTorusTestFunction Lt Ls → ℝ := fun k h =>
    letI : NeZero (Nt k) := hNt k
    letI : NeZero (Ns k) := hNs k
    ∑ x : AsymLatticeSites (Nt k) (Ns k),
      (evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x h) ^ 2
  have hfixed : ∀ N, Tendsto (fun k => S k (fN N)) atTop
      (nhds (l2InnerProduct (fN N) (fN N))) := by
    intro N
    have hS_expand : ∀ k,
        S k (fN N) =
          ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
            DyninMityaginSpace.coeff m f * DyninMityaginSpace.coeff n f *
              (letI : NeZero (Nt k) := hNt k
               letI : NeZero (Ns k) := hNs k
               ∑ x : AsymLatticeSites (Nt k) (Ns k),
                 evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x
                   (RapidDecaySeq.basisVec m) *
                 evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x
                   (RapidDecaySeq.basisVec n)) := by
      intro k
      dsimp [S, fN]
      simp only [Finset.sum_apply, map_sum, map_smul, Pi.smul_apply, smul_eq_mul,
        pow_two]
      rw [Finset.sum_mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro x hx
      ring
    rw [show (fun k => S k (fN N)) =
        (fun k => ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
          DyninMityaginSpace.coeff m f * DyninMityaginSpace.coeff n f *
            (letI : NeZero (Nt k) := hNt k
             letI : NeZero (Ns k) := hNs k
             ∑ x : AsymLatticeSites (Nt k) (Ns k),
               evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x
                 (RapidDecaySeq.basisVec m) *
               evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x
                 (RapidDecaySeq.basisVec n))) by
          funext k; exact hS_expand k]
    have hsum : Tendsto
        (fun k => ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
          DyninMityaginSpace.coeff m f * DyninMityaginSpace.coeff n f *
            (letI : NeZero (Nt k) := hNt k
             letI : NeZero (Ns k) := hNs k
             ∑ x : AsymLatticeSites (Nt k) (Ns k),
               evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x
                 (RapidDecaySeq.basisVec m) *
               evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x
                 (RapidDecaySeq.basisVec n))) atTop
        (nhds (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
          DyninMityaginSpace.coeff m f * DyninMityaginSpace.coeff n f *
            (if m = n then 1 else 0))) := by
      apply tendsto_finset_sum
      intro m hm
      apply tendsto_finset_sum
      intro n hn
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        ((asym_basis_pair_tendsto Lt Ls Nt Ns a hNt hNs hNt_top hNs_top m n).const_mul
          (DyninMityaginSpace.coeff m f * DyninMityaginSpace.coeff n f))
    have hdiag :
        (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
        DyninMityaginSpace.coeff m f * DyninMityaginSpace.coeff n f *
          (if m = n then 1 else 0)) =
        l2InnerProduct (fN N) (fN N) := by
      rw [hl2_fN N]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.sum_eq_single m]
      · simp [pow_two]
      · intro b hb hbm
        simp [hbm]
      · intro hmN
        exact (hmN hm).elim
    rw [hdiag] at hsum
    exact hsum
  have hpdiff : Tendsto
      (fun N => RapidDecaySeq.rapidDecaySeminorm 0 (fN N - f)) atTop (nhds 0) := by
    have hdiff : Tendsto (fun N => fN N - f) atTop (nhds 0) := by
      simpa using hfN.sub tendsto_const_nhds
    have hp :=
      (RapidDecaySeq.rapidDecay_withSeminorms.continuous_seminorm 0).continuousAt.tendsto.comp
        hdiff
    convert hp using 1
    exact congrArg nhds
      (map_zero (RapidDecaySeq.rapidDecaySeminorm 0)).symm
  obtain ⟨C₀t, hC₀t_pos, hC₀t_bound⟩ :=
    SmoothMap_Circle.sobolevSeminorm_fourierBasis_le (L := Lt) 0
  obtain ⟨C₀s, hC₀s_pos, hC₀s_bound⟩ :=
    SmoothMap_Circle.sobolevSeminorm_fourierBasis_le (L := Ls) 0
  let C₀ := Lt * Ls * C₀t ^ 2 * C₀s ^ 2
  have hC₀_pos : 0 < C₀ := by
    dsimp [C₀]
    positivity
  have hsample_bound : ∀ k (h : AsymTorusTestFunction Lt Ls),
      ‖WithLp.toLp 2 (fun x : AsymLatticeSites (Nt k) (Ns k) =>
          evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x h)‖ ≤
        Real.sqrt C₀ * RapidDecaySeq.rapidDecaySeminorm 0 h := by
    intro k h
    letI : NeZero (Nt k) := hNt k
    letI : NeZero (Ns k) := hNs k
    have hsquare := asymTorusSiteEval_norm_sq_le_seminorm Lt Ls
      C₀t hC₀t_pos (fun m => by
        simpa only [pow_zero, mul_one] using hC₀t_bound m)
      C₀s hC₀s_pos (fun m => by
        simpa only [pow_zero, mul_one] using hC₀s_bound m) h (Nt k) (Ns k)
    have hsquare' :
        ‖WithLp.toLp 2 (fun x : AsymLatticeSites (Nt k) (Ns k) =>
          evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x h)‖ ^ 2 ≤
          C₀ * (RapidDecaySeq.rapidDecaySeminorm 0 h) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simpa [C₀, Real.norm_eq_abs, sq_abs] using hsquare
    have hp : 0 ≤ RapidDecaySeq.rapidDecaySeminorm 0 h := apply_nonneg _ _
    have hsqrt : 0 ≤ Real.sqrt C₀ := Real.sqrt_nonneg _
    nlinarith [Real.sq_sqrt hC₀_pos.le, norm_nonneg
      (WithLp.toLp 2 (fun x : AsymLatticeSites (Nt k) (Ns k) =>
        evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x h))]
  rw [Metric.tendsto_atTop]
  intro ε hε
  let p : AsymTorusTestFunction Lt Ls → ℝ :=
    RapidDecaySeq.rapidDecaySeminorm 0
  let A : ℝ := Real.sqrt C₀
  let d : ℝ := p f
  have hden : 0 < 3 * A ^ 2 * (2 * d + 1) := by
    dsimp [A, d]
    have hd : 0 ≤ p f := apply_nonneg _ _
    positivity
  have htarget : ∀ᶠ N in atTop,
      |l2InnerProduct (fN N) (fN N) - l2InnerProduct f f| < ε / 3 := by
    have h := (Metric.tendsto_atTop.mp hl2_tendsto) (ε / 3) (by positivity)
    simpa [Real.dist_eq] using h
  have hsmall : ∀ᶠ N in atTop,
      p (fN N - f) < min 1 (ε / (3 * A ^ 2 * (2 * d + 1))) := by
    have hmin : 0 < min 1 (ε / (3 * A ^ 2 * (2 * d + 1))) := by
      rw [lt_min_iff]
      exact ⟨by norm_num, div_pos hε hden⟩
    have h := (Metric.tendsto_atTop.mp hpdiff)
      (min 1 (ε / (3 * A ^ 2 * (2 * d + 1)))) hmin
    simpa [Real.dist_eq, abs_of_nonneg (apply_nonneg _ _)] using h
  rcases eventually_atTop.1 (htarget.and hsmall) with ⟨N₀, hN₀⟩
  have hNtarget := hN₀ N₀ le_rfl |>.1
  have hNsmall := hN₀ N₀ le_rfl |>.2
  obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.mp (hfixed N₀)) (ε / 3) (by positivity)
  refine ⟨K, fun k hk => ?_⟩
  have hfixed_k := hK k hk
  rw [Real.dist_eq] at hfixed_k ⊢
  let vf : EuclideanSpace ℝ (AsymLatticeSites (Nt k) (Ns k)) :=
    WithLp.toLp 2 (fun x =>
      evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x f)
  let vn : EuclideanSpace ℝ (AsymLatticeSites (Nt k) (Ns k)) :=
    WithLp.toLp 2 (fun x =>
      evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x (fN N₀))
  let vd : EuclideanSpace ℝ (AsymLatticeSites (Nt k) (Ns k)) :=
    WithLp.toLp 2 (fun x =>
      evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x (f - fN N₀))
  have hvd : vd = vf - vn := by
    ext x
    simp [vd, vf, vn, map_sub]
  have hnorm_f := hsample_bound k f
  have hnorm_n := hsample_bound k (fN N₀)
  have hnorm_d := hsample_bound k (f - fN N₀)
  have hpfn : p (fN N₀) ≤ d + 1 := by
    have hdecomp : (fN N₀ - f) + f = fN N₀ := by abel
    have htriangle := (RapidDecaySeq.rapidDecaySeminorm 0).add_le'
      (fN N₀ - f) f
    have hdiff' := hNsmall.trans_le (min_le_left _ _)
    calc
      p (fN N₀) = p ((fN N₀ - f) + f) := by rw [hdecomp]
      _ ≤ p (fN N₀ - f) + p f := htriangle
      _ ≤ 1 + d := by
        have hdiff'' : p (fN N₀ - f) ≤ 1 := hdiff'.le
        dsimp [d]
        linarith
      _ = d + 1 := by ring
  have hnorm_sum : ‖vf‖ + ‖vn‖ ≤ A * (2 * d + 1) := by
    have h1 := hnorm_f
    have h2 := hnorm_n
    dsimp [A, p, d] at *
    have hpf : 0 ≤ RapidDecaySeq.rapidDecaySeminorm 0 f := apply_nonneg _ _
    have hpn : 0 ≤ RapidDecaySeq.rapidDecaySeminorm 0 (fN N₀) := apply_nonneg _ _
    have hA : 0 ≤ A := by
      dsimp [A]
      exact Real.sqrt_nonneg _
    nlinarith
  have hnorm_diff : ‖vf - vn‖ ≤ A * p (fN N₀ - f) := by
    rw [← hvd]
    have := hsample_bound k (f - fN N₀)
    have heq : p (f - fN N₀) = p (fN N₀ - f) := by
      rw [show f - fN N₀ = -(fN N₀ - f) by abel,
        map_neg_eq_map]
    rw [heq] at this
    exact this
  have hsqdiff :
      |S k f - S k (fN N₀)| ≤
        (‖vf‖ + ‖vn‖) * ‖vf - vn‖ := by
    dsimp [S, vf, vn]
    rw [← EuclideanSpace.real_norm_sq_eq, ← EuclideanSpace.real_norm_sq_eq]
    rw [show ‖vf‖ ^ 2 - ‖vn‖ ^ 2 =
        (‖vf‖ - ‖vn‖) * (‖vf‖ + ‖vn‖) by ring, abs_mul]
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le vf vn)
        (add_nonneg (norm_nonneg _) (norm_nonneg _))
  have hsqdiff' : |S k f - S k (fN N₀)| < ε / 3 := by
    calc
      |S k f - S k (fN N₀)| ≤
          (‖vf‖ + ‖vn‖) * ‖vf - vn‖ := hsqdiff
      _ ≤ A * (2 * d + 1) * (A * p (fN N₀ - f)) := by
        have hA : 0 ≤ A := by
          dsimp [A]
          exact Real.sqrt_nonneg _
        have hd : 0 ≤ d := by
          dsimp [d]
          exact apply_nonneg _ _
        have hsumfac : 0 ≤ A * (2 * d + 1) := by positivity
        calc
          (‖vf‖ + ‖vn‖) * ‖vf - vn‖ ≤
              A * (2 * d + 1) * ‖vf - vn‖ :=
            mul_le_mul_of_nonneg_right hnorm_sum (norm_nonneg _)
          _ ≤ A * (2 * d + 1) * (A * p (fN N₀ - f)) :=
            mul_le_mul_of_nonneg_left hnorm_diff hsumfac
      _ < ε / 3 := by
        have hsmall' := hNsmall.trans_le (min_le_right _ _)
        have heq : A * (2 * d + 1) * (A * p (fN N₀ - f)) =
            A ^ 2 * (2 * d + 1) * p (fN N₀ - f) := by ring
        rw [heq]
        have hcoef : 0 < A ^ 2 * (2 * d + 1) := by
          nlinarith [hden]
        have hmul := mul_lt_mul_of_pos_left hsmall' hcoef
        calc
          A ^ 2 * (2 * d + 1) * p (fN N₀ - f) <
              A ^ 2 * (2 * d + 1) *
                (ε / (3 * A ^ 2 * (2 * d + 1))) := hmul
          _ = ε / 3 := by
            field_simp [ne_of_gt hden, ne_of_gt hcoef]
  calc
    |S k f - l2InnerProduct f f| ≤
        |S k f - S k (fN N₀)| +
          |S k (fN N₀) - l2InnerProduct (fN N₀) (fN N₀)| +
          |l2InnerProduct (fN N₀) (fN N₀) - l2InnerProduct f f| := by
      calc
        |S k f - l2InnerProduct f f| ≤
            |S k f - S k (fN N₀)| +
              |S k (fN N₀) - l2InnerProduct f f| := abs_sub_le _ _ _
        _ ≤ |S k f - S k (fN N₀)| +
              (|S k (fN N₀) - l2InnerProduct (fN N₀) (fN N₀)| +
                |l2InnerProduct (fN N₀) (fN N₀) - l2InnerProduct f f|) :=
          add_le_add_left (abs_sub_le _ _ _) _
        _ = _ := by ring
    _ < ε / 3 + ε / 3 + ε / 3 := by
      gcongr
    _ = ε := by ring

/-- The normalized squared lattice pullback converges to the asymmetric-torus
`L²` coefficient norm along every fixed-physical-size UV sequence. -/
theorem asymTorusIso_raw_sampling_tendsto_of_siteEval
    (Lt Ls : ℝ) [Fact (0 < Lt)] [Fact (0 < Ls)]
    (Nt Ns : ℕ → ℕ) (a : ℕ → ℝ)
    (hNt : ∀ k, NeZero (Nt k)) (hNs : ∀ k, NeZero (Ns k))
    (ha : ∀ k, 0 < a k)
    (hLt_phys : ∀ k, (Nt k : ℝ) * a k = Lt)
    (hLs_phys : ∀ k, (Ns k : ℝ) * a k = Ls)
    (ha0 : Filter.Tendsto a Filter.atTop (nhds 0)) :
    ∀ f : CylinderTestFunction Ls,
      Filter.Tendsto
        (fun k ⇒
          letI : NeZero (Nt k) := hNt k
          letI : NeZero (Ns k) := hNs k
          (a k ^ 2 : ℝ)⁻¹ *
            ∑ x : AsymLatticeSites (Nt k) (Ns k),
              (asymLatticeTestFnIso Lt Ls (Nt k) (Ns k) (a k)
                (cylinderToTorusEmbed Lt Ls f) x) ^ 2)
        Filter.atTop
        (nhds (l2InnerProduct (cylinderToTorusEmbed Lt Ls f)
          (cylinderToTorusEmbed Lt Ls f))) := by
  intro f
  have hsite :=
    asymTorusSiteEval_sq_tendsto Lt Ls Nt Ns a hNt hNs ha
      hLt_phys hLs_phys ha0 (cylinderToTorusEmbed Lt Ls f)
  have hscale :
      (fun k ⇒
        letI : NeZero (Nt k) := hNt k
        letI : NeZero (Ns k) := hNs k
        (a k ^ 2 : ℝ)⁻¹ *
          ∑ x : AsymLatticeSites (Nt k) (Ns k),
            (asymLatticeTestFnIso Lt Ls (Nt k) (Ns k) (a k)
              (cylinderToTorusEmbed Lt Ls f) x) ^ 2) =
      (fun k ⇒
        letI : NeZero (Nt k) := hNt k
        letI : NeZero (Ns k) := hNs k
        ∑ x : AsymLatticeSites (Nt k) (Ns k),
          (evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x
            (cylinderToTorusEmbed Lt Ls f)) ^ 2) := by
    funext k
    letI : NeZero (Nt k) := hNt k
    letI : NeZero (Ns k) := hNs k
    exact asymLatticeTestFnIso_scaled_sq_sum_eq_evalAsymTorusAtSite_sq_sum
      Lt Ls (Nt k) (Ns k) (a k) (ha k)
        (cylinderToTorusEmbed Lt Ls f)
  rw [hscale]
  simpa using hsite

/-- A raw finite-grid sampling limit turns the sitewise massive variance estimate
into a cylinder exponential-moment bound after the UV weak limit, relative to a
fixed cylinder seminorm that dominates the embedded ℓ² product at this `Lt`. -/
theorem asymTorusIso_measureHasCylinderExpMomentBound_of_raw_sampling_of_seminorm
    (mass : ℝ) (hmass : 0 < mass)
    (K C : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (q : Seminorm ℝ (CylinderTestFunction Ls))
    (hq_l2 : ∀ f : CylinderTestFunction Ls,
      l2InnerProduct (cylinderToTorusEmbed Lt Ls f)
        (cylinderToTorusEmbed Lt Ls f) ≤ q f ^ 2)
    (Nt Ns : ℕ → ℕ) (a : ℕ → ℝ)
    (hNt : ∀ k, NeZero (Nt k)) (hNs : ∀ k, NeZero (Ns k))
    (ha : ∀ k, 0 < a k)
    (hLt_phys : ∀ k, (Nt k : ℝ) * a k = Lt)
    (hLs_phys : ∀ k, (Ns k : ℝ) * a k = Ls)
    (ha0 : Filter.Tendsto a Filter.atTop (nhds 0))
    (ν : ℕ → Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    (hν_prob : ∀ k, IsProbabilityMeasure (ν k))
    (hμ_prob : IsProbabilityMeasure μ)
    (hbc : ∀ (g : Configuration (AsymTorusTestFunction Lt Ls) → ℝ),
      Continuous g → (∃ B, ∀ x, |g x| ≤ B) →
      Filter.Tendsto (fun k ⇒ ∫ ω, g ω ∂(ν k)) Filter.atTop
        (nhds (∫ ω, g ω ∂μ)))
    (hcutoff : ∀ k,
      letI : NeZero (Nt k) := hNt k
      letI : NeZero (Ns k) := hNs k
      ∀ F : AsymTorusTestFunction Lt Ls,
        Integrable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) ⇒
          Real.exp (|ω F|)) (ν k) ∧
        ∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
          Real.exp (|ω F|) ∂(ν k) ≤
          K * Real.exp (C *
            ∫ ω : Configuration (AsymLatticeField (Nt k) (Ns k)),
              (ω (fun x ⇒ |asymLatticeTestFnIso Lt Ls (Nt k) (Ns k) (a k) F x|)) ^ 2
              ∂(latticeGaussianMeasureAsym (Nt k) (Ns k) (a k)
                mass (ha k) hmass))) :
    MeasureHasCylinderExpMomentBound Ls K (C * mass⁻¹ ^ 2) q μ := by
  have hraw := asymTorusIso_raw_sampling_tendsto_of_siteEval
    Lt Ls Nt Ns a hNt hNs ha hLt_phys hLs_phys ha0
  intro f
  let F : AsymTorusTestFunction Lt Ls := cylinderToTorusEmbed Lt Ls f
  let R : ℕ → ℝ := fun k ⇒
    letI : NeZero (Nt k) := hNt k
    letI : NeZero (Ns k) := hNs k
    (a k ^ 2 : ℝ)⁻¹ *
      ∑ x : AsymLatticeSites (Nt k) (Ns k),
        (asymLatticeTestFnIso Lt Ls (Nt k) (Ns k) (a k) F x) ^ 2
  have hR : Filter.Tendsto R Filter.atTop
      (nhds (l2InnerProduct F F)) := by
    simpa [R, F] using hraw f
  let D : ℝ := C * mass⁻¹ ^ 2
  let B : ℕ → ℝ := fun k ⇒ K * Real.exp (D * R k)
  let Binf : ℝ := K * Real.exp (D * l2InnerProduct F F)
  have hB : Filter.Tendsto B Filter.atTop (nhds Binf) := by
    dsimp [B, Binf]
    exact ((Real.continuous_exp.tendsto _).comp (hR.const_mul D)).const_mul K
  have h_unif : ∀ k,
      Integrable (fun ω : Configuration (CylinderTestFunction Ls) ⇒
        Real.exp (|ω f|)) (cylinderPullbackMeasure Lt Ls (ν k)) ∧
      ∫ ω : Configuration (CylinderTestFunction Ls),
        Real.exp (|ω f|) ∂(cylinderPullbackMeasure Lt Ls (ν k)) ≤ B k := by
    intro k
    letI : NeZero (Nt k) := hNt k
    letI : NeZero (Ns k) := hNs k
    letI : IsProbabilityMeasure (ν k) := hν_prob k
    obtain ⟨hT_int, hT_bound⟩ := hcutoff k F
    have hT_int' :
        Integrable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) ⇒
          Real.exp (|ω (cylinderToTorusEmbed Lt Ls f)|)) (ν k) := by
      simpa [F] using hT_int
    have hT_bound' :
        ∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
            Real.exp (|ω (cylinderToTorusEmbed Lt Ls f)|) ∂(ν k) ≤
          K * Real.exp (C *
            ∫ ω : Configuration (AsymLatticeField (Nt k) (Ns k)),
              (ω (fun x ⇒ |asymLatticeTestFnIso Lt Ls (Nt k) (Ns k) (a k)
                (cylinderToTorusEmbed Lt Ls f) x|)) ^ 2
              ∂(latticeGaussianMeasureAsym (Nt k) (Ns k) (a k)
                mass (ha k) hmass)) := by
      simpa [F] using hT_bound
    obtain ⟨hCyl_int, hEq⟩ :=
      cylinderPullback_expMoment_eq Ls Lt (ν k) f hT_int'
    have hvar :
        (∫ ω : Configuration (AsymLatticeField (Nt k) (Ns k)),
          (ω (fun x ⇒ |asymLatticeTestFnIso Lt Ls (Nt k) (Ns k) (a k)
            (cylinderToTorusEmbed Lt Ls f) x|)) ^ 2
          ∂(latticeGaussianMeasureAsym (Nt k) (Ns k) (a k)
            mass (ha k) hmass)) ≤
        mass⁻¹ ^ 2 * R k := by
      calc
        _ ≤ (a k ^ 2 : ℝ)⁻¹ * mass⁻¹ ^ 2 *
            ∑ x : AsymLatticeSites (Nt k) (Ns k),
              (asymLatticeTestFnIso Lt Ls (Nt k) (Ns k) (a k)
                (cylinderToTorusEmbed Lt Ls f) x) ^ 2 :=
          asymFreeVariance_sitewiseAbs_le_mass_inv_sq
            (Nt k) (Ns k) (a k) mass (ha k) hmass
            (asymLatticeTestFnIso Lt Ls (Nt k) (Ns k) (a k)
              (cylinderToTorusEmbed Lt Ls f))
        _ = mass⁻¹ ^ 2 * R k := by
          dsimp [R, F]
          ring
    refine ⟨hCyl_int, hEq.le.trans ?_⟩
    calc
      ∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
          Real.exp (|ω (cylinderToTorusEmbed Lt Ls f)|) ∂(ν k) ≤
          K * Real.exp (C *
            ∫ ω : Configuration (AsymLatticeField (Nt k) (Ns k)),
              (ω (fun x ⇒ |asymLatticeTestFnIso Lt Ls (Nt k) (Ns k) (a k)
                (cylinderToTorusEmbed Lt Ls f) x|)) ^ 2
              ∂(latticeGaussianMeasureAsym (Nt k) (Ns k) (a k)
                mass (ha k) hmass)) := hT_bound'
      _ ≤ K * Real.exp (D * R k) := by
        apply mul_le_mul_of_nonneg_left _ hK
        apply Real.exp_le_exp.mpr
        calc
          C * _ ≤ C * (mass⁻¹ ^ 2 * R k) :=
            mul_le_mul_of_nonneg_left hvar hC
          _ = D * R k := by
            dsimp [D]
            ring
      _ = B k := by rfl
  obtain ⟨hint_cyl, hle_cyl⟩ :=
    cylinderPullbackMeasure_exponential_moment_of_tendsto_bc
      Lt Ls ν μ hν_prob hμ_prob hbc f B Binf hB h_unif
  have hL2 : l2InnerProduct F F ≤ q f ^ 2 := by
    simpa [F] using hq_l2 f
  refine ⟨hint_cyl, ?_⟩
  calc
    ∫ ω : Configuration (CylinderTestFunction Ls),
        Real.exp (|ω f|) ∂(cylinderPullbackMeasure Lt Ls μ) ≤ Binf := hle_cyl
    _ ≤ K * Real.exp (D * q f ^ 2) := by
      have hD : 0 ≤ D := by
        dsimp [D]
        exact mul_nonneg hC (sq_nonneg mass⁻¹)
      apply mul_le_mul_of_nonneg_left _ hK
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hL2 hD)
    _ = K * Real.exp ((C * mass⁻¹ ^ 2) * q f ^ 2) := by
      simp [D]

/-- A raw finite-grid sampling limit turns the sitewise massive variance estimate
into a cylinder exponential-moment bound after the UV weak limit.  The cutoff
estimate is supplied on the selected sequence; the physical mesh identities
and `a → 0` now discharge the sampling limit internally. -/
theorem asymTorusIso_measureHasCylinderExpMomentBound_of_raw_sampling
    (mass : ℝ) (hmass : 0 < mass)
    (K C : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (Nt Ns : ℕ → ℕ) (a : ℕ → ℝ)
    (hNt : ∀ k, NeZero (Nt k)) (hNs : ∀ k, NeZero (Ns k))
    (ha : ∀ k, 0 < a k)
    (hLt_phys : ∀ k, (Nt k : ℝ) * a k = Lt)
    (hLs_phys : ∀ k, (Ns k : ℝ) * a k = Ls)
    (ha0 : Filter.Tendsto a Filter.atTop (nhds 0))
    (ν : ℕ → Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    (hν_prob : ∀ k, IsProbabilityMeasure (ν k))
    (hμ_prob : IsProbabilityMeasure μ)
    (hbc : ∀ (g : Configuration (AsymTorusTestFunction Lt Ls) → ℝ),
      Continuous g → (∃ B, ∀ x, |g x| ≤ B) →
      Filter.Tendsto (fun k ⇒ ∫ ω, g ω ∂(ν k)) Filter.atTop
        (nhds (∫ ω, g ω ∂μ)))
    (hcutoff : ∀ k,
      letI : NeZero (Nt k) := hNt k
      letI : NeZero (Ns k) := hNs k
      ∀ F : AsymTorusTestFunction Lt Ls,
        Integrable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) ⇒
          Real.exp (|ω F|)) (ν k) ∧
        ∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
          Real.exp (|ω F|) ∂(ν k) ≤
          K * Real.exp (C *
            ∫ ω : Configuration (AsymLatticeField (Nt k) (Ns k)),
              (ω (fun x ⇒ |asymLatticeTestFnIso Lt Ls (Nt k) (Ns k) (a k) F x|)) ^ 2
              ∂(latticeGaussianMeasureAsym (Nt k) (Ns k) (a k)
                mass (ha k) hmass)))
    (hLt1 : 1 ≤ Lt) :
    ∃ q : Seminorm ℝ (CylinderTestFunction Ls), Continuous q ∧
      MeasureHasCylinderExpMomentBound Ls K (C * mass⁻¹ ^ 2) q μ := by
  obtain ⟨q, hq_cont, hq_bound⟩ :=
    -- Still an `axiom` in gaussian-field `Cylinder/MethodOfImages.lean:326`
    -- (pin `d63a285` and clone HEAD `1283a27`). Not a theorem.
    GaussianField.embed_l2_uniform_bound (Ls := Ls)
  refine ⟨q, hq_cont, ?_⟩
  refine asymTorusIso_measureHasCylinderExpMomentBound_of_raw_sampling_of_seminorm
    Lt Ls mass hmass K C hK hC q ?_ Nt Ns a hNt hNs ha
    hLt_phys hLs_phys ha0 ν μ hν_prob hμ_prob hbc hcutoff
  intro f
  simpa [Pphi2.cylinderToTorusEmbed, GaussianField.cylinderToTorusEmbed]
    using hq_bound Lt hLt1 f

/-- A sequence-level cylinder exponential-moment estimate passes through the
isotropic UV weak limit with the same constants and seminorm.

The cutoff premise is imposed only on the selected UV sequence.  This keeps
threshold and mesh hypotheses upstream, where that sequence is chosen. -/
theorem asymTorusIso_measureHasCylinderExpMomentBound_of_cutoff
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (K C : ℝ) (q : Seminorm ℝ (CylinderTestFunction Ls))
    (Nt Ns : ℕ → ℕ) (a : ℕ → ℝ)
    (hNt : ∀ k, NeZero (Nt k)) (hNs : ∀ k, NeZero (Ns k))
    (ha : ∀ k, 0 < a k)
    (hvolt : ∀ k, (Nt k : ℝ) * a k = Lt)
    (hvols : ∀ k, (Ns k : ℝ) * a k = Ls)
    (ha0 : Filter.Tendsto a Filter.atTop (nhds 0))
    (hcutoff : ∀ k,
      letI : NeZero (Nt k) := hNt k
      letI : NeZero (Ns k) := hNs k
      ∀ f : CylinderTestFunction Ls,
        Integrable (fun ω : Configuration (CylinderTestFunction Ls) ⇒
          Real.exp (|ω f|))
          (cylinderPullbackMeasure Lt Ls
            (asymTorusInteractingMeasureIso Lt Ls (Nt k) (Ns k) (a k)
              P mass (ha k) hmass)) ∧
        ∫ ω : Configuration (CylinderTestFunction Ls),
          Real.exp (|ω f|) ∂(cylinderPullbackMeasure Lt Ls
            (asymTorusInteractingMeasureIso Lt Ls (Nt k) (Ns k) (a k)
              P mass (ha k) hmass)) ≤
          K * Real.exp (C * q f ^ 2)) :
    ∃ μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)),
      IsProbabilityMeasure μ ∧
      MeasureHasCylinderExpMomentBound Ls K C q μ := by
  obtain ⟨μ, hμ_prob, φ, hφ_mono, hconv⟩ :=
    asymTorusIso_interacting_limit_exists Lt Ls P mass hmass
      Nt Ns a hNt hNs ha hvolt hvols ha0
  set ν : ℕ → Measure (Configuration (AsymTorusTestFunction Lt Ls)) := fun n ⇒
    haveI := hNt (φ n)
    haveI := hNs (φ n)
    asymTorusInteractingMeasureIso Lt Ls (Nt (φ n)) (Ns (φ n)) (a (φ n))
      P mass (ha (φ n)) hmass with hν_def
  have hν_prob : ∀ n, IsProbabilityMeasure (ν n) := fun n ⇒ by
    haveI := hNt (φ n)
    haveI := hNs (φ n)
    exact asymTorusInteractingMeasureIso_isProbability Lt Ls
      (Nt (φ n)) (Ns (φ n)) (a (φ n)) P mass (ha (φ n)) hmass
  have hbc : ∀ (g : Configuration (AsymTorusTestFunction Lt Ls) → ℝ),
      Continuous g → (∃ D, ∀ x, |g x| ≤ D) →
      Filter.Tendsto (fun n ⇒ ∫ ω, g ω ∂(ν n)) Filter.atTop
        (nhds (∫ ω, g ω ∂μ)) := by
    intro g hg hg_bound
    simpa [ν] using hconv g hg hg_bound
  refine ⟨μ, hμ_prob, ?_⟩
  intro f
  apply cylinderPullbackMeasure_exponential_moment_of_tendsto_bc
    Lt Ls ν μ hν_prob hμ_prob hbc f
    (fun _ ⇒ K * Real.exp (C * q f ^ 2))
    (K * Real.exp (C * q f ^ 2)) tendsto_const_nhds
  intro n
  haveI := hNt (φ n)
  haveI := hNs (φ n)
  simpa [ν] using hcutoff (φ n) f

/-- Convert the thresholded torus absolute-variance estimate into the direct
cylinder-seminorm estimate once the finite-grid variance has been bounded by
that seminorm.  This lemma contains only pushforward and monotonicity algebra;
the sampling estimate remains an explicit premise. -/
theorem asymTorusInteractingMeasureIso_cylinderExpMoment_of_absVarianceBound
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (ha : 0 < a)
    (K C D : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (q : Seminorm ℝ (CylinderTestFunction Ls))
    (f : CylinderTestFunction Ls)
    (hTorus :
      Integrable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) ⇒
        Real.exp (|ω (cylinderToTorusEmbed Lt Ls f)|))
        (asymTorusInteractingMeasureIso Lt Ls Nt Ns a P mass ha hmass) ∧
      ∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
        Real.exp (|ω (cylinderToTorusEmbed Lt Ls f)|)
          ∂(asymTorusInteractingMeasureIso Lt Ls Nt Ns a P mass ha hmass) ≤
        K * Real.exp (C *
          ∫ ω : Configuration (AsymLatticeField Nt Ns),
            (ω (fun x ⇒ |asymLatticeTestFnIso Lt Ls Nt Ns a
              (cylinderToTorusEmbed Lt Ls f) x|)) ^ 2
            ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass)))
    (hVariance :
      ∫ ω : Configuration (AsymLatticeField Nt Ns),
          (ω (fun x ⇒ |asymLatticeTestFnIso Lt Ls Nt Ns a
            (cylinderToTorusEmbed Lt Ls f) x|)) ^ 2
          ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) ≤
        D * q f ^ 2) :
    Integrable (fun ω : Configuration (CylinderTestFunction Ls) ⇒
      Real.exp (|ω f|))
      (cylinderPullbackMeasure Lt Ls
        (asymTorusInteractingMeasureIso Lt Ls Nt Ns a P mass ha hmass)) ∧
    ∫ ω : Configuration (CylinderTestFunction Ls),
      Real.exp (|ω f|) ∂(cylinderPullbackMeasure Lt Ls
        (asymTorusInteractingMeasureIso Lt Ls Nt Ns a P mass ha hmass)) ≤
      K * Real.exp ((C * D) * q f ^ 2) := by
  let μ := asymTorusInteractingMeasureIso Lt Ls Nt Ns a P mass ha hmass
  letI : IsProbabilityMeasure μ :=
    asymTorusInteractingMeasureIso_isProbability Lt Ls Nt Ns a P mass ha hmass
  obtain ⟨hint_cyl, heq⟩ :=
    cylinderPullback_expMoment_eq Ls Lt μ f hTorus.1
  refine ⟨hint_cyl, heq.le.trans ?_⟩
  calc
    ∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
        Real.exp (|ω (cylinderToTorusEmbed Lt Ls f)|) ∂μ ≤
        K * Real.exp (C *
          ∫ ω : Configuration (AsymLatticeField Nt Ns),
            (ω (fun x ⇒ |asymLatticeTestFnIso Lt Ls Nt Ns a
              (cylinderToTorusEmbed Lt Ls f) x|)) ^ 2
            ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass)) := hTorus.2
    _ ≤ K * Real.exp (C * (D * q f ^ 2)) := by
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hVariance hC)) hK
    _ = K * Real.exp ((C * D) * q f ^ 2) := by ring

/-- Translation and time-reflection symmetry of the isotropic UV limit use
only cutoff symmetries, fixed-volume second-moment control, and weak
convergence.  The cylinder-moment route calls this narrower projection
without importing torus OS0 or OS1. -/
theorem asymTorusIso_limit_satisfies_OS2
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (Nt Ns : ℕ → ℕ) (a : ℕ → ℝ)
    (hNt : ∀ k, NeZero (Nt k)) (hNs : ∀ k, NeZero (Ns k))
    (ha : ∀ k, 0 < a k)
    (hvolt : ∀ k, (Nt k : ℝ) * a k = Lt)
    (hvols : ∀ k, (Ns k : ℝ) * a k = Ls)
    (ha0 : Filter.Tendsto a Filter.atTop (nhds 0))
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ]
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hconv : ∀ (F : Configuration (AsymTorusTestFunction Lt Ls) → ℝ),
      Continuous F → (∃ D, ∀ x, |F x| ≤ D) →
        Filter.Tendsto (fun n ⇒ ∫ ω, F ω ∂(haveI := hNt (φ n); haveI := hNs (φ n)
            asymTorusInteractingMeasureIso Lt Ls (Nt (φ n)) (Ns (φ n)) (a (φ n))
              P mass (ha (φ n)) hmass))
          Filter.atTop (nhds (∫ ω, F ω ∂μ))) :
    AsymTorusOS2_TranslationInvariance Lt Ls μ ∧
    AsymTorusOS2_TimeReflectionInvariance Lt Ls μ := by
  let a' : ℕ → ℝ := fun n ⇒ a (φ n)
  let ν : ℕ → Measure (Configuration (AsymTorusTestFunction Lt Ls)) := fun n ⇒
    haveI := hNt (φ n)
    haveI := hNs (φ n)
    asymTorusInteractingMeasureIso Lt Ls (Nt (φ n)) (Ns (φ n)) (a (φ n))
      P mass (ha (φ n)) hmass
  letI (n : ℕ) : IsProbabilityMeasure (ν n) := by
    dsimp only [ν]
    infer_instance
  obtain ⟨Dint, hDint, hDint_bound⟩ :=
    asymTorusIso_interacting_second_moment_density_transfer Lt Ls P mass hmass
  obtain ⟨Dfree, hDfree, hDfree_bound⟩ :=
    asymGaussianIso_second_moment_le_seminorm Lt Ls mass hmass
  let p : AsymTorusTestFunction Lt Ls → ℝ :=
    RapidDecaySeq.rapidDecaySeminorm 0
  have hp : Continuous p :=
    RapidDecaySeq.rapidDecay_withSeminorms.continuous_seminorm 0
  have hp0 : p 0 = 0 := map_zero (RapidDecaySeq.rapidDecaySeminorm 0)
  have hmoment : ∀ (f : AsymTorusTestFunction Lt Ls) (n : ℕ),
      Integrable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) ⇒ (ω f) ^ 2) (ν n) ∧
      ∫ ω : Configuration (AsymTorusTestFunction Lt Ls), (ω f) ^ 2 ∂(ν n) ≤
        (Dint * Dfree) * p f ^ 2 := by
    intro f n
    haveI := hNt (φ n)
    haveI := hNs (φ n)
    refine ⟨asymTorusInteractingMeasureIso_sq_integrable Lt Ls
      (Nt (φ n)) (Ns (φ n)) (a (φ n)) P mass (ha (φ n)) hmass f, ?_⟩
    calc
      ∫ ω : Configuration (AsymTorusTestFunction Lt Ls), (ω f) ^ 2 ∂(ν n) ≤
          Dint * ∫ ω : Configuration (AsymLatticeField (Nt (φ n)) (Ns (φ n))),
            (ω (asymLatticeTestFnIso Lt Ls (Nt (φ n)) (Ns (φ n)) (a (φ n)) f)) ^ 2
            ∂(latticeGaussianMeasureAsym (Nt (φ n)) (Ns (φ n)) (a (φ n))
              mass (ha (φ n)) hmass) := by
        simpa [ν] using hDint_bound f (Nt (φ n)) (Ns (φ n)) (a (φ n))
          (ha (φ n)) (hvolt (φ n)) (hvols (φ n))
      _ ≤ Dint * (Dfree * p f ^ 2) :=
        mul_le_mul_of_nonneg_left
          (hDfree_bound (Nt (φ n)) (Ns (φ n)) (a (φ n)) (ha (φ n)) f)
          hDint.le
      _ = (Dint * Dfree) * p f ^ 2 := by ring
  have ha'_pos : ∀ n, 0 < a' n := fun n ⇒ ha (φ n)
  have ha'_zero : Filter.Tendsto a' Filter.atTop (nhds 0) :=
    ha0.comp hφ.tendsto_atTop
  have htrans : ∀ (n : ℕ) (j₁ j₂ : ℤ) (f : AsymTorusTestFunction Lt Ls),
      asymTorusGeneratingFunctional Lt Ls (ν n) f =
        asymTorusGeneratingFunctional Lt Ls (ν n)
          (asymTorusTranslation Lt Ls (a' n * j₁, a' n * j₂) f) := by
    intro n j₁ j₂ f
    haveI := hNt (φ n)
    haveI := hNs (φ n)
    simpa [ν, a'] using
      asymTorusInteractingMeasureIso_gf_latticeTranslation_invariant
        Lt Ls (Nt (φ n)) (Ns (φ n)) (a (φ n)) P mass (ha (φ n)) hmass
        (hvolt (φ n)) (hvols (φ n)) j₁ j₂ f
  have hrefl : ∀ (n : ℕ) (f : AsymTorusTestFunction Lt Ls),
      asymTorusGeneratingFunctional Lt Ls (ν n) f =
        asymTorusGeneratingFunctional Lt Ls (ν n) (asymTorusTimeReflection Lt Ls f) := by
    intro n f
    haveI := hNt (φ n)
    haveI := hNs (φ n)
    simpa [ν] using asymTorusInteractingMeasureIso_gf_timeReflection_invariant
      Lt Ls (Nt (φ n)) (Ns (φ n)) (a (φ n)) P mass (ha (φ n)) hmass f
  have hconv' : ∀ (F : Configuration (AsymTorusTestFunction Lt Ls) → ℝ),
      Continuous F → (∃ D, ∀ x, |F x| ≤ D) →
        Filter.Tendsto (fun n ⇒ ∫ ω, F ω ∂(ν n)) Filter.atTop
          (nhds (∫ ω, F ω ∂μ)) := by
    intro F hF hF_bound
    simpa [ν] using hconv F hF hF_bound
  exact ⟨
    asymTorusIsoFamilyOS2_translation Lt Ls μ ν
      (Dint * Dfree) (mul_pos hDint hDfree) p hp hp0 hmoment a' ha'_pos ha'_zero
      htrans hconv',
    asymTorusIsoFamilyOS2_timeReflection Lt Ls μ ν hrefl hconv'⟩

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
        Integrable (fun ω : Configuration (CylinderTestFunction Ls) ⇒
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
  have hNt : ∀ k, NeZero (2 * M k) := fun k ⇒ by
    letI := hM k
    infer_instance
  obtain ⟨μ, hμ_prob, φ, hφ_mono, hconv⟩ :=
    asymTorusIso_interacting_limit_exists Lt Ls P mass hmass
      (fun k ⇒ 2 * M k) Ns a hNt hNs ha hvolt hvols ha0
  haveI : IsProbabilityMeasure μ := hμ_prob
  set ν : ℕ → Measure (Configuration (AsymTorusTestFunction Lt Ls)) := fun n ⇒
    haveI := hM (φ n)
    haveI := hNs (φ n)
    asymTorusInteractingMeasureIso Lt Ls (2 * M (φ n)) (Ns (φ n)) (a (φ n))
      P mass (ha (φ n)) hmass with hν_def
  have hν_prob : ∀ n, IsProbabilityMeasure (ν n) := fun n ⇒ by
    haveI := hM (φ n)
    haveI := hNs (φ n)
    exact asymTorusInteractingMeasureIso_isProbability Lt Ls
      (2 * M (φ n)) (Ns (φ n)) (a (φ n)) P mass (ha (φ n)) hmass
  have hφ_atTop : Filter.Tendsto φ Filter.atTop Filter.atTop :=
    hφ_mono.tendsto_atTop
  have hbc : ∀ (g : Configuration (AsymTorusTestFunction Lt Ls) → ℝ),
      Continuous g → (∃ D, ∀ x, |g x| ≤ D) →
      Filter.Tendsto (fun n ⇒ ∫ ω, g ω ∂(ν n)) Filter.atTop
        (nhds (∫ ω, g ω ∂μ)) := by
    intro g hg hg_bound
    simpa [ν] using hconv g hg hg_bound
  have hμ_exp : MeasureHasCylinderExpMomentBound Ls K C q μ := by
    intro f
    apply cylinderPullbackMeasure_exponential_moment_of_tendsto_bc
      Lt Ls ν μ hν_prob hμ_prob hbc f
      (fun _ ⇒ K * Real.exp (C * q f ^ 2))
      (K * Real.exp (C * q f ^ 2)) tendsto_const_nhds
    intro n
    haveI := hM (φ n)
    haveI := hNs (φ n)
    simpa [ν] using hcutoff (φ n) f
  have hμ_os2 := asymTorusIso_limit_satisfies_OS2 Lt Ls P mass hmass
    (fun k ⇒ 2 * M k) Ns a hNt hNs ha hvolt hvols ha0 μ φ hφ_mono hconv
  refine ⟨μ, hμ_prob, hμ_exp, (fun _ ⇒ hμ_os2), ?_⟩
  intro R hR hLtR n f c hf
  let sigmaSq : ℕ → CylinderTestFunction Ls → ℝ := fun _ h ⇒ q h ^ 2
  apply cylinderRPMatrixNonnegative_of_link_limit Lt Ls ν μ hν_prob hμ_prob hbc
    (fun k ⇒ a (φ k)) (ha0.comp hφ_atTop) sigmaSq K C hK_pos hC_pos
  · intro k h
    exact sq_nonneg (q h)
  · intro k t h
    dsimp [sigmaSq]
    rw [SeminormClass.map_smul_eq_mul, mul_pow, Real.norm_eq_abs, sq_abs]
  · intro hseq hseq0
    have hq0 : Filter.Tendsto (fun k ⇒ q (hseq k)) Filter.atTop (nhds 0) := by
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
        Integrable (fun ω : Configuration (CylinderTestFunction Ls) ⇒
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
      (fun k ⇒ by
        letI : NeZero (M n k) := hM n k
        letI : NeZero (Ns n k) := hNs n k
        intro f
        exact hcutoff n k f)
  choose μ hμ_prob hμ_exp hμ_os2 hμ_rp using hbound
  have hμ_exp_seq : AsymTorusSequenceHasUniformCylinderExpMomentBound
      Ls K C q Lt hLt μ := by
    exact Filter.Eventually.of_forall fun n ⇒ by
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
        Integrable (fun ω : Configuration (CylinderTestFunction Ls) ⇒
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
        AnalyticOnNhd ℂ (fun z : Fin n → ℂ ⇒
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
    (fun φ ν hν_prob hφ hcf K' C' q' hK' hC' hq' hExp ⇒ by
      letI : IsProbabilityMeasure ν := hν_prob
      exact cylinderMeasureReflectionPositive_of_noWrap_limit Ls
        (fun k ⇒ Lt (φ k)) (hLt_tend.comp hφ.tendsto_atTop)
        (fun k ⇒ @cylinderPullbackMeasure (Lt (φ k)) Ls
          (hLt (φ k)) hLs (μ (φ k)))
        ν hcf (fun k ⇒ hμ_noWrap (φ k)) K' C' hK' hC' q' hq' hExp)
    hμ_os2

/-- The metric-correct heterogeneous Iso cutoff limit carries the full
asymmetric-torus OS0--OS2 package.  OS0 and OS1 come from the Green moment
bound; OS2 comes from the proved finite-lattice translation and
time-reflection symmetries. -/
theorem asymTorusIso_limit_satisfies_OS
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (K C : ℝ) (hK : 0 < K) (hC : 0 < C)
    (Nt Ns : ℕ → ℕ) (a : ℕ → ℝ)
    (hNt : ∀ k, NeZero (Nt k)) (hNs : ∀ k, NeZero (Ns k)) (ha : ∀ k, 0 < a k)
    (hvolt : ∀ k, (Nt k : ℝ) * a k = Lt) (hvols : ∀ k, (Ns k : ℝ) * a k = Ls)
    (ha0 : Filter.Tendsto a Filter.atTop (nhds 0))
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ]
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hconv : ∀ (F : Configuration (AsymTorusTestFunction Lt Ls) → ℝ),
      Continuous F → (∃ D, ∀ x, |F x| ≤ D) →
        Filter.Tendsto (fun n => ∫ ω, F ω ∂(haveI := hNt (φ n); haveI := hNs (φ n)
            asymTorusInteractingMeasureIso Lt Ls (Nt (φ n)) (Ns (φ n)) (a (φ n))
              P mass (ha (φ n)) hmass))
          Filter.atTop (nhds (∫ ω, F ω ∂μ)))
    (hgreen : MeasureHasGreenMomentBound Ls mass hmass K C μ) :
    AsymSatisfiesTorusOS Lt Ls μ := by
  let a' : ℕ → ℝ := fun n => a (φ n)
  let ν : ℕ → Measure (Configuration (AsymTorusTestFunction Lt Ls)) := fun n =>
    haveI := hNt (φ n)
    haveI := hNs (φ n)
    asymTorusInteractingMeasureIso Lt Ls (Nt (φ n)) (Ns (φ n)) (a (φ n))
      P mass (ha (φ n)) hmass
  letI (n : ℕ) : IsProbabilityMeasure (ν n) := by
    dsimp only [ν]
    infer_instance
  obtain ⟨Dint, hDint, hDint_bound⟩ :=
    asymTorusIso_interacting_second_moment_density_transfer Lt Ls P mass hmass
  obtain ⟨Dfree, hDfree, hDfree_bound⟩ :=
    asymGaussianIso_second_moment_le_seminorm Lt Ls mass hmass
  let p : AsymTorusTestFunction Lt Ls → ℝ :=
    RapidDecaySeq.rapidDecaySeminorm 0
  have hp : Continuous p :=
    RapidDecaySeq.rapidDecay_withSeminorms.continuous_seminorm 0
  have hp0 : p 0 = 0 := map_zero (RapidDecaySeq.rapidDecaySeminorm 0)
  have hmoment : ∀ (f : AsymTorusTestFunction Lt Ls) (n : ℕ),
      Integrable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) => (ω f) ^ 2) (ν n) ∧
      ∫ ω : Configuration (AsymTorusTestFunction Lt Ls), (ω f) ^ 2 ∂(ν n) ≤
        (Dint * Dfree) * p f ^ 2 := by
    intro f n
    haveI := hNt (φ n)
    haveI := hNs (φ n)
    refine ⟨asymTorusInteractingMeasureIso_sq_integrable Lt Ls
      (Nt (φ n)) (Ns (φ n)) (a (φ n)) P mass (ha (φ n)) hmass f, ?_⟩
    calc
      ∫ ω : Configuration (AsymTorusTestFunction Lt Ls), (ω f) ^ 2 ∂(ν n) ≤
          Dint * ∫ ω : Configuration (AsymLatticeField (Nt (φ n)) (Ns (φ n))),
            (ω (asymLatticeTestFnIso Lt Ls (Nt (φ n)) (Ns (φ n)) (a (φ n)) f)) ^ 2
            ∂(latticeGaussianMeasureAsym (Nt (φ n)) (Ns (φ n)) (a (φ n))
              mass (ha (φ n)) hmass) := by
        simpa [ν] using hDint_bound f (Nt (φ n)) (Ns (φ n)) (a (φ n))
          (ha (φ n)) (hvolt (φ n)) (hvols (φ n))
      _ ≤ Dint * (Dfree * p f ^ 2) :=
        mul_le_mul_of_nonneg_left
          (hDfree_bound (Nt (φ n)) (Ns (φ n)) (a (φ n)) (ha (φ n)) f)
          hDint.le
      _ = (Dint * Dfree) * p f ^ 2 := by ring
  have ha'_pos : ∀ n, 0 < a' n := fun n => ha (φ n)
  have ha'_zero : Filter.Tendsto a' Filter.atTop (nhds 0) :=
    ha0.comp hφ.tendsto_atTop
  have htrans : ∀ (n : ℕ) (j₁ j₂ : ℤ) (f : AsymTorusTestFunction Lt Ls),
      asymTorusGeneratingFunctional Lt Ls (ν n) f =
        asymTorusGeneratingFunctional Lt Ls (ν n)
          (asymTorusTranslation Lt Ls (a' n * j₁, a' n * j₂) f) := by
    intro n j₁ j₂ f
    haveI := hNt (φ n)
    haveI := hNs (φ n)
    simpa [ν, a'] using
      asymTorusInteractingMeasureIso_gf_latticeTranslation_invariant
        Lt Ls (Nt (φ n)) (Ns (φ n)) (a (φ n)) P mass (ha (φ n)) hmass
        (hvolt (φ n)) (hvols (φ n)) j₁ j₂ f
  have hrefl : ∀ (n : ℕ) (f : AsymTorusTestFunction Lt Ls),
      asymTorusGeneratingFunctional Lt Ls (ν n) f =
        asymTorusGeneratingFunctional Lt Ls (ν n) (asymTorusTimeReflection Lt Ls f) := by
    intro n f
    haveI := hNt (φ n)
    haveI := hNs (φ n)
    simpa [ν] using asymTorusInteractingMeasureIso_gf_timeReflection_invariant
      Lt Ls (Nt (φ n)) (Ns (φ n)) (a (φ n)) P mass (ha (φ n)) hmass f
  have hconv' : ∀ (F : Configuration (AsymTorusTestFunction Lt Ls) → ℝ),
      Continuous F → (∃ D, ∀ x, |F x| ≤ D) →
        Filter.Tendsto (fun n => ∫ ω, F ω ∂(ν n)) Filter.atTop
          (nhds (∫ ω, F ω ∂μ)) := by
    intro F hF hF_bound
    simpa [ν] using hconv F hF hF_bound
  exact
    { os0 := asymTorusOS0_of_greenMomentBound Lt Ls mass hmass K C μ hgreen
      os1 := asymTorusOS1_of_greenMomentBound Lt Ls mass hmass K C hK hC μ hgreen
      os2_translation := asymTorusIsoFamilyOS2_translation Lt Ls μ ν
        (Dint * Dfree) (mul_pos hDint hDfree) p hp hp0 hmoment a' ha'_pos ha'_zero
        htrans hconv'
      os2_timeReflection := asymTorusIsoFamilyOS2_timeReflection Lt Ls μ ν hrefl hconv' }

/-- **The isotropic UV continuum limit has the Green-controlled exponential moment bound** — from
a cutoff bound with an explicit constant `K`.

Given the lattice cutoff bound `∫ exp|ωf| dμ̃_int ≤ K·exp(σ²)` at fixed `(Lt, Ls)` (with `K`
constant in `(Nt, Ns, a)`), the UV continuum-limit torus measure `μ` along any isotropic sequence
satisfies `MeasureHasGreenMomentBound` with the *same* `K` and `C = 1`:

  `∫ exp(|ω f|) dμ ≤ K · exp(asymTorusContinuumGreen f f)`.

The cutoff bound + `σ²_k → asymTorusContinuumGreen f f` (`second_moment_asym_tendsto`) pass to the
weak limit by `weakLimit_exponential_moment` (truncation + MCT). `MeasureHasGreenMomentBound`,
never produced for the metric-mismatched square construction, is here a **theorem**. -/
theorem asymTorusIso_measureHasGreenMomentBound_of_cutoff
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (K C : ℝ) (_hK_pos : 0 < K)
    (hcutoff : ∀ (f : AsymTorusTestFunction Lt Ls) (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
      (a : ℝ) (ha : 0 < a), (Nt : ℝ) * a = Lt → (Ns : ℝ) * a = Ls →
      Integrable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
        Real.exp (|ω f|)) (asymTorusInteractingMeasureIso Lt Ls Nt Ns a P mass ha hmass) ∧
      ∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
        Real.exp (|ω f|) ∂(asymTorusInteractingMeasureIso Lt Ls Nt Ns a P mass ha hmass) ≤
      K * Real.exp (C * ∫ ω : Configuration (AsymLatticeField Nt Ns),
        (ω (asymLatticeTestFnIso Lt Ls Nt Ns a f)) ^ 2
        ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass)))
    (Nt Ns : ℕ → ℕ) (a : ℕ → ℝ)
    (hNt : ∀ k, NeZero (Nt k)) (hNs : ∀ k, NeZero (Ns k)) (ha : ∀ k, 0 < a k)
    (hvolt : ∀ k, (Nt k : ℝ) * a k = Lt) (hvols : ∀ k, (Ns k : ℝ) * a k = Ls)
    (ha0 : Filter.Tendsto a Filter.atTop (nhds 0)) :
    ∃ (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls))),
      IsProbabilityMeasure μ ∧
        MeasureHasGreenMomentBound Ls mass hmass K C μ := by
  obtain ⟨μ, hμ_prob, φ, hφ_mono, hconv⟩ :=
    asymTorusIso_interacting_limit_exists Lt Ls P mass hmass Nt Ns a hNt hNs ha hvolt hvols ha0
  haveI := hμ_prob
  refine ⟨μ, hμ_prob, ?_⟩
  intro f
  -- Subsequence measures and their uniform probability instances
  set ν : ℕ → Measure (Configuration (AsymTorusTestFunction Lt Ls)) := fun n =>
    haveI := hNt (φ n); haveI := hNs (φ n)
    asymTorusInteractingMeasureIso Lt Ls (Nt (φ n)) (Ns (φ n)) (a (φ n)) P mass (ha (φ n)) hmass
    with hν_def
  have hν_prob : ∀ n, IsProbabilityMeasure (ν n) := fun n => by
    haveI := hNt (φ n); haveI := hNs (φ n)
    exact asymTorusInteractingMeasureIso_isProbability Lt Ls (Nt (φ n)) (Ns (φ n)) (a (φ n))
      P mass (ha (φ n)) hmass
  -- The lattice second moment along the subsequence
  set B : ℕ → ℝ := fun n => K * Real.exp (C * haveI := hNt (φ n); haveI := hNs (φ n)
    ∫ ω : Configuration (AsymLatticeField (Nt (φ n)) (Ns (φ n))),
      (ω (asymLatticeTestFnIso Lt Ls (Nt (φ n)) (Ns (φ n)) (a (φ n)) f)) ^ 2
      ∂(latticeGaussianMeasureAsym (Nt (φ n)) (Ns (φ n)) (a (φ n)) mass (ha (φ n)) hmass))
    with hB_def
  -- B n → K · exp(asymTorusContinuumGreen f f): the σ² converge to the Green's function
  have hφ_atTop : Filter.Tendsto φ Filter.atTop Filter.atTop := hφ_mono.tendsto_atTop
  have hσ2_full : Filter.Tendsto (fun k => haveI := hNt k; haveI := hNs k
      ∫ ω : Configuration (AsymLatticeField (Nt k) (Ns k)),
        (ω (asymLatticeTestFnIso Lt Ls (Nt k) (Ns k) (a k) f)) ^ 2
        ∂(latticeGaussianMeasureAsym (Nt k) (Ns k) (a k) mass (ha k) hmass))
      Filter.atTop (nhds (asymTorusContinuumGreen Lt Ls mass hmass f f)) := by
    have heq : (fun k => haveI := hNt k; haveI := hNs k
        ∫ ω : Configuration (AsymLatticeField (Nt k) (Ns k)),
          (ω (asymLatticeTestFnIso Lt Ls (Nt k) (Ns k) (a k) f)) ^ 2
          ∂(latticeGaussianMeasureAsym (Nt k) (Ns k) (a k) mass (ha k) hmass)) =
        fun k => haveI := hNt k; haveI := hNs k
          covariance (latticeCovarianceAsymGJ (Nt k) (Ns k) (a k) mass (ha k) hmass)
            (asymLatticeTestFnIso Lt Ls (Nt k) (Ns k) (a k) f)
            (asymLatticeTestFnIso Lt Ls (Nt k) (Ns k) (a k) f) := by
      funext k; haveI := hNt k; haveI := hNs k
      exact second_moment_eq_covariance _ _
    rw [heq]
    exact second_moment_asym_tendsto Lt Ls mass hmass Nt Ns a hNt hNs ha hvolt hvols ha0 f f
  have hB_tendsto : Filter.Tendsto B Filter.atTop
      (nhds (K * Real.exp (C * asymTorusContinuumGreen Lt Ls mass hmass f f))) := by
    rw [hB_def]
    exact ((Real.continuous_exp.tendsto _).comp
      ((hσ2_full.comp hφ_atTop).const_mul C)).const_mul K
  -- Uniform per-n exponential moment bound from the cutoff bound
  have h_unif : ∀ n, Integrable (fun ω => Real.exp (|ω f|)) (ν n) ∧
      ∫ ω, Real.exp (|ω f|) ∂(ν n) ≤ B n := fun n => by
    haveI := hNt (φ n); haveI := hNs (φ n)
    exact hcutoff f (Nt (φ n)) (Ns (φ n)) (a (φ n)) (ha (φ n)) (hvolt (φ n)) (hvols (φ n))
  -- Bounded-continuous weak convergence along the subsequence
  have hbc : ∀ (g : Configuration (AsymTorusTestFunction Lt Ls) → ℝ),
      Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
      Filter.Tendsto (fun n => ∫ ω, g ω ∂(ν n)) Filter.atTop (nhds (∫ ω, g ω ∂μ)) :=
    fun g hg_cont hg_bdd => hconv g hg_cont hg_bdd
  -- Pass to the weak limit (truncation + MCT)
  obtain ⟨hint, hle⟩ := weakLimit_exponential_moment ν hν_prob μ hbc f B
    (K * Real.exp (C * asymTorusContinuumGreen Lt Ls mass hmass f f)) hB_tendsto h_unif
  exact ⟨hint, hle⟩

/-- The even-time-lattice UV construction carries both its Green moment bound
and cylinder reflection positivity for every compact-span family that fits in
the finite time period without wrapping. -/
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

/-- `…_of_cutoff` with the cutoff bound built from a Nelson `L²` constant `Knel` via
`…_cutoff_of_nelson`; the resulting Green-moment constant is `√(2·Knel)`. -/
theorem asymTorusIso_measureHasGreenMomentBound_of_nelson
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (Knel : ℝ) (hKnel_pos : 0 < Knel)
    (hKnel_bound : ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (ha : 0 < a),
      (Nt : ℝ) * a = Lt → (Ns : ℝ) * a = Ls →
      ∫ ω : Configuration (AsymLatticeField Nt Ns),
        (Real.exp (-interactionFunctionalAsym Nt Ns P a mass ω)) ^ 2
        ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) ≤ Knel)
    (Nt Ns : ℕ → ℕ) (a : ℕ → ℝ)
    (hNt : ∀ k, NeZero (Nt k)) (hNs : ∀ k, NeZero (Ns k)) (ha : ∀ k, 0 < a k)
    (hvolt : ∀ k, (Nt k : ℝ) * a k = Lt) (hvols : ∀ k, (Ns k : ℝ) * a k = Ls)
    (ha0 : Filter.Tendsto a Filter.atTop (nhds 0)) :
    ∃ (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls))),
      IsProbabilityMeasure μ ∧
        MeasureHasGreenMomentBound Ls mass hmass (Real.sqrt (2 * Knel)) 1 μ :=
  asymTorusIso_measureHasGreenMomentBound_of_cutoff Lt Ls P mass hmass (Real.sqrt (2 * Knel)) 1
    (Real.sqrt_pos_of_pos (by linarith))
    (fun f Nt Ns _ _ a ha hvt hvs => by
      simpa only [one_mul] using
        asymTorusInteractingMeasureIso_exponentialMomentBound_cutoff_of_nelson
          Lt Ls P mass hmass Knel hKnel_pos hKnel_bound f Nt Ns a ha hvt hvs)
    Nt Ns a hNt hNs ha hvolt hvols ha0

/-- **The isotropic UV continuum limit has the Green-controlled exponential moment bound.**
Thin wrapper over `…_of_nelson` with the (volume-`(Lt,Ls)`-dependent) Nelson constant supplied by
`asymNelson_exponential_estimate_iso`. -/
theorem asymTorusIso_measureHasGreenMomentBound
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (Nt Ns : ℕ → ℕ) (a : ℕ → ℝ)
    (hNt : ∀ k, NeZero (Nt k)) (hNs : ∀ k, NeZero (Ns k)) (ha : ∀ k, 0 < a k)
    (hvolt : ∀ k, (Nt k : ℝ) * a k = Lt) (hvols : ∀ k, (Ns k : ℝ) * a k = Ls)
    (ha0 : Filter.Tendsto a Filter.atTop (nhds 0)) :
    ∃ (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls))) (K : ℝ),
      IsProbabilityMeasure μ ∧ 0 < K ∧ MeasureHasGreenMomentBound Ls mass hmass K 1 μ := by
  obtain ⟨Knel, hKnel_pos, hKnel_bound⟩ :=
    asymNelson_exponential_estimate_iso P mass hmass Lt Ls hLt.out hLs.out
  obtain ⟨μ, hμ_prob, hMHGMB⟩ := asymTorusIso_measureHasGreenMomentBound_of_nelson Lt Ls
    P mass hmass Knel hKnel_pos hKnel_bound Nt Ns a hNt hNs ha hvolt hvols ha0
  exact ⟨μ, Real.sqrt (2 * Knel), hμ_prob, Real.sqrt_pos_of_pos (by linarith), hMHGMB⟩

/-- **Conditional cylinder Green-moment input from a volume-uniform *interacting* exp-moment.**

Given a *single* constant `K` bounding the **interacting** exponential moment
`∫ exp|ωf| dμ_int ≤ K·exp(σ²)` uniformly across all periods `L` (at fixed `Ls`) — the genuine
volume-uniformity (`Z⁻¹ ≥ e^{-p|Λ|}` pressure cancels the linear lower bound `e^{c|Λ|}`; a
cluster-expansion-level fact for P(φ)₂, see `docs/cylinder-conditional-inputs-provability.md` §4) —
the isotropic construction supplies the full IR family for `routeBPrime_cylinder_OS`: periods
`Lt n = (n+1)·Ls → ∞` (rational-compatible, so the UV limit exists at each `n`), UV-continuum
measures `μ n`, and `AsymTorusSequenceHasUniformGreenMomentBound` with the single constant `K`.

Each `μ n` is built by `asymTorusIso_measureHasGreenMomentBound_of_cutoff` along the exactly-
isotropic sequence `Ns_k = k+1`, `a_k = Ls/(k+1)`, `Nt_k = (n+1)(k+1)` (so `Nt_k·a_k = Lt n`,
`Ns_k·a_k = Ls`, `a_k → 0`).

NB: the hypothesis is on the **interacting** moment, *not* the Nelson `L²` moment `∫ e^{-2V}` —
the latter genuinely grows like `e^{f|Λ|}` (free energy) and is never volume-uniform. -/
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

/-- Even isotropic grids beyond Stage-C thresholds `L₀`, `a₀` and the
method-of-images constraint `1 ≤ Lt`.  The identities `Nt·a = Lt` and
`Ns·a = Ls` are preserved, `Nt` is even, and `a → 0`. -/
theorem exists_absForm_thresholded_cylinder_grids
    (L₀ a₀ : ℝ) (hL₀ : 0 < L₀) (ha₀ : 0 < a₀) :
    ∃ (N₀ S : ℕ) (LtFam : ℕ → ℝ)
      (M Ns : ℕ → ℕ → ℕ) (a : ℕ → ℕ → ℝ),
      (∀ n, Fact (0 < LtFam n)) ∧
      Filter.Tendsto LtFam Filter.atTop Filter.atTop ∧
      (∀ n, 1 ≤ LtFam n) ∧
      (∀ n, L₀ ≤ LtFam n) ∧
      (∀ n k, NeZero (M n k)) ∧
      (∀ n k, NeZero (Ns n k)) ∧
      (∀ n k, 0 < a n k) ∧
      (∀ n k, ((2 * M n k : ℕ) : ℝ) * a n k = LtFam n) ∧
      (∀ n k, (Ns n k : ℝ) * a n k = Ls) ∧
      (∀ n k, a n k ≤ a₀) ∧
      (∀ n, Filter.Tendsto (a n) Filter.atTop (nhds 0)) := by
  have hLs_pos : 0 < Ls := hLs.out
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (max L₀ (1 : ℝ) / Ls)
  obtain ⟨S, hS⟩ := exists_nat_ge (Ls / (2 * a₀))
  let LtFam : ℕ → ℝ := fun n => ((N₀ + n + 1 : ℕ) : ℝ) * Ls
  let M : ℕ → ℕ → ℕ := fun n k => (N₀ + n + 1) * (S + k + 1)
  let Ns : ℕ → ℕ → ℕ := fun _ k => 2 * (S + k + 1)
  let a : ℕ → ℕ → ℝ := fun _ k => Ls / (2 * ((S + k + 1 : ℕ) : ℝ))
  have hLt_pos : ∀ n, 0 < LtFam n := fun n => by
    dsimp [LtFam]
    positivity
  have hLtfact : ∀ n, Fact (0 < LtFam n) := fun n => ⟨hLt_pos n⟩
  have hmax : max L₀ (1 : ℝ) ≤ (N₀ : ℝ) * Ls :=
    (div_le_iff₀ hLs_pos).mp hN₀
  refine ⟨N₀, S, LtFam, M, Ns, a, hLtfact, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- LtFam n = (N₀+n+1)·Ls → ∞. Do not reuse the (n:ℝ)+1 tendsto proof:
    -- the first factor is ↑(N₀+n+1), not ↑n+1.
    have hmono : StrictMono (fun n : ℕ => N₀ + n + 1) := by
      intro i j hij
      omega
    have hcast : Filter.Tendsto (fun n : ℕ => ((N₀ + n + 1 : ℕ) : ℝ))
        Filter.atTop Filter.atTop :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp hmono.tendsto_atTop
    simpa [LtFam] using Filter.Tendsto.atTop_mul_const hLs_pos hcast
  · intro n
    dsimp [LtFam]
    have h1 : (1 : ℝ) ≤ max L₀ (1 : ℝ) := le_max_right _ _
    have hN : (N₀ : ℝ) * Ls ≤ ((N₀ + n + 1 : ℕ) : ℝ) * Ls :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) hLs_pos.le
    exact h1.trans (hmax.trans hN)
  · intro n
    dsimp [LtFam]
    have hL : L₀ ≤ max L₀ (1 : ℝ) := le_max_left _ _
    have hN : (N₀ : ℝ) * Ls ≤ ((N₀ + n + 1 : ℕ) : ℝ) * Ls :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) hLs_pos.le
    exact hL.trans (hmax.trans hN)
  · intro n k
    dsimp [M]
    exact ⟨by positivity⟩
  · intro n k
    dsimp [Ns]
    exact ⟨by positivity⟩
  · intro n k
    dsimp [a]
    positivity
  · intro n k
    dsimp [LtFam, M, a]
    push_cast
    field_simp
  · intro n k
    dsimp [Ns, a]
    push_cast
    field_simp
  · intro n k
    dsimp [a]
    have hden : (Ls / (2 * a₀) : ℝ) ≤ ((S + k + 1 : ℕ) : ℝ) :=
      hS.trans (Nat.cast_le.mpr (by omega))
    have ha₀' : 0 < 2 * a₀ := mul_pos (by norm_num) ha₀
    have hLs_le : Ls ≤ (2 * a₀) * (S + k + 1 : ℕ) :=
      (div_le_iff₀ ha₀').mp hden
    have hpos : 0 < (2 * ((S + k + 1 : ℕ) : ℝ)) := by positivity
    rw [div_le_iff₀ hpos]
    convert hLs_le using 1
    ring
  · -- a n k = Ls / (2(S+k+1)) → 0, same algebra as the even-grid
    -- `tendsto_one_div_add_atTop_nhds_zero_nat` family in this file, with offset S.
    intro n
    dsimp [a]
    have hmono : StrictMono (fun k : ℕ => S + k + 1) := by
      intro i j hij
      omega
    have hcast : Filter.Tendsto (fun k : ℕ => ((S + k + 1 : ℕ) : ℝ))
        Filter.atTop Filter.atTop :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp hmono.tendsto_atTop
    have hinv : Filter.Tendsto
        (fun k : ℕ => (1 : ℝ) / ((S + k + 1 : ℕ) : ℝ))
        Filter.atTop (nhds 0) := by
      simpa [one_div] using tendsto_inv_atTop_zero.comp hcast
    have h2 : Filter.Tendsto
        (fun k : ℕ => (Ls / 2) * (1 / ((S + k + 1 : ℕ) : ℝ)))
        Filter.atTop (nhds 0) := by
      simpa using hinv.const_mul (Ls / 2)
    have heq : (fun k : ℕ => Ls / (2 * ((S + k + 1 : ℕ) : ℝ))) =
        fun k : ℕ => (Ls / 2) * (1 / ((S + k + 1 : ℕ) : ℝ)) := by
      ext k
      rw [mul_one_div, div_div]
    rw [heq]
    exact h2

/-- The even-time UV construction transfers a thresholded `|f|`-form
exponential-moment estimate to the torus weak limit, together with OS2 and
no-wrap cylinder reflection positivity.

The cutoff premise is required only on the selected sequence (already
beyond `(L₀, a₀)` when the caller uses
`exists_absForm_thresholded_cylinder_grids`).  The cylinder seminorm is an
input so one `embed_l2_uniform_bound` witness can be shared across infrared
periods. -/
theorem asymTorusIso_measureHasCylinderExpMomentBound_of_absForm_withNoWrapRP
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (K C : ℝ) (hK_pos : 0 < K) (hC_pos : 0 < C)
    (q : Seminorm ℝ (CylinderTestFunction Ls))
    (hq_l2 : ∀ f : CylinderTestFunction Ls,
      l2InnerProduct (cylinderToTorusEmbed Lt Ls f)
        (cylinderToTorusEmbed Lt Ls f) ≤ q f ^ 2)
    (M Ns : ℕ → ℕ) (a : ℕ → ℝ)
    (hM : ∀ k, NeZero (M k)) (hNs : ∀ k, NeZero (Ns k))
    (ha : ∀ k, 0 < a k)
    (hvolt : ∀ k, ((2 * M k : ℕ) : ℝ) * a k = Lt)
    (hvols : ∀ k, (Ns k : ℝ) * a k = Ls)
    (ha0 : Filter.Tendsto a Filter.atTop (nhds 0))
    (hcutoff : ∀ k,
      letI : NeZero (M k) := hM k
      letI : NeZero (Ns k) := hNs k
      ∀ F : AsymTorusTestFunction Lt Ls,
        Integrable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
          Real.exp (|ω F|))
          (asymTorusInteractingMeasureIso Lt Ls (2 * M k) (Ns k) (a k)
            P mass (ha k) hmass) ∧
        ∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
          Real.exp (|ω F|)
            ∂(asymTorusInteractingMeasureIso Lt Ls (2 * M k) (Ns k) (a k)
              P mass (ha k) hmass) ≤
          K * Real.exp (C *
            ∫ ω : Configuration (AsymLatticeField (2 * M k) (Ns k)),
              (ω (fun x => |asymLatticeTestFnIso Lt Ls (2 * M k) (Ns k) (a k)
                F x|)) ^ 2
              ∂(latticeGaussianMeasureAsym (2 * M k) (Ns k) (a k)
                mass (ha k) hmass))) :
    ∃ μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)),
      IsProbabilityMeasure μ ∧
      MeasureHasCylinderExpMomentBound Ls K (C * mass⁻¹ ^ 2) q μ ∧
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
  have hcutoff_sub : ∀ n,
      letI : NeZero (2 * M (φ n)) := hNt (φ n)
      letI : NeZero (Ns (φ n)) := hNs (φ n)
      ∀ F : AsymTorusTestFunction Lt Ls,
        Integrable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
          Real.exp (|ω F|)) (ν n) ∧
        ∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
          Real.exp (|ω F|) ∂(ν n) ≤
          K * Real.exp (C *
            ∫ ω : Configuration (AsymLatticeField (2 * M (φ n)) (Ns (φ n))),
              (ω (fun x => |asymLatticeTestFnIso Lt Ls (2 * M (φ n)) (Ns (φ n))
                (a (φ n)) F x|)) ^ 2
              ∂(latticeGaussianMeasureAsym (2 * M (φ n)) (Ns (φ n)) (a (φ n))
                mass (ha (φ n)) hmass)) := by
    intro n
    haveI := hM (φ n)
    haveI := hNs (φ n)
    intro F
    simpa [ν] using hcutoff (φ n) F
  have hμ_exp :
      MeasureHasCylinderExpMomentBound Ls K (C * mass⁻¹ ^ 2) q μ :=
    asymTorusIso_measureHasCylinderExpMomentBound_of_raw_sampling_of_seminorm
      Lt Ls mass hmass K C hK_pos.le hC_pos.le q hq_l2
      (fun n => 2 * M (φ n)) (fun n => Ns (φ n)) (fun n => a (φ n))
      (fun n => hNt (φ n)) (fun n => hNs (φ n)) (fun n => ha (φ n))
      (fun n => hvolt (φ n)) (fun n => hvols (φ n)) (ha0.comp hφ_atTop)
      ν μ hν_prob hμ_prob hbc hcutoff_sub
  have hμ_os2 := asymTorusIso_limit_satisfies_OS2 Lt Ls P mass hmass
    (fun k => 2 * M k) Ns a hNt hNs ha hvolt hvols ha0 μ φ hφ_mono hconv
  refine ⟨μ, hμ_prob, hμ_exp, (fun _ => hμ_os2), ?_⟩
  intro R hR hLtR n f c hf
  let sigmaSq : ℕ → CylinderTestFunction Ls → ℝ := fun k h =>
    haveI := hM (φ k)
    haveI := hNs (φ k)
    ∫ ω : Configuration (AsymLatticeField (2 * M (φ k)) (Ns (φ k))),
      (ω (fun x => |asymLatticeTestFnIso Lt Ls (2 * M (φ k)) (Ns (φ k))
        (a (φ k)) (cylinderToTorusEmbed Lt Ls h) x|)) ^ 2
      ∂(latticeGaussianMeasureAsym (2 * M (φ k)) (Ns (φ k)) (a (φ k))
        mass (ha (φ k)) hmass)
  apply cylinderRPMatrixNonnegative_of_link_limit Lt Ls ν μ hν_prob hμ_prob hbc
    (fun k => a (φ k)) (ha0.comp hφ_atTop) sigmaSq K C hK_pos hC_pos
  · intro k h
    dsimp [sigmaSq]
    exact integral_nonneg fun _ => sq_nonneg _
  · intro k t h
    dsimp [sigmaSq]
    exact asymCylinderLatticeAbsSecondMoment_smul Lt Ls
      (2 * M (φ k)) (Ns (φ k)) (a (φ k)) mass (ha (φ k)) hmass t h
  · intro hseq hseq0
    simpa [sigmaSq] using
      (asymCylinderLatticeAbsSecondMoment_tendsto_zero_of_tendsto Lt Ls mass hmass
        (fun k => 2 * M (φ k)) (fun k => Ns (φ k)) (fun k => a (φ k))
        (fun k => by letI := hM (φ k); infer_instance)
        (fun k => hNs (φ k)) (fun k => ha (φ k)) hseq hseq0)
  · intro k h
    haveI := hM (φ k)
    haveI := hNs (φ k)
    obtain ⟨hint_torus, hle_torus⟩ := hcutoff_sub k (cylinderToTorusEmbed Lt Ls h)
    obtain ⟨hint_cyl, heq⟩ := cylinderPullback_expMoment_eq Ls Lt (ν k) h hint_torus
    exact ⟨hint_cyl, heq.le.trans hle_torus⟩
  · intro k
    haveI := hM (φ k)
    haveI := hNs (φ k)
    exact asymTorusInteractingMeasureIso_cylinderLinkRPMatrix_span_noWrap
      Lt Ls P (a (φ k)) mass (ha (φ k)) hmass (M (φ k)) (Ns (φ k))
      (hvolt (φ k)) (hvols (φ k)) R hR hLtR n f c hf

/-- Apply the thresholded `|f|`-form UV construction at every infrared period
of an explicit grid family already past `(L₀, a₀)` and `Lt ≥ 1`. -/
theorem asymTorusIso_cylinderUniformCylinderExpMomentBound_of_absForm_grids
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (K C : ℝ) (hK_pos : 0 < K) (hC_pos : 0 < C)
    (q : Seminorm ℝ (CylinderTestFunction Ls)) (_hq : Continuous q)
    (hq_l2 : ∀ (L : ℝ) [Fact (0 < L)], 1 ≤ L →
      ∀ f : CylinderTestFunction Ls,
        l2InnerProduct (cylinderToTorusEmbed L Ls f)
          (cylinderToTorusEmbed L Ls f) ≤ q f ^ 2)
    (LtFam : ℕ → ℝ) (hLtFam : ∀ n, Fact (0 < LtFam n))
    (hLt1 : ∀ n, 1 ≤ LtFam n)
    (M Ns : ℕ → ℕ → ℕ) (a : ℕ → ℕ → ℝ)
    (hM : ∀ n k, NeZero (M n k)) (hNs : ∀ n k, NeZero (Ns n k))
    (ha : ∀ n k, 0 < a n k)
    (hvolt : ∀ n k, ((2 * M n k : ℕ) : ℝ) * a n k = LtFam n)
    (hvols : ∀ n k, (Ns n k : ℝ) * a n k = Ls)
    (ha0 : ∀ n, Filter.Tendsto (a n) Filter.atTop (nhds 0))
    (hcutoff : ∀ n k,
      letI : NeZero (M n k) := hM n k
      letI : NeZero (Ns n k) := hNs n k
      letI : Fact (0 < LtFam n) := hLtFam n
      ∀ F : AsymTorusTestFunction (LtFam n) Ls,
        Integrable (fun ω : Configuration (AsymTorusTestFunction (LtFam n) Ls) =>
          Real.exp (|ω F|))
          (asymTorusInteractingMeasureIso (LtFam n) Ls
            (2 * M n k) (Ns n k) (a n k) P mass (ha n k) hmass) ∧
        ∫ ω : Configuration (AsymTorusTestFunction (LtFam n) Ls),
          Real.exp (|ω F|)
            ∂(asymTorusInteractingMeasureIso (LtFam n) Ls
              (2 * M n k) (Ns n k) (a n k) P mass (ha n k) hmass) ≤
          K * Real.exp (C *
            ∫ ω : Configuration (AsymLatticeField (2 * M n k) (Ns n k)),
              (ω (fun x => |asymLatticeTestFnIso (LtFam n) Ls (2 * M n k) (Ns n k)
                (a n k) F x|)) ^ 2
              ∂(latticeGaussianMeasureAsym (2 * M n k) (Ns n k) (a n k)
                mass (ha n k) hmass))) :
    ∃ μ : ∀ n, Measure (Configuration (AsymTorusTestFunction (LtFam n) Ls)),
      (∀ n, IsProbabilityMeasure (μ n)) ∧
      AsymTorusSequenceHasUniformCylinderExpMomentBound
        Ls K (C * mass⁻¹ ^ 2) q LtFam hLtFam μ ∧
      AsymTorusSequenceHasCylinderOS2Symmetry Ls LtFam hLtFam μ ∧
      (∀ n,
        CylinderMeasureNoWrapReflectionPositive (LtFam n) Ls
          (@cylinderPullbackMeasure (LtFam n) Ls (hLtFam n) hLs (μ n))) := by
  have hbound : ∀ n,
      letI : Fact (0 < LtFam n) := hLtFam n
      ∃ μ : Measure (Configuration (AsymTorusTestFunction (LtFam n) Ls)),
        IsProbabilityMeasure μ ∧
        MeasureHasCylinderExpMomentBound Ls K (C * mass⁻¹ ^ 2) q μ ∧
        (∀ hμ_prob : IsProbabilityMeasure μ,
          @AsymTorusOS2_TranslationInvariance (LtFam n) Ls (hLtFam n) hLs μ hμ_prob ∧
          @AsymTorusOS2_TimeReflectionInvariance (LtFam n) Ls (hLtFam n) hLs μ hμ_prob) ∧
        CylinderMeasureNoWrapReflectionPositive (LtFam n) Ls
          (@cylinderPullbackMeasure (LtFam n) Ls (hLtFam n) hLs μ) := by
    intro n
    letI : Fact (0 < LtFam n) := hLtFam n
    exact asymTorusIso_measureHasCylinderExpMomentBound_of_absForm_withNoWrapRP
      (LtFam n) Ls P mass hmass K C hK_pos hC_pos q
      (fun f => hq_l2 (LtFam n) (hLt1 n) f)
      (M n) (Ns n) (a n) (hM n) (hNs n) (ha n)
      (hvolt n) (hvols n) (ha0 n)
      (fun k => by
        letI : NeZero (M n k) := hM n k
        letI : NeZero (Ns n k) := hNs n k
        intro F
        exact hcutoff n k F)
  choose μ hμ_prob hμ_exp hμ_os2 hμ_rp using hbound
  have hμ_exp_seq : AsymTorusSequenceHasUniformCylinderExpMomentBound
      Ls K (C * mass⁻¹ ^ 2) q LtFam hLtFam μ := by
    exact Filter.Eventually.of_forall fun n => by
      letI : Fact (0 < LtFam n) := hLtFam n
      simpa [MeasureHasCylinderExpMomentBound] using hμ_exp n
  have hμ_os2_seq : AsymTorusSequenceHasCylinderOS2Symmetry Ls LtFam hLtFam μ := by
    constructor
    · intro n
      letI : Fact (0 < LtFam n) := hLtFam n
      haveI : IsProbabilityMeasure (μ n) := hμ_prob n
      intro v f
      simpa [AsymTorusOS2_TranslationInvariance, asymTorusGeneratingFunctional] using
        (hμ_os2 n (hμ_prob n)).1 v f
    · intro n
      letI : Fact (0 < LtFam n) := hLtFam n
      haveI : IsProbabilityMeasure (μ n) := hμ_prob n
      intro f
      simpa [AsymTorusOS2_TimeReflectionInvariance, asymTorusGeneratingFunctional] using
        (hμ_os2 n (hμ_prob n)).2 f
  exact ⟨μ, hμ_prob, hμ_exp_seq, hμ_os2_seq, hμ_rp⟩

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

This axiom is **not** consumed by `cylinderIso_OS_of_RP_OS2`.  The headline uses
the proved thresholded `|f|`-form
`asymInteracting_expMoment_volume_uniform_absForm_thresholded` instead, so its
footprint is the named Layer A/B2 inputs of that theorem together with
`GaussianField.embed_l2_uniform_bound`.  The exact `C · Var_free(f)` form for
signed `f` remains unrecovered (cross-term cancellation). Do not treat this
axiom, or the headline, as a Newman discharge.

Layer A (`asymInteracting_mgf_gaussianDominated`) is quartic-only; Layer B2
(`asymInteractingVariance_le_freeVariance_Lt_uniform`) is a torus wrapper of a
lattice axiom, not a discharge. The Layer C assembly in `AsymSignedSplit.lean`
inherits both and does not make this axiom a theorem. -/
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

Quartic-only (`P.n = 4`). Consumes the proved thresholded `|f|`-form
`asymInteracting_expMoment_volume_uniform_absForm_thresholded`, not the
monolithic axiom `asymInteracting_expMoment_volume_uniform`. The public
conclusion type is unchanged. Newman / FSS / transfer-gap / bridge axioms
remain as named inputs of the thresholded theorem; this is not a discharge
of those inputs, and it is not a Newman or DDJ producer. OS2 is proved from
the heterogeneous lattice construction, and reflection positivity is carried
through the no-wrap limit. `GaussianField.embed_l2_uniform_bound` remains in
the footprint.

Not compiled on this MacBook. `#print axioms` is Colab / remote CI only
(`LOCAL_COLAB_LAKE_BUILD.md`). Do not treat this rewire as certified until
that certificate exists. -/
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
  obtain ⟨K, C, L₀, a₀, hK_pos, hC_pos, hL₀, ha₀, hThresh⟩ :=
    asymInteracting_expMoment_volume_uniform_absForm_thresholded P hP mass hmass Ls
  obtain ⟨q, hq_cont, hq_bound⟩ :=
    GaussianField.embed_l2_uniform_bound (Ls := Ls)
  obtain ⟨_N₀, _S, LtFam, M, Ns, a, hLtFam, hLt_tend, hLt1, hLtL0,
      hM, hNs, ha, hvolt, hvols, ha_le, ha0⟩ :=
    exists_absForm_thresholded_cylinder_grids Ls L₀ a₀ hL₀ ha₀
  have hC_cyl_pos : 0 < C * mass⁻¹ ^ 2 :=
    mul_pos hC_pos (sq_pos_of_pos (inv_pos.mpr hmass))
  have hq_l2 : ∀ (L : ℝ) [Fact (0 < L)], 1 ≤ L →
      ∀ f : CylinderTestFunction Ls,
        l2InnerProduct (cylinderToTorusEmbed L Ls f)
          (cylinderToTorusEmbed L Ls f) ≤ q f ^ 2 := by
    intro L _ hL1 f
    simpa [Pphi2.cylinderToTorusEmbed, GaussianField.cylinderToTorusEmbed]
      using hq_bound L hL1 f
  have hcutoff : ∀ n k,
      letI : NeZero (M n k) := hM n k
      letI : NeZero (Ns n k) := hNs n k
      letI : Fact (0 < LtFam n) := hLtFam n
      ∀ F : AsymTorusTestFunction (LtFam n) Ls,
        Integrable (fun ω : Configuration (AsymTorusTestFunction (LtFam n) Ls) =>
          Real.exp (|ω F|))
          (asymTorusInteractingMeasureIso (LtFam n) Ls
            (2 * M n k) (Ns n k) (a n k) P mass (ha n k) hmass) ∧
        ∫ ω : Configuration (AsymTorusTestFunction (LtFam n) Ls),
          Real.exp (|ω F|)
            ∂(asymTorusInteractingMeasureIso (LtFam n) Ls
              (2 * M n k) (Ns n k) (a n k) P mass (ha n k) hmass) ≤
          K * Real.exp (C *
            ∫ ω : Configuration (AsymLatticeField (2 * M n k) (Ns n k)),
              (ω (fun x => |asymLatticeTestFnIso (LtFam n) Ls (2 * M n k) (Ns n k)
                (a n k) F x|)) ^ 2
              ∂(latticeGaussianMeasureAsym (2 * M n k) (Ns n k) (a n k)
                mass (ha n k) hmass)) := by
    intro n k
    letI : NeZero (M n k) := hM n k
    letI : NeZero (Ns n k) := hNs n k
    letI : Fact (0 < LtFam n) := hLtFam n
    intro F
    exact hThresh (LtFam n) (2 * M n k) (Ns n k) (a n k) (ha n k)
      (hvolt n k) (hvols n k) (ha_le n k) (hLtL0 n) F
  obtain ⟨μ, hμ_prob, hμ_exp, hμ_os2, hμ_noWrap⟩ :=
    asymTorusIso_cylinderUniformCylinderExpMomentBound_of_absForm_grids
      Ls P mass hmass K C hK_pos hC_pos q hq_cont hq_l2
      LtFam hLtFam hLt1 M Ns a hM hNs ha hvolt hvols ha0 hcutoff
  exact routeBPrime_cylinder_OS_of_uniform_cylinderExpMoment Ls
    K (C * mass⁻¹ ^ 2) hK_pos hC_cyl_pos q hq_cont LtFam hLtFam hLt_tend
    μ hμ_prob hμ_exp
    (fun φ ν hν_prob hφ hcf K' C' q' hK' hC' hq' hExp => by
      letI : IsProbabilityMeasure ν := hν_prob
      exact cylinderMeasureReflectionPositive_of_noWrap_limit Ls
        (fun k => LtFam (φ k)) (hLt_tend.comp hφ.tendsto_atTop)
        (fun k => @cylinderPullbackMeasure (LtFam (φ k)) Ls
          (hLtFam (φ k)) hLs (μ (φ k)))
        ν hcf (fun k => hμ_noWrap (φ k)) K' C' hK' hC' q' hq' hExp)
    hμ_os2

end Pphi2

end
