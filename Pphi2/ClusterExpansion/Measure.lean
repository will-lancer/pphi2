/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Pphi2.ClusterExpansion.GaussianBase
import Pphi2.ClusterExpansion.Interaction

/-!
# Normalized continuous-spin Gibbs measures

Finite-volume measures are normalized Boltzmann densities with respect to a
finite-dimensional Gaussian probability measure.  The analytic interfaces use
Gaussian integrals and weighted L² conditions.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace Pphi2.ClusterExpansion

variable {Site : Type*}

/-- The one-site partition function relative to a probability base measure. -/
noncomputable def singleSitePartitionFunction
    (μ : Measure ℝ) (P : InteractionPolynomial) (a c : ℝ) : ℝ :=
  ∫ x, singleSiteBoltzmannWeight P a c x ∂μ

theorem singleSiteBoltzmannWeight_integrable
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (P : InteractionPolynomial) (a c : ℝ) :
    Integrable (singleSiteBoltzmannWeight P a c) μ := by
  obtain ⟨A, _, hwick⟩ := wickPolynomial_bounded_below P c
  refine Integrable.of_bound
    (singleSiteBoltzmannWeight_measurable P a c).aestronglyMeasurable
    (Real.exp (a ^ 2 * A)) ?_
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_pos (singleSiteBoltzmannWeight_pos P a c x)]
    apply Real.exp_le_exp_of_le
    have ha : 0 ≤ a ^ 2 := sq_nonneg a
    have hmul := mul_le_mul_of_nonneg_left (hwick x) ha
    linarith

/-- Every real monomial is integrable under a one-dimensional Gaussian. -/
theorem integrable_pow_gaussianReal (variance : ℝ≥0) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k)
      (ProbabilityTheory.gaussianReal 0 variance) := by
  cases k with
  | zero =>
      simpa using (integrable_const (1 : ℝ) :
        Integrable (fun _ : ℝ => (1 : ℝ))
          (ProbabilityTheory.gaussianReal 0 variance))
  | succ k =>
      have hmem : MemLp (id : ℝ → ℝ) (Nat.succ k)
          (ProbabilityTheory.gaussianReal 0 variance) := by
        exact ProbabilityTheory.memLp_id_gaussianReal
          (μ := (0 : ℝ)) (v := variance) (p := (Nat.succ k : ℝ≥0))
      have hnorm : Integrable (fun x : ℝ => ‖x‖ ^ Nat.succ k)
          (ProbabilityTheory.gaussianReal 0 variance) := by
        simpa using hmem.integrable_norm_pow'
      have hmeas : AEStronglyMeasurable (fun x : ℝ => x ^ Nat.succ k)
          (ProbabilityTheory.gaussianReal 0 variance) :=
        (continuous_id.pow _).aestronglyMeasurable
      rw [← integrable_norm_iff hmeas]
      simpa [norm_pow] using hnorm

/-- Every formal real polynomial is Gaussian-integrable. -/
theorem integrable_polynomial_gaussianReal
    (variance : ℝ≥0) (p : Polynomial ℝ) :
    Integrable (fun x : ℝ => p.eval x)
      (ProbabilityTheory.gaussianReal 0 variance) := by
  have heval : (fun x : ℝ => p.eval x) =
      fun x => ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * x ^ i := by
    funext x
    rw [Polynomial.eval_eq_sum_range]
  rw [heval]
  exact integrable_finset_sum _ fun i _ =>
    (integrable_pow_gaussianReal variance i).const_mul (p.coeff i)

/-- The square of a Wick interaction is integrable under every centered
one-dimensional Gaussian. -/
theorem integrable_wickPolynomial_sq_gaussianReal
    (variance : ℝ≥0) (P : InteractionPolynomial) (c : ℝ) :
    Integrable (fun x : ℝ => (wickPolynomial P c x) ^ 2)
      (ProbabilityTheory.gaussianReal 0 variance) := by
  let p := wickPolynomialFormal P c * wickPolynomialFormal P c
  have hp := integrable_polynomial_gaussianReal variance p
  convert hp using 1
  funext x
  simp [p, Polynomial.eval_mul, wickPolynomialFormal_eval, pow_two]

/-- The basic Wick insertion has the required Gaussian-weighted L2 control
against its single-site Boltzmann factor. -/
theorem integrable_wickPolynomial_sq_mul_boltzmann
    (variance : ℝ≥0) (P : InteractionPolynomial) (a c : ℝ) :
    Integrable (fun x : ℝ =>
      (wickPolynomial P c x) ^ 2 * singleSiteBoltzmannWeight P a c x)
      (ProbabilityTheory.gaussianReal 0 variance) := by
  obtain ⟨A, _, hwick⟩ := wickPolynomial_bounded_below P c
  have hsquare := integrable_wickPolynomial_sq_gaussianReal variance P c
  have hmajorant : Integrable (fun x : ℝ =>
      Real.exp (a ^ 2 * A) * (wickPolynomial P c x) ^ 2)
      (ProbabilityTheory.gaussianReal 0 variance) :=
    hsquare.const_mul _
  apply hmajorant.mono'
  · exact (((wickPolynomial_continuous₂ P).comp
      (continuous_const.prodMk continuous_id)).pow 2).mul
        (singleSiteBoltzmannWeight_continuous P a c) |>.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _)
        (le_of_lt (singleSiteBoltzmannWeight_pos P a c x)))]
      calc
        (wickPolynomial P c x) ^ 2 * singleSiteBoltzmannWeight P a c x
            ≤ (wickPolynomial P c x) ^ 2 * Real.exp (a ^ 2 * A) := by
              apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
              apply Real.exp_le_exp_of_le
              have ha : 0 ≤ a ^ 2 := sq_nonneg a
              have := mul_le_mul_of_nonneg_left (hwick x) ha
              linarith
        _ = Real.exp (a ^ 2 * A) * (wickPolynomial P c x) ^ 2 := mul_comm _ _

theorem singleSitePartitionFunction_pos
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (P : InteractionPolynomial) (a c : ℝ) :
    0 < singleSitePartitionFunction μ P a c := by
  unfold singleSitePartitionFunction
  have hint := singleSiteBoltzmannWeight_integrable μ P a c
  rw [integral_pos_iff_support_of_nonneg
    (fun x => le_of_lt (singleSiteBoltzmannWeight_pos P a c x)) hint]
  have hsupport :
      Function.support (singleSiteBoltzmannWeight P a c) = Set.univ := by
    ext x
    simp [Function.mem_support,
      ne_of_gt (singleSiteBoltzmannWeight_pos P a c x)]
  rw [hsupport]
  exact Measure.measure_univ_pos.mpr (IsProbabilityMeasure.ne_zero μ)

/-- The normalized one-site measure
`Z⁻¹ exp (-a² :P(x):_c) dμ(x)`. -/
noncomputable def singleSiteMeasure
    (μ : Measure ℝ) (P : InteractionPolynomial) (a c : ℝ) : Measure ℝ :=
  (ENNReal.ofReal (singleSitePartitionFunction μ P a c))⁻¹ •
    μ.withDensity
      (fun x => ENNReal.ofReal (singleSiteBoltzmannWeight P a c x))

noncomputable instance singleSiteMeasure_isProbability
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (P : InteractionPolynomial) (a c : ℝ) :
    IsProbabilityMeasure (singleSiteMeasure μ P a c) := by
  constructor
  have hZ := singleSitePartitionFunction_pos μ P a c
  have hZ0 : ENNReal.ofReal (singleSitePartitionFunction μ P a c) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hZ).ne'
  have hZtop :
      ENNReal.ofReal (singleSitePartitionFunction μ P a c) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  unfold singleSiteMeasure
  rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (singleSiteBoltzmannWeight_integrable μ P a c)
    (Filter.Eventually.of_forall
      (fun x => le_of_lt (singleSiteBoltzmannWeight_pos P a c x)))]
  simp only [smul_eq_mul]
  exact ENNReal.inv_mul_cancel hZ0 hZtop

/-- The Gaussian single-site measure used by the continuous-spin model. -/
noncomputable def gaussianSingleSiteMeasure
    (P : InteractionPolynomial) (a c : ℝ) (variance : ℝ≥0) : Measure ℝ :=
  singleSiteMeasure (ProbabilityTheory.gaussianReal 0 variance) P a c

noncomputable instance gaussianSingleSiteMeasure_isProbability
    (P : InteractionPolynomial) (a c : ℝ) (variance : ℝ≥0) :
    IsProbabilityMeasure (gaussianSingleSiteMeasure P a c variance) := by
  unfold gaussianSingleSiteMeasure
  infer_instance

/-- The finite-volume partition function. -/
noncomputable def blockPartitionFunction
    (μ : Measure (ContinuousConfig Site))
    (P : InteractionPolynomial) (a c : ℝ) (B : Finset Site) : ℝ :=
  ∫ φ, blockBoltzmannWeight P a c B φ ∂μ

theorem blockPartitionFunction_pos
    (μ : Measure (ContinuousConfig Site)) [IsProbabilityMeasure μ]
    (P : InteractionPolynomial) (a c : ℝ) (B : Finset Site) :
    0 < blockPartitionFunction μ P a c B := by
  unfold blockPartitionFunction
  have hint := blockBoltzmannWeight_integrable μ P a c B
  rw [integral_pos_iff_support_of_nonneg
    (fun φ => le_of_lt (blockBoltzmannWeight_pos P a c B φ)) hint]
  have hsupport :
      Function.support (blockBoltzmannWeight P a c B) = Set.univ := by
    ext φ
    simp [Function.mem_support,
      ne_of_gt (blockBoltzmannWeight_pos P a c B φ)]
  rw [hsupport]
  exact Measure.measure_univ_pos.mpr (IsProbabilityMeasure.ne_zero μ)

/-- The normalized finite-volume density
`Z_B⁻¹ exp (-V_B) dμ`. -/
noncomputable def interactingBlockMeasure
    (μ : Measure (ContinuousConfig Site))
    (P : InteractionPolynomial) (a c : ℝ) (B : Finset Site) :
    Measure (ContinuousConfig Site) :=
  (ENNReal.ofReal (blockPartitionFunction μ P a c B))⁻¹ •
    μ.withDensity
      (fun φ => ENNReal.ofReal (blockBoltzmannWeight P a c B φ))

noncomputable instance interactingBlockMeasure_isProbability
    (μ : Measure (ContinuousConfig Site)) [IsProbabilityMeasure μ]
    (P : InteractionPolynomial) (a c : ℝ) (B : Finset Site) :
    IsProbabilityMeasure (interactingBlockMeasure μ P a c B) := by
  constructor
  have hZ := blockPartitionFunction_pos μ P a c B
  have hZ0 : ENNReal.ofReal (blockPartitionFunction μ P a c B) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hZ).ne'
  have hZtop :
      ENNReal.ofReal (blockPartitionFunction μ P a c B) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  unfold interactingBlockMeasure
  rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (blockBoltzmannWeight_integrable μ P a c B)
    (Filter.Eventually.of_forall
      (fun φ => le_of_lt (blockBoltzmannWeight_pos P a c B φ)))]
  simp only [smul_eq_mul]
  exact ENNReal.inv_mul_cancel hZ0 hZtop

/-- A Gaussian weighted-L² condition for an interaction insertion. -/
def GaussianWeightedL2
    (μ : Measure (ContinuousConfig Site))
    (V insertion : ContinuousConfig Site → ℝ) : Prop :=
  Integrable
    (fun φ => insertion φ ^ 2 * Real.exp (-V φ)) μ

/-- Integral control for one interaction insertion.  Activity constructions
carry one such certificate for each insertion that their forest derivatives
produce.  The interface contains no pointwise supremum over the real spin
space. -/
structure GaussianInteractionControl
    (μ : Measure (ContinuousConfig Site))
    (V insertion : ContinuousConfig Site → ℝ) : Prop where
  interaction_measurable : Measurable V
  insertion_measurable : Measurable insertion
  boltzmann_integrable : Integrable (fun φ => Real.exp (-V φ)) μ
  insertionL2 : GaussianWeightedL2 μ V insertion

end Pphi2.ClusterExpansion
