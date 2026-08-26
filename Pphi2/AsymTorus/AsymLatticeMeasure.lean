/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Heterogeneous isotropic lattice measures (Z_Nt × Z_Ns)

The Gaussian (and, downstream, interacting) P(φ)₂ measures on the *heterogeneous* lattice
`AsymLatticeField Nt Ns = ZMod Nt × ZMod Ns → ℝ` with a **single isotropic spacing `a`**
(`a = Lt/Nt = Ls/Ns`). This is the metric-correct replacement for the square
`FinLatticeField 2 N` + geometric-mean-spacing construction: the covariance is
`latticeCovarianceAsymGJ` from gaussian-field, whose lattice→continuum limit is the correct
rectangular-torus Green's function (`lattice_green_tendsto_continuum_asym`), so the rectangle
`Nt ≠ Ns` is carried by the boundary condition, not a distorted metric.

## Main definitions

- `latticeGaussianMeasureAsym` — centered GJ-normalized Gaussian measure on
  `Configuration (AsymLatticeField Nt Ns)`, covariance `latticeCovarianceAsymGJ`.

## Design

Mirrors gaussian-field's square `latticeGaussianMeasure`, with `FinLatticeField d N`
replaced by `AsymLatticeField Nt Ns` and the isotropic covariance. The cell area is `a²`
and the volume `Nt·Ns·a² = Lt·Ls`, so the `d = 2` Glimm–Jaffe normalisation factor is
`(a²)^{-1/2} = 1/a` (built into `latticeCovarianceAsymGJ`).
-/

import Lattice.AsymCovariance
import Lattice.AsymFiniteField
import Pphi2.InteractingMeasure.LatticeMeasure
import GaussianField.Symmetry

noncomputable section

open GaussianField MeasureTheory
open scoped BigOperators

namespace Pphi2

/-! The `DyninMityaginSpace (AsymLatticeField)` instance now lives in GaussianField
(`Lattice.AsymFiniteField`, imported above). -/

/-- The centered Gaussian measure on the heterogeneous isotropic lattice
`ZMod Nt × ZMod Ns` (**Glimm–Jaffe-aligned normalisation**).

Constructed via `GaussianField.measure` from the GJ-aligned isotropic covariance CLM
`latticeCovarianceAsymGJ`. Has covariance kernel `a^{-2} Q⁻¹` (cell area `a²`), so the
lattice two-point function converges to the rectangular continuum Green's function on
`T_{Lt,Ls}` as `a → 0` (`Nt, Ns → ∞`, `Nt/Ns = Lt/Ls`). -/
noncomputable def latticeGaussianMeasureAsym (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    @Measure (Configuration (AsymLatticeField Nt Ns)) instMeasurableSpaceConfiguration :=
  GaussianField.measure (latticeCovarianceAsymGJ Nt Ns a mass ha hmass)

/-- The heterogeneous lattice Gaussian measure is a probability measure. -/
instance latticeGaussianMeasureAsym_isProbability (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    @IsProbabilityMeasure (Configuration (AsymLatticeField Nt Ns))
      instMeasurableSpaceConfiguration
      (latticeGaussianMeasureAsym Nt Ns a mass ha hmass) := by
  unfold latticeGaussianMeasureAsym
  exact GaussianField.measure_isProbability (latticeCovarianceAsymGJ Nt Ns a mass ha hmass)

/-- The two-point function of the heterogeneous lattice Gaussian measure equals the GJ-aligned
isotropic covariance bilinear form. -/
theorem latticeGaussianMeasureAsym_cross_moment (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) (f g : AsymLatticeField Nt Ns) :
    ∫ ω : Configuration (AsymLatticeField Nt Ns),
      (ω f) * (ω g) ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) =
    GaussianField.covariance (latticeCovarianceAsymGJ Nt Ns a mass ha hmass) f g := by
  unfold latticeGaussianMeasureAsym
  exact GaussianField.cross_moment_eq_covariance _ f g

/-! ## Wick ordering constant (heterogeneous lattice) -/

/-- The Wick ordering constant on the heterogeneous lattice (GJ-aligned diagonal of the
lattice propagator):

  `c_a = (a²)⁻¹ · (1/|Λ|) · Σ_k 1/λ_k = (a²)⁻¹ · (1/(Nt·Ns)) · Tr(Q⁻¹)`

where `λ_k` are the eigenvalues of `massOperatorAsym = -Δ_a + m²`. This is the variance of
the lattice GFF site value `ω(δ_x)` under `latticeGaussianMeasureAsym` (translation-invariant,
so the `Q⁻¹` diagonal equals `(1/|Λ|) Tr(Q⁻¹)`, which is basis-independent — hence the clean
sum over the Hermitian eigenvalues). The factor `(a²)⁻¹` is the `d = 2` GJ Riemann-sum factor. -/
def wickConstantAsym (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass : ℝ) : ℝ :=
  (a ^ 2 : ℝ)⁻¹ *
  ((1 / Fintype.card (AsymLatticeSites Nt Ns) : ℝ) *
    ∑ k : AsymLatticeSites Nt Ns, (massEigenvaluesAsym Nt Ns a mass k)⁻¹)

/-- The heterogeneous Wick constant is positive when `mass > 0`. -/
theorem wickConstantAsym_pos (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    0 < wickConstantAsym Nt Ns a mass := by
  unfold wickConstantAsym
  refine mul_pos (inv_pos.mpr (pow_pos ha 2)) (mul_pos ?_ ?_)
  · exact div_pos one_pos (by exact_mod_cast Fintype.card_pos)
  · exact Finset.sum_pos
      (fun k _ => inv_pos.mpr (massOperatorMatrixAsym_eigenvalues_pos Nt Ns a mass ha hmass k))
      Finset.univ_nonempty

/-! ## Interaction functional (heterogeneous lattice) -/

/-- The heterogeneous lattice interaction as a function of the configuration `ω`:
`V_a(ω) = a² · Σ_{x : ZMod Nt × ZMod Ns} :P(ω(δ_x)):_{c_a}`. -/
def interactionFunctionalAsym (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) :
    Configuration (AsymLatticeField Nt Ns) → ℝ :=
  fun ω => a ^ 2 * ∑ x : AsymLatticeSites Nt Ns,
    wickPolynomial P (wickConstantAsym Nt Ns a mass) (ω (asymLatticeDelta Nt Ns x))

private theorem wickMonomial_measurable_asym {α : Type*} (n : ℕ) (c : ℝ) (f : α → ℝ)
    {mα : MeasurableSpace α}
    (hf : @Measurable α ℝ mα (borel ℝ) f) :
    @Measurable α ℝ mα (borel ℝ) (fun x => wickMonomial n c (f x)) := by
  suffices h : ∀ k ≤ n, @Measurable α ℝ mα (borel ℝ) (fun x => wickMonomial k c (f x)) from
    h n le_rfl
  intro k hk
  induction k using Nat.strongRecOn with
  | ind k ih =>
    match k with
    | 0 => exact measurable_const
    | 1 => exact hf
    | k + 2 =>
      simp only [wickMonomial_succ_succ]
      exact (hf.mul (ih (k + 1) (by omega) (by omega))).sub
        (measurable_const.mul (ih k (by omega) (by omega)))

theorem interactionFunctionalAsym_measurable (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) :
    @Measurable (Configuration (AsymLatticeField Nt Ns)) ℝ
      instMeasurableSpaceConfiguration (borel ℝ)
      (interactionFunctionalAsym Nt Ns P a mass) := by
  unfold interactionFunctionalAsym
  apply Measurable.const_mul
  apply Finset.measurable_sum _ (fun x _ => ?_)
  unfold wickPolynomial
  apply Measurable.add
  · exact Measurable.const_mul
      (wickMonomial_measurable_asym P.n (wickConstantAsym Nt Ns a mass) _
        (configuration_eval_measurable _)) _
  · exact Finset.measurable_sum _ (fun m _ =>
      Measurable.const_mul
        (wickMonomial_measurable_asym m (wickConstantAsym Nt Ns a mass) _
          (configuration_eval_measurable _)) _)

/-- The heterogeneous interaction functional is bounded below. -/
theorem interactionFunctionalAsym_bounded_below (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (_hmass : 0 < mass) :
    ∃ B : ℝ, ∀ ω : Configuration (AsymLatticeField Nt Ns),
    interactionFunctionalAsym Nt Ns P a mass ω ≥ -B := by
  obtain ⟨A, _hA_pos, hA_bound⟩ := wickPolynomial_bounded_below P (wickConstantAsym Nt Ns a mass)
  refine ⟨a ^ 2 * Fintype.card (AsymLatticeSites Nt Ns) * A, fun ω => ?_⟩
  unfold interactionFunctionalAsym
  have ha_pow : (0 : ℝ) < a ^ 2 := pow_pos ha 2
  calc a ^ 2 * ∑ x : AsymLatticeSites Nt Ns,
        wickPolynomial P (wickConstantAsym Nt Ns a mass) (ω (asymLatticeDelta Nt Ns x))
      ≥ a ^ 2 * ∑ _x : AsymLatticeSites Nt Ns, (-A) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt ha_pow)
        exact Finset.sum_le_sum (fun x _ => hA_bound _)
    _ = -(a ^ 2 * Fintype.card (AsymLatticeSites Nt Ns) * A) := by
        simp [Finset.sum_const, mul_comm]; ring

/-- The heterogeneous interaction is a sum of single-site Wick polynomials. -/
theorem interactionFunctionalAsym_single_site
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) :
    ∃ v : AsymLatticeSites Nt Ns → (ℝ → ℝ),
      ∀ ω : Configuration (AsymLatticeField Nt Ns),
        interactionFunctionalAsym Nt Ns P a mass ω =
          a ^ 2 * ∑ x, v x (ω (asymLatticeDelta Nt Ns x)) :=
  ⟨fun _x τ => wickPolynomial P (wickConstantAsym Nt Ns a mass) τ, fun _ω => rfl⟩

/-! ## Boltzmann weight, partition function, interacting measure -/

/-- The Boltzmann weight `exp(-V_a(ω))` on the heterogeneous lattice. -/
def boltzmannWeightAsym (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) :
    Configuration (AsymLatticeField Nt Ns) → ℝ :=
  fun ω => Real.exp (-(interactionFunctionalAsym Nt Ns P a mass ω))

theorem boltzmannWeightAsym_pos (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ)
    (ω : Configuration (AsymLatticeField Nt Ns)) :
    0 < boltzmannWeightAsym Nt Ns P a mass ω :=
  Real.exp_pos _

/-- The Boltzmann weight is the product of Wick site factors
`exp(-a² :P(φ_x):_c)`. Pair couplings live in the free Gaussian, not here. -/
theorem boltzmannWeightAsym_eq_siteProduct
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ)
    (ω : Configuration (AsymLatticeField Nt Ns)) :
    boltzmannWeightAsym Nt Ns P a mass ω =
      ∏ x : AsymLatticeSites Nt Ns,
        Real.exp (-(a ^ 2 *
          wickPolynomial P (wickConstantAsym Nt Ns a mass)
            (ω (asymLatticeDelta Nt Ns x)))) := by
  unfold boltzmannWeightAsym interactionFunctionalAsym
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum]

theorem boltzmannWeightAsym_integrable (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    Integrable (boltzmannWeightAsym Nt Ns P a mass)
      (latticeGaussianMeasureAsym Nt Ns a mass ha hmass) := by
  obtain ⟨B, hB_bound⟩ := interactionFunctionalAsym_bounded_below Nt Ns P a mass ha hmass
  apply Integrable.of_bound (C := Real.exp B)
  · exact (interactionFunctionalAsym_measurable Nt Ns P a mass).neg.exp.aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro ω
    simp only [boltzmannWeightAsym, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp_of_le (by linarith [hB_bound ω])

/-- The partition function `Z_a = ∫ exp(-V_a) dμ_{GFF,a}` on the heterogeneous lattice. -/
def partitionFunctionAsym (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) : ℝ :=
  ∫ ω, boltzmannWeightAsym Nt Ns P a mass ω
    ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass)

theorem partitionFunctionAsym_pos (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    0 < partitionFunctionAsym Nt Ns P a mass ha hmass := by
  unfold partitionFunctionAsym
  have hinteg := boltzmannWeightAsym_integrable Nt Ns P a mass ha hmass
  rw [integral_pos_iff_support_of_nonneg
    (fun ω => le_of_lt (boltzmannWeightAsym_pos Nt Ns P a mass ω)) hinteg]
  have hsup : Function.support (boltzmannWeightAsym Nt Ns P a mass) = Set.univ := by
    ext ω; simp [Function.mem_support, ne_of_gt (boltzmannWeightAsym_pos Nt Ns P a mass ω)]
  rw [hsup]
  exact Measure.measure_univ_pos.mpr (IsProbabilityMeasure.ne_zero _)

/-- The P(φ)₂ interacting measure on the heterogeneous isotropic lattice:
`dμ_a = (1/Z_a)·exp(-V_a(ω))·dμ_{GFF,a}(ω)`. -/
def interactingLatticeMeasureAsym (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    @Measure (Configuration (AsymLatticeField Nt Ns)) instMeasurableSpaceConfiguration :=
  (ENNReal.ofReal (partitionFunctionAsym Nt Ns P a mass ha hmass))⁻¹ •
    (latticeGaussianMeasureAsym Nt Ns a mass ha hmass).withDensity
      (fun ω => ENNReal.ofReal (boltzmannWeightAsym Nt Ns P a mass ω))

/-- The heterogeneous interacting lattice measure is a probability measure. -/
theorem interactingLatticeMeasureAsym_isProbability (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    @IsProbabilityMeasure (Configuration (AsymLatticeField Nt Ns))
      instMeasurableSpaceConfiguration
      (interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) := by
  constructor
  have hZ := partitionFunctionAsym_pos Nt Ns P a mass ha hmass
  have hZ_ne : ENNReal.ofReal (partitionFunctionAsym Nt Ns P a mass ha hmass) ≠ 0 :=
    ENNReal.ofReal_pos.mpr hZ |>.ne'
  have hZ_ne_top : ENNReal.ofReal (partitionFunctionAsym Nt Ns P a mass ha hmass) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  unfold interactingLatticeMeasureAsym
  rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (boltzmannWeightAsym_integrable Nt Ns P a mass ha hmass)
    (Filter.Eventually.of_forall (fun ω => le_of_lt (boltzmannWeightAsym_pos Nt Ns P a mass ω)))]
  simp only [smul_eq_mul]
  exact ENNReal.inv_mul_cancel hZ_ne hZ_ne_top

/-! ## Source-tilted exponential integrability -/

/-- A pointwise upper bound on the source exponent after subtracting the interaction
implies integrability under the normalized interacting lattice measure.  The proof only
uses the density representation of that measure: the product of the source exponential
and the Boltzmann weight is bounded by `exp C` under the free Gaussian measure. -/
theorem interactingLatticeMeasureAsym_integrable_exp_of_sub_interaction_le
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (g : AsymLatticeField Nt Ns) (C : ℝ)
    (hbound : ∀ ω : Configuration (AsymLatticeField Nt Ns),
      (ω g) ^ P.n / (P.n : ℝ) -
          interactionFunctionalAsym Nt Ns P a mass ω ≤ C) :
    Integrable
      (fun ω : Configuration (AsymLatticeField Nt Ns) =>
        Real.exp ((ω g) ^ P.n / (P.n : ℝ)))
      (interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) := by
  let μG := latticeGaussianMeasureAsym Nt Ns a mass ha hmass
  let bw := boltzmannWeightAsym Nt Ns P a mass
  have hZ : 0 < partitionFunctionAsym Nt Ns P a mass ha hmass :=
    partitionFunctionAsym_pos Nt Ns P a mass ha hmass
  have hF_meas : Measurable (fun ω : Configuration (AsymLatticeField Nt Ns) =>
      Real.exp ((ω g) ^ P.n / (P.n : ℝ))) := by
    exact Real.measurable_exp.comp
      (((configuration_eval_measurable g).pow_const P.n).div measurable_const)
  have hbw_meas : Measurable (fun ω : Configuration (AsymLatticeField Nt Ns) =>
      ENNReal.ofReal (bw ω)) := by
    exact ENNReal.measurable_ofReal.comp
      ((interactionFunctionalAsym_measurable Nt Ns P a mass).neg.exp)
  have hbw_pos : ∀ ω : Configuration (AsymLatticeField Nt Ns), 0 < bw ω := by
    intro ω
    exact boltzmannWeightAsym_pos Nt Ns P a mass ω
  have hbw_simp : ∀ ω : Configuration (AsymLatticeField Nt Ns),
      (ENNReal.ofReal (bw ω)).toReal = bw ω := by
    intro ω
    exact ENNReal.toReal_ofReal (le_of_lt (hbw_pos ω))
  have hF_wd : Integrable
      (fun ω : Configuration (AsymLatticeField Nt Ns) =>
        Real.exp ((ω g) ^ P.n / (P.n : ℝ)))
      (μG.withDensity (fun ω => ENNReal.ofReal (bw ω))) := by
    apply (integrable_withDensity_iff hbw_meas
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
    simp_rw [hbw_simp]
    apply Integrable.of_bound (C := Real.exp C)
    · exact hF_meas.aestronglyMeasurable.mul
        ((interactionFunctionalAsym_measurable Nt Ns P a mass).neg.exp.aestronglyMeasurable)
    · apply Filter.Eventually.of_forall
      intro ω
      simp only [Real.norm_eq_abs, bw, boltzmannWeightAsym]
      rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le
          (Real.exp_pos _).le), abs_of_nonneg (Real.exp_pos C).le]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      simpa [sub_eq_add_neg] using hbound ω
  unfold interactingLatticeMeasureAsym
  exact hF_wd.smul_measure
    (ENNReal.inv_ne_top.mpr ((ENNReal.ofReal_pos.mpr hZ).ne'))

/-- A finite source-control inequality together with Wick coercivity supplies the pointwise
bound used by `interactingLatticeMeasureAsym_integrable_exp_of_sub_interaction_le`.
The source-control hypothesis is deliberately explicit: proving it uniformly in the lattice
parameters is the analytic finite-volume input, while the density transfer is elementary. -/
theorem interactingLatticeMeasureAsym_integrable_exp_of_source_control
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (g : AsymLatticeField Nt Ns) (η : ℝ) (hη_pos : 0 < η) (hη_lt_one : η < 1)
    (hsource : ∀ ω : Configuration (AsymLatticeField Nt Ns),
      (ω g) ^ P.n / (P.n : ℝ) ≤
        a ^ 2 * ∑ x : AsymLatticeSites Nt Ns,
          ((1 - η) / (P.n : ℝ)) *
            |ω (asymLatticeDelta Nt Ns x)| ^ P.n) :
    Integrable
      (fun ω : Configuration (AsymLatticeField Nt Ns) =>
        Real.exp ((ω g) ^ P.n / (P.n : ℝ)))
      (interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) := by
  obtain ⟨B, _hB_nonneg, hcoercive⟩ :=
    wickPolynomial_coercive P (wickConstantAsym Nt Ns a mass) η hη_pos hη_lt_one
  apply interactingLatticeMeasureAsym_integrable_exp_of_sub_interaction_le
    Nt Ns P a mass ha hmass g (a ^ 2 * Fintype.card (AsymLatticeSites Nt Ns) * B)
  intro ω
  have hsum :
      a ^ 2 * ∑ x : AsymLatticeSites Nt Ns,
          (((1 - η) / (P.n : ℝ)) *
            |ω (asymLatticeDelta Nt Ns x)| ^ P.n - B) ≤
        a ^ 2 * ∑ x : AsymLatticeSites Nt Ns,
          wickPolynomial P (wickConstantAsym Nt Ns a mass)
            (ω (asymLatticeDelta Nt Ns x)) := by
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg a)
    exact Finset.sum_le_sum (fun x _ => hcoercive _)
  calc
    (ω g) ^ P.n / (P.n : ℝ) -
          interactionFunctionalAsym Nt Ns P a mass ω ≤
        a ^ 2 * ∑ x : AsymLatticeSites Nt Ns,
          ((1 - η) / (P.n : ℝ)) *
            |ω (asymLatticeDelta Nt Ns x)| ^ P.n -
          interactionFunctionalAsym Nt Ns P a mass ω := by
      exact sub_le_sub_right (hsource ω) _
    _ = a ^ 2 * ∑ x : AsymLatticeSites Nt Ns,
          (((1 - η) / (P.n : ℝ)) *
            |ω (asymLatticeDelta Nt Ns x)| ^ P.n - B) +
          a ^ 2 * Fintype.card (AsymLatticeSites Nt Ns) * B -
          interactionFunctionalAsym Nt Ns P a mass ω := by
      simp only [interactionFunctionalAsym]
      rw [Finset.sum_sub_distrib]
      simp [Finset.sum_const, mul_comm] <;> ring
    _ ≤ a ^ 2 * Fintype.card (AsymLatticeSites Nt Ns) * B := by
      simp only [interactionFunctionalAsym]
      linarith [hsum]

/-! ## GFF-to-interacting integrability transfer and Z₂ parity -/

/-- If `T` preserves `μ` and the density `f` is `T`-invariant, then `T`
preserves `μ.withDensity f`. -/
private theorem map_withDensity_eq_of_invariant {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {T : α → α} (hT : Measurable T) (hμ : μ.map T = μ)
    {f : α → ℝ≥0∞} (hf : Measurable f) (hfT : ∀ x, f (T x) = f x) :
    (μ.withDensity f).map T = μ.withDensity f := by
  ext s hs
  rw [Measure.map_apply hT hs, withDensity_apply _ (hT hs), withDensity_apply _ hs]
  calc
    ∫⁻ x in T ⁻¹' s, f x ∂μ
        = ∫⁻ x in T ⁻¹' s, f (T x) ∂μ :=
          setLIntegral_congr_fun (hT hs) fun x _ => (hfT x).symm
    _ = ∫⁻ y in s, f y ∂(μ.map T) := (setLIntegral_map hs hf hT).symm
    _ = ∫⁻ y in s, f y ∂μ := by rw [hμ]

/-- The interaction is invariant under the field flip `ω ↦ ω ∘ (-1)`. -/
theorem interactionFunctionalAsym_comp_neg (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ)
    (ω : Configuration (AsymLatticeField Nt Ns)) :
    interactionFunctionalAsym Nt Ns P a mass
        (configurationPullback negCLM ω) =
      interactionFunctionalAsym Nt Ns P a mass ω := by
  unfold interactionFunctionalAsym
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [configurationPullback_apply, negCLM_apply, map_neg, wickPolynomial_neg]

/-- The heterogeneous lattice Gaussian is parity-invariant. -/
theorem latticeGaussianMeasureAsym_map_neg (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    (latticeGaussianMeasureAsym Nt Ns a mass ha hmass).map
        (configurationPullback (negCLM (E := AsymLatticeField Nt Ns))) =
      latticeGaussianMeasureAsym Nt Ns a mass ha hmass := by
  unfold latticeGaussianMeasureAsym
  exact measure_neg_invariant (latticeCovarianceAsymGJ Nt Ns a mass ha hmass)

/-- **Parity invariance of the interacting heterogeneous lattice measure.** -/
theorem interactingLatticeMeasureAsym_map_neg (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    (interactingLatticeMeasureAsym Nt Ns P a mass ha hmass).map
        (configurationPullback (negCLM (E := AsymLatticeField Nt Ns))) =
      interactingLatticeMeasureAsym Nt Ns P a mass ha hmass := by
  unfold interactingLatticeMeasureAsym
  rw [Measure.map_smul]
  congr 1
  refine map_withDensity_eq_of_invariant (measurable_configurationPullback _)
    (latticeGaussianMeasureAsym_map_neg Nt Ns a mass ha hmass)
    (ENNReal.measurable_ofReal.comp
      ((interactionFunctionalAsym_measurable Nt Ns P a mass).neg.exp))
    fun ω => ?_
  unfold boltzmannWeightAsym
  rw [interactionFunctionalAsym_comp_neg]

/-- An observable integrable under the free GFF remains integrable under the
Wick interacting reweighting: `exp(-V)` is bounded because `V` is bounded
below. -/
theorem interactingLatticeMeasureAsym_integrable_of_gff
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (F : Configuration (AsymLatticeField Nt Ns) → ℝ)
    (hF_GFF : Integrable F (latticeGaussianMeasureAsym Nt Ns a mass ha hmass)) :
    Integrable F (interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) := by
  obtain ⟨B, hB⟩ := interactionFunctionalAsym_bounded_below Nt Ns P a mass ha hmass
  have hZ := partitionFunctionAsym_pos Nt Ns P a mass ha hmass
  set μ_GFF := latticeGaussianMeasureAsym Nt Ns a mass ha hmass
  set bw := boltzmannWeightAsym Nt Ns P a mass
  have hbw_pos : ∀ ω, 0 < bw ω := boltzmannWeightAsym_pos Nt Ns P a mass
  have hbw_bound : ∀ ω, bw ω ≤ Real.exp B := fun ω =>
    Real.exp_le_exp_of_le (by linarith [hB ω])
  have hf_dens_meas : Measurable (fun ω => ENNReal.ofReal (bw ω)) :=
    ENNReal.measurable_ofReal.comp
      ((interactionFunctionalAsym_measurable Nt Ns P a mass).neg.exp)
  have hbw_simp : ∀ ω, (ENNReal.ofReal (bw ω)).toReal = bw ω :=
    fun ω => ENNReal.toReal_ofReal (le_of_lt (hbw_pos ω))
  have hF_wd : Integrable F (μ_GFF.withDensity (fun ω => ENNReal.ofReal (bw ω))) := by
    apply (integrable_withDensity_iff hf_dens_meas
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
    simp_rw [hbw_simp]
    apply (hF_GFF.mul_const (Real.exp B)).mono
    · exact hF_GFF.aestronglyMeasurable.mul
        (interactionFunctionalAsym_measurable Nt Ns P a mass).neg.exp.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun ω => by
        simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (hbw_pos ω),
          abs_of_pos (Real.exp_pos B)]
        exact mul_le_mul_of_nonneg_left (hbw_bound ω) (abs_nonneg _)
  unfold interactingLatticeMeasureAsym
  exact hF_wd.smul_measure
    (ENNReal.inv_ne_top.mpr ((ENNReal.ofReal_pos.mpr hZ).ne'))

end Pphi2

end
