/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2

/-!
# Kernel axiom certificate generator for pphi2

Runs `#print axioms` on the headline theorems and prints the result. The
output is the kernel-authoritative axiom set: anything that does NOT appear
in this trace cannot have leaked through the build, so this is the single
source of truth for "what does the headline depend on".

**Targets**: the five entries in `formalization.yaml` → `main_results`,
plus one secondary regression target.

`main_results` (5):

* `Pphi2.pphi2_existence` — ∃ μ on S'(ℝ²) satisfying OS0–OS4 (conditional).
* `Pphi2.pphi2_main` — a P(Φ)₂ continuum-limit measure satisfies the OS bundle.
* `Pphi2.pphi2_nonGaussianity` — u₄ ≠ 0 (rests on `continuumLimit_nonGaussian`).
* `Pphi2.pphi2_nontrivial` — S₂(f,f) > 0 (rests on `pphi2_nontriviality`).
* `Pphi2.cylinderIso_OS_of_RP_OS2` — cylinder OS0–OS3 assembly
  (conditional on RP + OS2-symmetry + the uniform exp-moment axiom).

Secondary regression targets (not in `formalization.yaml`):

* `Pphi2.pphi2_exists_os_and_massParameter_positive` — the variant
  carrying the (input) mass-parameter positivity; included here as a
  regression check, not as a headline result.
* `Pphi2.asymInteractingVariance_le_freeVariance_Lt_uniform` — the
  Layer-B2 torus statement converted from axiom to theorem in Piece 5.
* `Pphi2.asymInteracting_expMoment_volume_uniform_proof` — the Layer-C
  assembly theorem consuming Layer A and Layer B2 (since 2026-07-13 in
  `AsymSignedSplit.lean`, split-seminorm form).
* `Pphi2.asymInteracting_expMoment_of_signed` — the signed-split recovery
  lemma (sole direct consumer of the sign-restricted Layer A axiom).

Part-A regression targets:

* the direct cylinder exponential-moment predicates, second-moment extractor,
  Prokhorov adapters, and OS compatibility route;
* the massive asymmetric-lattice free-variance bounds, including the
  sitewise-absolute form used by the thresholded cylinder adapter.

**Usage**:

```
lake env lean audit/axiom_report.lean > audit/axiom-report.txt
```

The committed `audit/axiom-report.txt` is the **golden trace**; CI diffs the
fresh run against it (when wired). The two-file split is deliberate:
generator vs. golden output, with the underscore/hyphen difference in the
filename per the hub convention.
-/

#print axioms Pphi2.pphi2_existence
#print axioms Pphi2.pphi2_main
#print axioms Pphi2.pphi2_nonGaussianity
#print axioms Pphi2.pphi2_nontrivial
#print axioms Pphi2.cylinderIso_OS_of_RP_OS2
#print axioms Pphi2.pphi2_exists_os_and_massParameter_positive
#print axioms Pphi2.asymInteractingVariance_le_freeVariance_Lt_uniform
#print axioms Pphi2.asymInteracting_expMoment_volume_uniform_proof
#print axioms Pphi2.asymInteracting_expMoment_of_signed
#print axioms Pphi2.MeasureHasCylinderExpMomentBound
#print axioms Pphi2.MeasureHasLocalCylinderNthExpMomentBound
#print axioms Pphi2.measureHasCylinderExpMomentBound_of_localNth
#print axioms Pphi2.cylinder_uniform_second_moment_of_expMoment
#print axioms Pphi2.cylinderIR_uniform_second_moment
#print axioms Pphi2.CylinderSequenceHasUniformExponentialMomentBound
#print axioms Pphi2.AsymTorusSequenceHasUniformCylinderExpMomentBound
#print axioms Pphi2.AsymTorusSequenceHasUniformLocalCylinderNthExpMomentBound
#print axioms Pphi2.AsymTorusSequenceHasUniformCylinderExpMomentBound.of_localNth
#print axioms Pphi2.cylinderIRLimit_exists_of_eventual_expMoment
#print axioms Pphi2.cylinderIRLimit_exists_of_uniform_cylinderExpMoment
#print axioms Pphi2.routeBPrime_cylinder_OS_of_uniform_cylinderExpMoment
#print axioms Pphi2.routeBPrime_cylinder_OS
#print axioms Pphi2.massEigenvaluesAsym_ge_mass_sq
#print axioms Pphi2.asymFreeVariance_le_mass_inv_sq
#print axioms Pphi2.asymFreeVariance_sitewiseAbs_le_mass_inv_sq
#print axioms Pphi2.circleRestriction_fourierBasis_eq_latticeFourierBasisFun
#print axioms Pphi2.evalAsymTorusAtSite_basisVec
#print axioms Pphi2.asymLatticeTestFnIso_scaled_sq_sum_eq_evalAsymTorusAtSite_sq_sum
#print axioms Pphi2.asymTorusSiteEval_sq_tendsto
#print axioms Pphi2.asymTorusIso_raw_sampling_tendsto_of_siteEval
#print axioms Pphi2.centeredZMod_decay_sum_le_three
#print axioms Pphi2.asymInteractingVariance_le_freeVariance_torus
#print axioms Pphi2.cylinderPullbackMeasure_exponential_moment_of_tendsto_bc
#print axioms Pphi2.asymTorusIso_measureHasCylinderExpMomentBound_of_raw_sampling
#print axioms Pphi2.asymRawSource_asymLatticeTestFnIso_apply
#print axioms Pphi2.asymRawSource_pairing_eq
#print axioms Pphi2.asymTorusIso_measureHasCylinderExpMomentBound_of_cutoff
#print axioms Pphi2.asymTorusInteractingMeasureIso_cylinderExpMoment_of_absVarianceBound
#print axioms Pphi2.asymTorusIso_limit_satisfies_OS2
#print axioms Pphi2.asymTorusIso_measureHasCylinderExpMomentBound_of_cutoff_withNoWrapRP
#print axioms Pphi2.asymTorusIso_measureHasGreenMomentBound_of_cutoff_withNoWrapRP
#print axioms Pphi2.asymTorusIso_measureHasGreenMomentBound_of_cutoff_withNoWrapRP_withUV
#print axioms Pphi2.asymTorusIso_cylinderUniformGreenBound_withUVFamily
#print axioms Pphi2.asymTorusIso_cylinderUniformCylinderExpMomentBound_of_cutoffFamily
#print axioms Pphi2.routeBPrimeIso_cylinder_OS_of_cutoffFamily
#print axioms GaussianField.integral_exp_le_exp_integral_tilted
#print axioms Pphi2.integral_exp_pow_div_nat_le_two_of_tilted_moment
#print axioms Pphi2.wickPolynomial_coercive
#print axioms Pphi2.interactingLatticeMeasureAsym_integrable_exp_of_sub_interaction_le
#print axioms Pphi2.interactingLatticeMeasureAsym_integrable_exp_of_source_control
#print axioms Pphi2.interactingLatticeMeasureAsym_exp_moment_le_exp_of_sub_interaction_le
#print axioms Pphi2.asymWeightedPairing_pow_le
#print axioms Pphi2.asymWeightedLpPow_le_of_sup_of_weightedL1
#print axioms Pphi2.asymWeightedLpPow_le_of_centered_temporal_decay
#print axioms Pphi2.asymRawSource_pointwise_centered_decay
#print axioms Pphi2.asymRawSource_weightedLpPow_le_of_centered_decay
#print axioms Pphi2.finiteLaplacianAsym_map_smul
#print axioms Pphi2.finiteLaplacianAsymFun_asymRawSource_apply
#print axioms Pphi2.periodizeCLM_circlePoint_centered_decay
#print axioms Pphi2.periodizeCLM_circlePoint_centered_second_diff_decay
#print axioms Pphi2.centeredSecondDiffSeminorm
#print axioms Pphi2.centeredSecondDiffSeminorm_continuous
#print axioms Pphi2.schwartz_centered_second_diff_decay
#print axioms Pphi2.asymSourceControl_of_weightedLpPow
#print axioms Pphi2.interactingLatticeMeasureAsym_integrable_exp_of_weightedLpPow
#print axioms Pphi2.interactingLatticeMeasureAsym_exp_moment_le_two_of_weightedLpPow_and_tiltedMoment
