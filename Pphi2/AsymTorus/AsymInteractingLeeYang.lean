/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# lee-yang adapter for Layer A (Newman MGF)

Audited `mrdouglasny/lee-yang` at `d48ee59243afb5e30a3de3ccc90eae2d51806537`.
The finite-Ising Newman bound and the Griffiths–Simon *inequality* passage
are theorems. They do **not** apply to Wick interacting φ⁴ on
`interactingLatticeMeasureAsym` until that measure is exhibited as a
Griffiths–Simon limit of ferromagnetic Ising approximants (lee-yang A3,
deliberately deferred).

This file wires the matching inequality and records the missing hypotheses.
It does **not** convert `asymInteracting_mgf_gaussianDominated` into a
theorem. Do not restore the all-`P` quantifier. Do not weaken pphi2 to the
free field.

## What lee-yang actually proves

* `newman_mgf_le_gaussian` / `newman_absMgf_le_two_exp`
  (`LeeYang/Measure/NewmanPolynomial.lean`) — Newman for a
  `PairedUnitCircleFactorization`: a finite palindromic unit-circle /
  integer-weight polynomial MGF, not a Wick lattice measure.
* `newman_mgf_le_gaussian_of_griffithsSimon` /
  `newman_absMgf_le_two_exp_of_griffithsSimon`
  (`LeeYang/Measure/GriffithsSimon.lean`) — if a target MGF is a pointwise
  limit of approximants that already obey Newman, with converging
  variances, then the limit obeys Newman. The Wick measure as a GS limit
  of Ising is **not** constructed.
* `isingPartitionMv_isPolydiskZeroFree` / `isingDiagonal_leeYangCircle`
  (`LeeYang/Measure/IsingLeeYang.lean`) — *edge-product* ferromagnetic Ising
  polynomials / Asano. Each edge carries its own copy of the endpoint spins,
  so this is not the Gibbs partition polynomial of a shared-spin model.
* `sharedSpinIsingPartitionMv_isPolydiskZeroFree` /
  `sharedSpinIsingDiagonal_leeYangCircle` / `sharedSpinIsingMgf_even` /
  `sharedSpinIsingMgf_natWeights_eq_diagonal`
  (`LeeYang/Measure/SharedSpinIsing.lean`, lee-yang branch
  `codex/newman-shared-spin`, **not** at the pinned `d48ee59`) — the genuine
  finite-volume Lee-Yang circle theorem: for `J ≥ 0` on a loopless edge set
  the shared-spin Gibbs polynomial is polydisk zero-free (Asano-Ruelle edge
  induction via `asanoHadamard_ne_zero`), its integer-weight diagonal has all
  roots on the unit circle, and the MGF of `∑ w_i σ_i` is a normalized
  evaluation of that diagonal at `e^{2t}`. Still no continuum lattice and no
  Wick `:P(φ):`.
* `IsLeeYang` (`LeeYang/Measure/Newman.lean`) — planned, not defined.

## Missing hypotheses for the live axiom

Comparison fields of `AsymWickPhi4GriffithsSimonData` are now theorems for
the canonical interacting MGF of `⟨ω, f⟩`: Z₂ evenness, `e^{|x|} ≤ e^x + e^{-x}`,
finite-lattice `exp(|⟨ω,f⟩|)` integrability (GFF MGF + bounded Boltzmann
weight), and `Var ≤ E[X²]` by taking variance to be the second moment.
Wick site factors are identified as `boltzmannWeightAsym_eq_siteProduct`.

The remaining producer is `AsymWickPhi4IsingApproximants`: ferromagnetic
Ising approximants of those *Wick* site factors (Simon VIII.3, not the free
field and not a non-Wick quartic) whose linear statistics `⟨ω, f⟩` admit a
`PairedUnitCircleFactorization` and whose MGFs/variances tendsto
`asymInteractingMgf` and `∫ (ω f)²`. Uniform exponential integrability of
the full-lattice Ising approximants (unbounded pair couplings) is the
analytic risk. Until that bundle is inhabited, Layer A remains an axiom.

Two independent gaps stand between the shared-spin Lee-Yang theorem above and
that bundle, and neither is plumbing:

1. **Root pairing.** `sharedSpinIsingMgf_natWeights_eq_diagonal` exhibits the
   finite-Ising MGF as a normalized evaluation of a real palindromic
   polynomial whose roots all lie on the unit circle, but
   `PairedUnitCircleFactorization` additionally wants the roots paired as
   `e^{±iθ_k}` together with the cosh-product MGF identity and the variance
   identity. `pairedUnitCircleFactorization_of_unitCircleRoots` still takes
   all three as hypotheses; producing them is the palindromic reduction
   `Q(X) = X^n R(X + X⁻¹)` plus `R`'s real splitting on `[-2, 2)`.
2. **Griffiths-Simon block spins.** The Wick site factor `exp(-a² :P(φ):_c)`
   must be exhibited as a limit of block-spin sums of `±1` spins with
   ferromagnetic couplings, and the full-lattice approximants must converge
   with their MGFs and second moments — the uniform exponential
   integrability noted above.
-/

import LeeYang.Measure.GriffithsSimon
import Pphi2.AsymTorus.AsymExpMomentDischarge
import Pphi2.GeneralResults.GaussianExpMoment

noncomputable section

open MeasureTheory MeasureTheory.Measure GaussianField

namespace Pphi2

/-- Canonical MGF of the linear statistic `⟨ω, f⟩` under the Wick interacting
lattice measure. -/
noncomputable def asymInteractingMgf (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f : AsymLatticeField Nt Ns) (t : ℝ) : ℝ :=
  ∫ ω, Real.exp (t * ω f)
    ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass)

/-- Canonical absolute MGF `∫ exp(|t ⟨ω, f⟩|)`. At `t = 1` this is the
Layer A left-hand side. -/
noncomputable def asymInteractingAbsMgf (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f : AsymLatticeField Nt Ns) (t : ℝ) : ℝ :=
  ∫ ω, Real.exp (|t * ω f|)
    ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass)

/-- `exp(|t ⟨ω, f⟩|)` is integrable on the finite lattice: the free pairing is
Gaussian, and the Wick Boltzmann weight is bounded. This is not Newman. -/
theorem interactingLatticeMeasureAsym_integrable_exp_abs
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f : AsymLatticeField Nt Ns) (t : ℝ) :
    Integrable (fun ω => Real.exp (|t * ω f|))
      (interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) := by
  set Tcov := latticeCovarianceAsymGJ Nt Ns a mass ha hmass
  have hμ : latticeGaussianMeasureAsym Nt Ns a mass ha hmass =
      GaussianField.measure Tcov := rfl
  have hGFF : Integrable (fun ω : Configuration (AsymLatticeField Nt Ns) =>
      Real.exp (|t * ω f|)) (latticeGaussianMeasureAsym Nt Ns a mass ha hmass) := by
    rw [hμ]
    simpa [abs_mul] using (gaussian_exp_abs_moment Tcov f |t|).1
  exact interactingLatticeMeasureAsym_integrable_of_gff Nt Ns P a mass ha hmass
    _ hGFF

/-- Signed exponential `exp(t ⟨ω, f⟩)` is integrable by domination. -/
theorem interactingLatticeMeasureAsym_integrable_exp
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f : AsymLatticeField Nt Ns) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * ω f))
      (interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) := by
  have habs :=
    interactingLatticeMeasureAsym_integrable_exp_abs Nt Ns P a mass ha hmass f t
  refine habs.mono
    (Real.measurable_exp.comp
      (measurable_const.mul (configuration_eval_measurable f))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (le_abs_self _)

/-- Second moment of `⟨ω, f⟩` under the interacting measure. -/
theorem interactingLatticeMeasureAsym_integrable_sq
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f : AsymLatticeField Nt Ns) :
    Integrable (fun ω => (ω f) ^ 2)
      (interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) := by
  set Tcov := latticeCovarianceAsymGJ Nt Ns a mass ha hmass
  have hμ : latticeGaussianMeasureAsym Nt Ns a mass ha hmass =
      GaussianField.measure Tcov := rfl
  have hGFF : Integrable (fun ω : Configuration (AsymLatticeField Nt Ns) =>
      (ω f) ^ 2) (latticeGaussianMeasureAsym Nt Ns a mass ha hmass) := by
    rw [hμ]
    simpa [sq] using pairing_product_integrable Tcov f f
  exact interactingLatticeMeasureAsym_integrable_of_gff Nt Ns P a mass ha hmass
    _ hGFF

/-- Z₂ evenness of the interacting MGF: `φ ↦ -φ` leaves the Wick measure
invariant, so `M(-t) = M(t)`. -/
theorem asymInteractingMgf_even (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f : AsymLatticeField Nt Ns) (t : ℝ) :
    asymInteractingMgf Nt Ns P a mass ha hmass f (-t) =
      asymInteractingMgf Nt Ns P a mass ha hmass f t := by
  set μ := interactingLatticeMeasureAsym Nt Ns P a mass ha hmass
  set Tpb := configurationPullback (negCLM (E := AsymLatticeField Nt Ns))
  have hmap : μ.map Tpb = μ :=
    interactingLatticeMeasureAsym_map_neg Nt Ns P a mass ha hmass
  have hT : Measurable Tpb := measurable_configurationPullback _
  have hint : Integrable (fun ω => Real.exp (t * ω f)) μ :=
    interactingLatticeMeasureAsym_integrable_exp Nt Ns P a mass ha hmass f t
  have hasm : AEStronglyMeasurable (fun ω => Real.exp (t * ω f)) (μ.map Tpb) := by
    rw [hmap]; exact hint.aestronglyMeasurable
  have hpull :
      ∫ ω, Real.exp (t * ω f) ∂(μ.map Tpb) =
        ∫ ω, Real.exp (t * Tpb ω f) ∂μ :=
    integral_map hT.aemeasurable hasm
  have hneg : ∀ ω, Tpb ω f = -ω f := fun ω => by
    change (configurationPullback negCLM ω) f = -ω f
    rw [configurationPullback_apply, negCLM_apply, map_neg]
  unfold asymInteractingMgf
  calc ∫ ω, Real.exp ((-t) * ω f) ∂μ
      = ∫ ω, Real.exp (t * Tpb ω f) ∂μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
          simp [hneg ω, mul_neg, neg_mul]
    _ = ∫ ω, Real.exp (t * ω f) ∂(μ.map Tpb) := hpull.symm
    _ = ∫ ω, Real.exp (t * ω f) ∂μ := by rw [hmap]

/-- Pointwise `e^{|x|} ≤ e^x + e^{-x}` integrates to the `K = 2` comparison. -/
theorem asymInteractingAbsMgf_le_two_mgf (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f : AsymLatticeField Nt Ns) (t : ℝ) :
    asymInteractingAbsMgf Nt Ns P a mass ha hmass f t ≤
      asymInteractingMgf Nt Ns P a mass ha hmass f t +
        asymInteractingMgf Nt Ns P a mass ha hmass f (-t) := by
  set μ := interactingLatticeMeasureAsym Nt Ns P a mass ha hmass
  have hpos :=
    interactingLatticeMeasureAsym_integrable_exp Nt Ns P a mass ha hmass f t
  have hneg :=
    interactingLatticeMeasureAsym_integrable_exp Nt Ns P a mass ha hmass f (-t)
  have habs :=
    interactingLatticeMeasureAsym_integrable_exp_abs Nt Ns P a mass ha hmass f t
  have hsum : Integrable (fun ω => Real.exp (t * ω f) + Real.exp ((-t) * ω f)) μ :=
    hpos.add (by simpa [neg_mul] using hneg)
  unfold asymInteractingAbsMgf asymInteractingMgf
  have hadd :
      ∫ ω, Real.exp (t * ω f) + Real.exp ((-t) * ω f) ∂μ =
        (∫ ω, Real.exp (t * ω f) ∂μ) + ∫ ω, Real.exp ((-t) * ω f) ∂μ :=
    integral_add hpos (by simpa [neg_mul] using hneg)
  rw [← hadd]
  refine integral_mono habs hsum fun ω => ?_
  simpa [neg_mul] using Real.exp_abs_le (t * ω f)

/-- Bundle that would turn lee-yang's Griffiths–Simon MGF passage into the
Layer A Newman bound on `interactingLatticeMeasureAsym`.

No constructor from thin air is provided: constructing the Ising
approximants is the remaining Griffiths–Simon / Wick-φ⁴ work (lee-yang A3 +
pphi2 A4). The comparison fields are filled by
`AsymWickPhi4GriffithsSimonData.of_griffithsSimon` once `GriffithsSimonMGFData`
for `asymInteractingMgf` is supplied. -/
structure AsymWickPhi4GriffithsSimonData
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f : AsymLatticeField Nt Ns) where
  mgf absMgf : ℝ → ℝ
  variance : ℝ
  gs : GriffithsSimonMGFData mgf variance
  mgf_even : ∀ t, mgf (-t) = mgf t
  abs_le_two_mgf : ∀ t, absMgf t ≤ mgf t + mgf (-t)
  integrable_abs :
    Integrable (fun ω => Real.exp (|ω f|))
      (interactingLatticeMeasureAsym Nt Ns P a mass ha hmass)
  absMgf_one :
    absMgf 1 =
      ∫ ω, Real.exp (|ω f|)
        ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass)
  /-- Newman's RHS uses variance; the live axiom uses the second moment.
  `Var ≤ E[X²]` makes this the only comparison needed. -/
  variance_le_second_moment :
    variance ≤
      ∫ ω, (ω f) ^ 2
        ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass)

/-- Conditional Newman bound: Griffiths–Simon MGF data for the pushforward
of `interactingLatticeMeasureAsym` along `ω ↦ ω f` imply the live Layer A
inequality. This does **not** discharge `asymInteracting_mgf_gaussianDominated`;
it records the exact remaining producer. The quartic / `f ≥ 0` binders match
the axiom and are not used in the inequality step. -/
theorem asymInteracting_mgf_gaussianDominated_of_griffithsSimon
    (P : InteractionPolynomial) (_hP : P.n = 4) (mass : ℝ) (hmass : 0 < mass)
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (ha : 0 < a)
    (f : AsymLatticeField Nt Ns) (_hf : ∀ x, 0 ≤ f x)
    (h : AsymWickPhi4GriffithsSimonData Nt Ns P a mass ha hmass f) :
    Integrable (fun ω => Real.exp (|ω f|))
      (interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) ∧
    ∫ ω, Real.exp (|ω f|)
      ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) ≤
    2 * Real.exp ((1 / 2) *
      ∫ ω, (ω f) ^ 2
        ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass)) := by
  refine ⟨h.integrable_abs, ?_⟩
  have hN :=
    newman_absMgf_le_two_exp_of_griffithsSimon h.gs h.mgf_even h.abs_le_two_mgf
      (1 : ℝ)
  have hident :
      ∫ ω, Real.exp (|ω f|)
        ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) ≤
      2 * Real.exp ((1 : ℝ) ^ 2 * h.variance / 2) := by
    simpa [h.absMgf_one] using hN
  have hvar : (1 : ℝ) ^ 2 * h.variance / 2 = h.variance / 2 := by ring
  have hle :
      h.variance / 2 ≤
        (∫ ω, (ω f) ^ 2
          ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass)) / 2 :=
    div_le_div_of_nonneg_right h.variance_le_second_moment (by norm_num : (0 : ℝ) ≤ 2)
  have hdiv :
      (∫ ω, (ω f) ^ 2
        ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass)) / 2 =
      (1 / 2) *
        ∫ ω, (ω f) ^ 2
          ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) := by
    rw [div_eq_mul_inv, one_div, mul_comm]
  calc
    ∫ ω, Real.exp (|ω f|)
      ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) ≤
        2 * Real.exp ((1 : ℝ) ^ 2 * h.variance / 2) := hident
    _ = 2 * Real.exp (h.variance / 2) := by rw [hvar]
    _ ≤ 2 * Real.exp ((1 / 2) *
          ∫ ω, (ω f) ^ 2
            ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass)) := by
      rw [← hdiv]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) (by positivity)

/-- Fill every comparison field of `AsymWickPhi4GriffithsSimonData` from the
canonical interacting MGF. The remaining input is Griffiths–Simon data for
that MGF (Ising approximants of the Wick site factors). -/
noncomputable def AsymWickPhi4GriffithsSimonData.of_griffithsSimon
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f : AsymLatticeField Nt Ns)
    (gs : GriffithsSimonMGFData
      (asymInteractingMgf Nt Ns P a mass ha hmass f)
      (∫ ω, (ω f) ^ 2
        ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass))) :
    AsymWickPhi4GriffithsSimonData Nt Ns P a mass ha hmass f where
  mgf := asymInteractingMgf Nt Ns P a mass ha hmass f
  absMgf := asymInteractingAbsMgf Nt Ns P a mass ha hmass f
  variance := ∫ ω, (ω f) ^ 2
    ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass)
  gs := gs
  mgf_even := fun t =>
    asymInteractingMgf_even Nt Ns P a mass ha hmass f t
  abs_le_two_mgf := fun t =>
    asymInteractingAbsMgf_le_two_mgf Nt Ns P a mass ha hmass f t
  integrable_abs := by
    have h :=
      interactingLatticeMeasureAsym_integrable_exp_abs Nt Ns P a mass ha hmass f 1
    exact h.congr (ae_of_all _ fun ω => by simp)
  absMgf_one := by
    simp [asymInteractingAbsMgf]
  variance_le_second_moment := le_rfl

/-- Remaining lee-yang A3 producer: ferromagnetic Ising approximants of the
Wick site factors `exp(-a² :P(φ):_c)` whose linear statistics `⟨ω, f⟩` are
paired unit-circle polynomials converging to the interacting Wick MGF.

This is **not** inhabited. Do not fill it with the free field or a non-Wick
quartic. Only `P.n = 4` is expected to work (Simon–Griffiths). -/
structure AsymWickPhi4IsingApproximants
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f : AsymLatticeField Nt Ns) where
  pairCount : ℕ → ℕ
  scale : ℕ → ℕ+
  approxMgf : ℕ → ℝ → ℝ
  approxVar : ℕ → ℝ
  paired : ∀ n,
    PairedUnitCircleFactorization (pairCount n) (scale n)
      (approxMgf n) (approxVar n)
  mgf_tendsto : ∀ t,
    Filter.Tendsto (fun n => approxMgf n t) Filter.atTop
      (nhds (asymInteractingMgf Nt Ns P a mass ha hmass f t))
  var_tendsto :
    Filter.Tendsto approxVar Filter.atTop
      (nhds (∫ ω, (ω f) ^ 2
        ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass)))

/-- Package finite-Ising paired Newman data into the Layer A bundle.
Does not construct the approximants. -/
noncomputable def AsymWickPhi4GriffithsSimonData.of_isingApproximants
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f : AsymLatticeField Nt Ns)
    (h : AsymWickPhi4IsingApproximants Nt Ns P a mass ha hmass f) :
    AsymWickPhi4GriffithsSimonData Nt Ns P a mass ha hmass f :=
  AsymWickPhi4GriffithsSimonData.of_griffithsSimon Nt Ns P a mass ha hmass f
    (GriffithsSimonMGFData.of_paired h.approxMgf h.approxVar h.paired
      h.mgf_tendsto h.var_tendsto)

end Pphi2

end
