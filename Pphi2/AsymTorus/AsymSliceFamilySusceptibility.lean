/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.AsymTorus.AsymB5bSingleSlice
import GaussianField.Symmetry

/-!
# Layer-B2 Stage B, hole B-I: slice-family susceptibility bound

This file proves the `hPiece3` input of the B5b composition shell
(`AsymB5bSingleSlice.lean`): the path-measure second moment of a slice FAMILY
observable `ψ ↦ Σ_t ⟨g_t, ψ_t⟩` is bounded by `2/(1-γ)` times the sum of
ground-state single-slice variances, plus a `γ^Nt`-small remainder.

Route (the 7-step design of `planning/b2-stageB-holes-spec.md` §"Hole B-I"):

1. truncate all slices at a common `K` and prove the `K`-uniform bound;
2. expand the square into the double time sum (Fubini on the probability
   path measure with bounded integrands);
3. **mean-zero by parity**: the one-point functions of the odd truncated
   observables vanish, because the interacting asym measure is invariant
   under the field flip `ω ↦ -ω` (`P` is even), and this parity pushes
   forward to the periodic path measure;
4. **cyclic invariance of the path measure** (new, generic over
   `TransferSystem`; candidate for upstreaming to reflection-positivity):
   the kernel-product path density is invariant under the cyclic time shift,
   so every pair `(t, t')` reduces to the two-point function at times
   `(0, t' - t)`;
5. the finite-periodic connected two-point bridge at the OFF-diagonal pair
   `(A_{t,K}, A_{t',K})` (the upstream engine already takes two observables);
6. AM–GM plus the wrap-around geometric sum (`geom_wrap_sum_le`) gives the
   `(1+γ)/(1-γ)`-weighted susceptibility; Piece 1
   (`norm_sq_proj_obsTrunc_omega_le`) converts each perpendicular norm to a
   ground slice variance; the diagonal contributes the remaining `1`, so the
   total constant is `1 + (1+γ)/(1-γ) = 2/(1-γ)`;
7. the landed `K → ∞` engine (`asymSliceObsLinear_pathMeasure_two_point_bound`)
   transfers the `K`-uniform bound to the linear observable.

## Interface deviations (explicit hypotheses, NOT new axioms)

Two finite-volume ground-dominance inputs are NOT derivable from the landed
bricks and are therefore carried as named hypotheses of the headline theorem
(each in the exact shape its future discharge will produce):

* `hDiag` — the diagonal (`t = t'`) one-point bound
  `∫ A_{t,K}(ψ_t)² dμ_path ≤ groundSliceVariance (g t) + C_diag·γ^Nt`.
  The single-slice marginal of the finite-periodic path measure is
  `Z⁻¹·kPow(Nt-1)(x,x)·ν`, which differs from `Ω²·ν` by the positive
  remainder-kernel diagonal — an `O(γ^Nt)` correction requiring the same
  trace/HS input as the two-point remainder.  (The spec's step-6 claim that
  the diagonal is bounded by the ground variance *exactly* is false at finite
  `Nt`.)
* `hRes` — a `K`-UNIFORM constant for the finite-periodic bridge residual
  `finitePeriodicBridgeResidual ≤ C_off·γ^Nt`.  The landed axiom
  `asymFinitePeriodicBridge_remainder_bound` produces a constant *per
  contract pair*, hence `K`-dependent, which the `K → ∞` step cannot use;
  the physically correct constant is `K`-uniform (the residual is controlled
  by `L²`-norms of `A·Ω`, not by `‖A‖_∞`).

Both hypotheses are pure `γ^Nt`-remainder data: the shell
`piece3_pathMeasure_bound_to_freeCovariance_sum` consumes the resulting
remainder `(C_diag·Nt + C_off·Nt²)·γ^Nt` through its abstract `rem` slot.

**Stage C task C3 (per-pair remainder + sharp corollary):** the `hRes` slot is
generalized from a scalar `C_off` to per-pair bounds `r t t'` (theorems
`…_pairwise`; the scalar forms are re-derived as corollaries).  Instantiating
`r t t' := C₂·√gSV(g t)·√gSV(g t')` from the τ-form remainder axiom and
collapsing the double sum by Cauchy–Schwarz (`(Σ√gSV)² ≤ Nt·gSVSum`) yields the
sharp corollaries `…_le_sharp` / `…_le_fixedLs_sharp` with remainder
`C_rem·Nt·γ^(Nt-⌈τ/a⌉)·gSVSum` — one power of `Nt`, closing the Stage-C `a → 0`
corner.

## S2: the fixed-`Ls` a-uniform gap axiom

The axiom `asymTransferGap_uniform_fixedLs` (§S2 of
`planning/b2-route-a-statements.md`, pinned statement verbatim) enters here
with its consumer `asymSliceFamily_pathMeasure_second_moment_le_fixedLs`:
the `γ := exp(-m₀·a)` specialization of the headline theorem, which makes
the `2/(1-γ)` prefactor `a`-uniformly `≤ 2/(m₀·a)`-controlled at fixed `Ls`.

## References

* Glimm–Jaffe, *Quantum Physics*, Ch. 6, 19 (transfer matrix, mass gap).
* Simon, *The P(φ)₂ Euclidean (Quantum) Field Theory*, Ch. VI.
* `reflection-positivity/docs/B2_UNIFORMITY_QUESTION.md` (S2 vet record).
-/

noncomputable section

open MeasureTheory GaussianField ReflectionPositivity
open scoped BigOperators ENNReal

namespace Pphi2

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

variable {Nt Ns : ℕ} [NeZero Nt] [NeZero Ns]

local notation "ν" => (volume : Measure (SpatialField Ns))

/-! ## Generic helper: pushforward of `withDensity` under an invariant map -/

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
        = ∫⁻ x in T ⁻¹' s, f (T x) ∂μ := lintegral_congr fun x => (hfT x).symm
    _ = ∫⁻ y in s, f y ∂(μ.map T) := (setLIntegral_map hs hf hT).symm
    _ = ∫⁻ y in s, f y ∂μ := by rw [hμ]

/-! ## Parity (`Z₂` field symmetry) of the interacting asym measure

`P` is even (`InteractionPolynomial.coeff_odd_eq_zero`), so the Wick-ordered
interaction is even in the field, the Boltzmann weight is parity-invariant,
and — since the centered lattice Gaussian is parity-invariant
(`GaussianField.measure_neg_invariant`) — so is the interacting measure and
its path-measure pushforward. -/

/-- Wick monomials have the parity of their degree:
`:(-x)^n:_c = (-1)^n · :x^n:_c`. -/
theorem wickMonomial_neg : ∀ (n : ℕ) (c x : ℝ),
    wickMonomial n c (-x) = (-1) ^ n * wickMonomial n c x
  | 0, _, _ => by simp
  | 1, _, _ => by simp
  | n + 2, c, x => by
      rw [wickMonomial_succ_succ, wickMonomial_succ_succ,
        wickMonomial_neg (n + 1), wickMonomial_neg n, pow_succ, pow_succ]
      ring

/-- The Wick-ordered interaction polynomial of an even `P` is even:
`:P(-x):_c = :P(x):_c`. -/
theorem wickPolynomial_neg (P : InteractionPolynomial) (c x : ℝ) :
    wickPolynomial P c (-x) = wickPolynomial P c x := by
  unfold wickPolynomial
  congr 1
  · rw [wickMonomial_neg, Even.neg_one_pow P.hn_even, one_mul]
  · refine Finset.sum_congr rfl fun m _ => ?_
    by_cases hm : Odd (m : ℕ)
    · simp [P.coeff_odd_eq_zero m hm]
    · rw [Nat.not_odd_iff_even] at hm
      rw [wickMonomial_neg, Even.neg_one_pow hm, one_mul]

/-- The asym interaction functional is invariant under the field flip
`ω ↦ ω ∘ (-1)`. -/
theorem interactionFunctionalAsym_comp_neg
    (P : InteractionPolynomial) (a mass : ℝ)
    (ω : Configuration (AsymLatticeField Nt Ns)) :
    interactionFunctionalAsym Nt Ns P a mass
        (configurationPullback negCLM ω) =
      interactionFunctionalAsym Nt Ns P a mass ω := by
  unfold interactionFunctionalAsym
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [configurationPullback_apply, negCLM_apply, map_neg, wickPolynomial_neg]

/-- The asym lattice Gaussian measure is parity-invariant. -/
theorem latticeGaussianMeasureAsym_map_neg
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    (latticeGaussianMeasureAsym Nt Ns a mass ha hmass).map
        (configurationPullback (negCLM (E := AsymLatticeField Nt Ns))) =
      latticeGaussianMeasureAsym Nt Ns a mass ha hmass := by
  unfold latticeGaussianMeasureAsym
  exact measure_neg_invariant (latticeCovarianceAsymGJ Nt Ns a mass ha hmass)

/-- **Parity invariance of the interacting asym lattice measure.**  The
Boltzmann weight of the even interaction is parity-invariant and the centered
Gaussian is parity-invariant, hence so is the normalized interacting measure. -/
theorem interactingLatticeMeasureAsym_map_neg
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    (interactingLatticeMeasureAsym Nt Ns P a mass ha hmass).map
        (configurationPullback (negCLM (E := AsymLatticeField Nt Ns))) =
      interactingLatticeMeasureAsym Nt Ns P a mass ha hmass := by
  unfold interactingLatticeMeasureAsym
  rw [Measure.map_smul]
  congr 1
  refine map_withDensity_eq_of_invariant (measurable_configurationPullback _)
    (latticeGaussianMeasureAsym_map_neg (Nt := Nt) (Ns := Ns) a mass ha hmass)
    (ENNReal.measurable_ofReal.comp
      ((interactionFunctionalAsym_measurable Nt Ns P a mass).neg.exp))
    fun ω => ?_
  unfold boltzmannWeightAsym
  rw [interactionFunctionalAsym_comp_neg]

/-- **Parity invariance of the asym periodic path measure.**  Pushes the
lattice parity through the slice/eval factorization. -/
theorem asymPathMeasure_map_neg
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    ((asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).pathMeasure Nt).map
        (fun ψ : ZMod Nt → SpatialField Ns => -ψ) =
      (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).pathMeasure Nt := by
  have hsl : Measurable (⇑(asymSliceEquiv Nt Ns)) := by
    rw [← asymSliceMeasurableEquiv_coe Nt Ns]
    exact (asymSliceMeasurableEquiv Nt Ns).measurable
  have hev : Measurable (evalMapAsym Nt Ns) := measurable_evalMapAsym Nt Ns
  have hneg : Measurable (fun ψ : ZMod Nt → SpatialField Ns => -ψ) := measurable_neg
  set μI := interactingLatticeMeasureAsym Nt Ns P a mass ha hmass with hμI
  have hcomp1 : ((μI.map (evalMapAsym Nt Ns)).map (asymSliceEquiv Nt Ns)) =
      (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).pathMeasure Nt :=
    interactingLatticeMeasureAsym_slice_pushforward_eq_pathMeasure Nt Ns P a mass ha hmass
  have hinter : ((fun ψ : ZMod Nt → SpatialField Ns => -ψ) ∘
      (⇑(asymSliceEquiv Nt Ns) ∘ evalMapAsym Nt Ns)) =
      (⇑(asymSliceEquiv Nt Ns) ∘ evalMapAsym Nt Ns) ∘
        configurationPullback (negCLM (E := AsymLatticeField Nt Ns)) := by
    funext ω
    simp only [Function.comp_apply]
    have hev_neg : evalMapAsym Nt Ns (configurationPullback negCLM ω) =
        -(evalMapAsym Nt Ns ω) := by
      funext x
      simp only [evalMapAsym, configurationPullback_apply, negCLM_apply, map_neg,
        Pi.neg_apply]
    rw [hev_neg, map_neg]
  have key : μI.map ((fun ψ : ZMod Nt → SpatialField Ns => -ψ) ∘
      (⇑(asymSliceEquiv Nt Ns) ∘ evalMapAsym Nt Ns)) =
      μI.map (⇑(asymSliceEquiv Nt Ns) ∘ evalMapAsym Nt Ns) := by
    rw [hinter, ← Measure.map_map (hsl.comp hev) (measurable_configurationPullback _)]
    rw [show μI.map (configurationPullback (negCLM (E := AsymLatticeField Nt Ns))) = μI from
      interactingLatticeMeasureAsym_map_neg (Nt := Nt) (Ns := Ns) P a mass ha hmass]
  calc ((asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).pathMeasure Nt).map
        (fun ψ : ZMod Nt → SpatialField Ns => -ψ)
      = ((μI.map (evalMapAsym Nt Ns)).map (asymSliceEquiv Nt Ns)).map
          (fun ψ : ZMod Nt → SpatialField Ns => -ψ) := by rw [hcomp1]
    _ = μI.map ((fun ψ : ZMod Nt → SpatialField Ns => -ψ) ∘
          (⇑(asymSliceEquiv Nt Ns) ∘ evalMapAsym Nt Ns)) := by
        rw [Measure.map_map hsl hev, Measure.map_map hneg (hsl.comp hev)]
    _ = μI.map (⇑(asymSliceEquiv Nt Ns) ∘ evalMapAsym Nt Ns) := key
    _ = (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).pathMeasure Nt := by
        rw [← Measure.map_map hsl hev, hcomp1]

/-- The asym periodic path measure is a probability measure (pushforward of the
interacting probability measure). -/
theorem asymPathMeasure_isProbability
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    IsProbabilityMeasure
      ((asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).pathMeasure Nt) := by
  have hsl : Measurable (⇑(asymSliceEquiv Nt Ns)) := by
    rw [← asymSliceMeasurableEquiv_coe Nt Ns]
    exact (asymSliceMeasurableEquiv Nt Ns).measurable
  rw [← interactingLatticeMeasureAsym_slice_pushforward_eq_pathMeasure Nt Ns P a mass ha hmass]
  haveI := interactingLatticeMeasureAsym_isProbability Nt Ns P a mass ha hmass
  haveI : IsProbabilityMeasure
      ((interactingLatticeMeasureAsym Nt Ns P a mass ha hmass).map (evalMapAsym Nt Ns)) :=
    Measure.isProbabilityMeasure_map (measurable_evalMapAsym Nt Ns).aemeasurable
  exact Measure.isProbabilityMeasure_map hsl.aemeasurable

/-! ## Oddness and mean-zero of the truncated slice observables -/

omit [NeZero Ns] in
/-- The linear slice observable is odd. -/
theorem asymSliceObsLinear_neg (g x : SpatialField Ns) :
    asymSliceObsLinear g (-x) = -asymSliceObsLinear g x := by
  unfold asymSliceObsLinear
  simp [mul_neg]

omit [NeZero Ns] in
/-- The truncated slice observable is odd (clamp of an odd function with
symmetric bounds). -/
theorem asymSliceObsTrunc_neg (g : SpatialField Ns) {K : ℝ} (hK : 0 ≤ K)
    (x : SpatialField Ns) :
    asymSliceObsTrunc g K (-x) = -asymSliceObsTrunc g K x := by
  unfold asymSliceObsTrunc
  rw [asymSliceObsLinear_neg]
  set t := asymSliceObsLinear g x with ht
  rcases lt_or_ge t (-K) with h1 | h1
  · -- t < -K: both sides equal K
    rw [min_eq_left (by linarith : K ≤ -t), max_eq_right (by linarith : -K ≤ K),
      min_eq_right (by linarith : t ≤ K), max_eq_left h1.le, neg_neg]
  · rcases le_or_gt t K with h2 | h2
    · -- -K ≤ t ≤ K: both sides equal -t
      rw [min_eq_right (by linarith : -t ≤ K), max_eq_right (by linarith : -K ≤ -t),
        min_eq_right h2, max_eq_right h1]
    · -- t > K: both sides equal -K
      rw [min_eq_right (by linarith : -t ≤ K), max_eq_left (by linarith : -t ≤ -K),
        min_eq_left h2.le, max_eq_right (by linarith : -K ≤ K)]

/-- **Mean-zero by parity** (step 3): the one-point function of a truncated
slice observable vanishes under the periodic path measure, because the path
measure is parity-invariant and the observable is odd. -/
theorem asymSliceObsTrunc_pathMeasure_mean_zero
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (h : SpatialField Ns) {K : ℝ} (hK : 0 ≤ K) (t : ZMod Nt) :
    ∫ ψ : ZMod Nt → SpatialField Ns, asymSliceObsTrunc h K (ψ t)
        ∂((asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).pathMeasure Nt)
      = 0 := by
  set μ := (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).pathMeasure Nt
    with hμdef
  have hmeas : Measurable fun ψ : ZMod Nt → SpatialField Ns =>
      asymSliceObsTrunc h K (ψ t) :=
    (asymSliceObsTrunc_measurable h K).comp (measurable_pi_apply t)
  have hinv : μ.map (fun ψ : ZMod Nt → SpatialField Ns => -ψ) = μ :=
    asymPathMeasure_map_neg (Nt := Nt) (Ns := Ns) P a mass ha hmass
  have key : ∫ ψ, asymSliceObsTrunc h K (ψ t) ∂μ =
      -∫ ψ, asymSliceObsTrunc h K (ψ t) ∂μ := by
    calc ∫ ψ, asymSliceObsTrunc h K (ψ t) ∂μ
        = ∫ ψ, asymSliceObsTrunc h K (ψ t)
            ∂(μ.map (fun ψ : ZMod Nt → SpatialField Ns => -ψ)) := by rw [hinv]
      _ = ∫ ψ, asymSliceObsTrunc h K ((-ψ) t) ∂μ :=
          integral_map measurable_neg.aemeasurable hmeas.aestronglyMeasurable
      _ = ∫ ψ, -asymSliceObsTrunc h K (ψ t) ∂μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun ψ => ?_)
          change asymSliceObsTrunc h K ((-ψ) t) = -asymSliceObsTrunc h K (ψ t)
          rw [Pi.neg_apply, asymSliceObsTrunc_neg h hK]
      _ = -∫ ψ, asymSliceObsTrunc h K (ψ t) ∂μ := integral_neg _
  linarith

/-! ## Cyclic invariance of the periodic path measure (step 4)

Generic over any `TransferSystem`; kept in pphi2 for now (candidate for
upstreaming to reflection-positivity). -/

section CyclicShift

variable {S : Type*} [MeasurableSpace S]

/-- The cyclic time shift on periodic paths: `(cyclicShift n c ψ) t = ψ (t + c)`. -/
def cyclicShift (n : ℕ) [NeZero n] (c : ZMod n) (ψ : ZMod n → S) : ZMod n → S :=
  fun t => ψ (t + c)

theorem measurable_cyclicShift (n : ℕ) [NeZero n] (c : ZMod n) :
    Measurable (cyclicShift (S := S) n c) :=
  measurable_pi_lambda _ fun t => measurable_pi_apply (t + c)

private theorem cyclicShift_eq_piCongrLeft (n : ℕ) [NeZero n] (c : ZMod n) :
    cyclicShift (S := S) n c =
      ⇑(MeasurableEquiv.piCongrLeft (fun _ : ZMod n => S) (Equiv.subRight c)) := by
  funext ψ t
  calc cyclicShift n c ψ t = ψ (t + c) := rfl
    _ = (MeasurableEquiv.piCongrLeft (fun _ : ZMod n => S) (Equiv.subRight c)) ψ
          ((Equiv.subRight c) (t + c)) :=
        (MeasurableEquiv.piCongrLeft_apply_apply
          (β := fun _ : ZMod n => S) (Equiv.subRight c) ψ (t + c)).symm
    _ = (MeasurableEquiv.piCongrLeft (fun _ : ZMod n => S) (Equiv.subRight c)) ψ t := by
        simp [Equiv.subRight]

private theorem pi_map_cyclicShift (μ0 : Measure S) [SigmaFinite μ0]
    (n : ℕ) [NeZero n] (c : ZMod n) :
    (Measure.pi (fun _ : ZMod n => μ0)).map (cyclicShift (S := S) n c) =
      Measure.pi (fun _ : ZMod n => μ0) := by
  rw [cyclicShift_eq_piCongrLeft]
  exact (measurePreserving_piCongrLeft (fun _ : ZMod n => μ0) (Equiv.subRight c)).map_eq

omit [MeasurableSpace S] in
private theorem periodicPathDensity_cyclicShift (k : S → S → ℝ) (n : ℕ) [NeZero n]
    (c : ZMod n) (ψ : ZMod n → S) :
    periodicPathDensity k n (cyclicShift n c ψ) = periodicPathDensity k n ψ := by
  change (∏ t : ZMod n, k (ψ (t + c)) (ψ (t + 1 + c))) = ∏ t : ZMod n, k (ψ t) (ψ (t + 1))
  calc (∏ t : ZMod n, k (ψ (t + c)) (ψ (t + 1 + c)))
      = ∏ t : ZMod n, k (ψ (t + c)) (ψ (t + c + 1)) := by
        refine Finset.prod_congr rfl fun t _ => ?_
        rw [add_right_comm]
    _ = ∏ t : ZMod n, k (ψ t) (ψ (t + 1)) := by
        exact Equiv.prod_comp (Equiv.addRight c) fun s => k (ψ s) (ψ (s + 1))

/-- **Cyclic invariance of the periodic path measure** (step 4): the kernel
path measure on `ZMod n → S` is invariant under the cyclic time shift.  The
path density `∏_t k(ψ_t, ψ_{t+1})` is shift-invariant and the product measure
is permutation-invariant. -/
theorem pathMeasure_map_cyclicShift (Ts : TransferSystem S) (n : ℕ) [NeZero n]
    (c : ZMod n) :
    (Ts.pathMeasure n).map (cyclicShift n c) = Ts.pathMeasure n := by
  letI := Ts.ν_sigmaFinite
  unfold TransferSystem.pathMeasure
  rw [Measure.map_smul]
  congr 1
  refine map_withDensity_eq_of_invariant (measurable_cyclicShift n c)
    (pi_map_cyclicShift Ts.ν n c)
    (ENNReal.measurable_ofReal.comp (Ts.pathDensity_measurable n)) fun ψ => ?_
  have := periodicPathDensity_cyclicShift Ts.k n c ψ
  simp only [TransferSystem.pathDensity]
  rw [this]

/-- **Two-point reduction** (step 4, consequence): a path-measure pair
correlation at arbitrary times `(t, t')` equals the two-point function at
times `(0, t' - t)`. -/
theorem pathMeasure_pair_eq_pathTwoPoint (Ts : TransferSystem S) (n : ℕ) [NeZero n]
    (A B : MultiplicationCLMContract Ts.ν) (t t' : ZMod n) :
    ∫ ψ, A.A (ψ t) * B.A (ψ t') ∂(Ts.pathMeasure n) =
      pathTwoPoint Ts A B n (t' - t) := by
  have hmeas : AEStronglyMeasurable
      (fun ψ : ZMod n → S => A.A (ψ 0) * B.A (ψ (t' - t)))
      ((Ts.pathMeasure n).map (cyclicShift n t)) :=
    ((A.A_meas.comp (measurable_pi_apply 0)).mul
      (B.A_meas.comp (measurable_pi_apply (t' - t)))).aestronglyMeasurable
  calc ∫ ψ, A.A (ψ t) * B.A (ψ t') ∂(Ts.pathMeasure n)
      = ∫ ψ, A.A (cyclicShift n t ψ 0) * B.A (cyclicShift n t ψ (t' - t))
          ∂(Ts.pathMeasure n) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ψ => ?_)
        simp only [cyclicShift]
        rw [zero_add, sub_add_cancel]
    _ = ∫ ψ, A.A (ψ 0) * B.A (ψ (t' - t))
          ∂((Ts.pathMeasure n).map (cyclicShift n t)) :=
        (integral_map (measurable_cyclicShift n t).aemeasurable hmeas).symm
    _ = pathTwoPoint Ts A B n (t' - t) := by
        rw [pathMeasure_map_cyclicShift]
        rfl

end CyclicShift

/-! ## ZMod summation helper -/

private theorem sum_zmod_eq_sum_range (n : ℕ) [NeZero n] (f : ZMod n → ℝ) :
    ∑ t : ZMod n, f t = ∑ d ∈ Finset.range n, f (d : ZMod n) := by
  refine Finset.sum_bij (fun t _ => t.val) ?mem ?inj ?surj ?eq
  · intro t _
    exact Finset.mem_range.mpr (ZMod.val_lt t)
  · intro a _ b _ h
    exact ZMod.val_injective n h
  · intro d hd
    refine ⟨(d : ZMod n), Finset.mem_univ _, ?_⟩
    exact ZMod.val_natCast_of_lt (Finset.mem_range.mp hd)
  · intro t _
    have ht : ((t.val : ℕ) : ZMod n) = t := by
      simp [ZMod.natCast_val]
    simp [ht]

/-! ## The finite-`K` slice-family susceptibility bound (steps 2–6) -/

/-- **Finite-`K` slice-family susceptibility bound, per-pair form** (Stage C
task C3).  For the family of truncated slice observables
`A_{t,K} = clamp(-K,K,⟨g_t, ·⟩)` and any per-pair residual bounds `r t t'`,

`∫ (Σ_t A_{t,K}(ψ_t))² dμ_path ≤ (2/(1-γ))·Σ_t Var_Ω(g_t)
   + (C_diag·Nt)·R + (Σ_{t,t'} r t t')·R`,

with a right-hand side independent of `K`.  The diagonal one-point bound
(`hDiag`) and the `K`-uniform finite-periodic bridge residual bound (`hRes`)
are the two finite-volume ground-dominance inputs (see the module docstring).
The diagonal entries of `r` are unused; summing over all pairs is an upper
bound since `r ≥ 0`. -/
theorem asymSliceFamilyTrunc_pathMeasure_second_moment_le_pairwise
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hnorm : ∀ v : L2SpatialField Ns,
      ⟪asymGroundVector Nt Ns P a mass ha hmass, v⟫ = 0 →
        ‖asymTransferNormalized Nt Ns P a mass ha hmass v‖ ≤ γ * ‖v‖)
    (g : ZMod Nt → SpatialField Ns)
    (hInt : ∀ t : ZMod Nt, Integrable (fun ψ => (asymSliceObsLinear (g t) ψ) ^ 2 *
        ((asymGroundVector Nt Ns P a mass ha hmass) ψ) ^ 2) ν)
    (C_diag : ℝ) (r : ZMod Nt → ZMod Nt → ℝ) (hr : ∀ t t' : ZMod Nt, 0 ≤ r t t')
    (R : ℝ) (hR : 0 ≤ R)
    {K : ℝ} (hK : 0 < K)
    (hDiag : ∀ t : ZMod Nt,
      ∫ ψ : ZMod Nt → SpatialField Ns, (asymSliceObsTrunc (g t) K (ψ t)) ^ 2
          ∂((asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).pathMeasure Nt) ≤
        groundSliceVariance (Nt := Nt) (Ns := Ns) P a mass ha hmass (g t) +
          C_diag * R)
    (hRes : ∀ t t' d : ZMod Nt, 0 < d.val → d.val < Nt →
      finitePeriodicBridgeResidual
          (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass)
          (asymSliceObsTruncContract (Ns := Ns) (g t) hK)
          (asymSliceObsTruncContract (Ns := Ns) (g t') hK)
          (asymGappedTransfer Nt Ns P a mass ha hmass γ hγ0 hγ1 hnorm) γ Nt d ≤
        r t t' * R) :
    ∫ ψ : ZMod Nt → SpatialField Ns, (asymSliceFamilyTrunc g K ψ) ^ 2
        ∂((asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).pathMeasure Nt) ≤
      (2 / (1 - γ)) * groundSliceVarianceSum (Nt := Nt) (Ns := Ns) P a mass ha hmass g +
        (C_diag * Nt) * R + (∑ t : ZMod Nt, ∑ t' : ZMod Nt, r t t') * R := by
  classical
  set μ := (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).pathMeasure Nt
    with hμdef
  haveI hprob : IsProbabilityMeasure μ :=
    asymPathMeasure_isProbability (Nt := Nt) (Ns := Ns) P a mass ha hmass
  set G := asymGappedTransfer Nt Ns P a mass ha hmass γ hγ0 hγ1 hnorm with hGdef
  set A : ZMod Nt → MultiplicationCLMContract ν :=
    fun t => asymSliceObsTruncContract (Ns := Ns) (g t) hK with hAdef
  set b : ZMod Nt → ℝ := fun t => ‖G.vacuumPerp ((A t).M G.vacuum)‖ ^ 2 with hbdef
  set w : ZMod Nt → ℝ := fun s => γ ^ s.val + γ ^ (Nt - s.val) with hwdef
  set gsv : ZMod Nt → ℝ :=
    fun t => groundSliceVariance (Nt := Nt) (Ns := Ns) P a mass ha hmass (g t) with hgsvdef
  have hw_nonneg : ∀ s, 0 ≤ w s := fun s =>
    add_nonneg (pow_nonneg hγ0 _) (pow_nonneg hγ0 _)
  have hb_nonneg : ∀ t, 0 ≤ b t := fun t => sq_nonneg _
  -- Piece 1: perpendicular norms squared are bounded by ground slice variances.
  have hb_le : ∀ t, b t ≤ gsv t := by
    intro t
    have h := norm_sq_proj_obsTrunc_omega_le (Nt := Nt) (Ns := Ns) P a mass ha hmass
      (g t) hK (hInt t)
    exact h
  -- Integrability of the pair products (bounded on a probability measure).
  have hint_prod : ∀ t t' : ZMod Nt, Integrable (fun ψ : ZMod Nt → SpatialField Ns =>
      asymSliceObsTrunc (g t) K (ψ t) * asymSliceObsTrunc (g t') K (ψ t')) μ := by
    intro t t'
    have hmeas : Measurable (fun ψ : ZMod Nt → SpatialField Ns =>
        asymSliceObsTrunc (g t) K (ψ t) * asymSliceObsTrunc (g t') K (ψ t')) :=
      ((asymSliceObsTrunc_measurable (g t) K).comp (measurable_pi_apply t)).mul
        ((asymSliceObsTrunc_measurable (g t') K).comp (measurable_pi_apply t'))
    refine (integrable_const (K * K)).mono' hmeas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun ψ => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (asymSliceObsTrunc_abs_le_bound (g t) hK.le (ψ t))
      (asymSliceObsTrunc_abs_le_bound (g t') hK.le (ψ t')) (abs_nonneg _) hK.le
  -- Step 2: expand the square into the double time sum.
  have hexpand : ∫ ψ, (asymSliceFamilyTrunc g K ψ) ^ 2 ∂μ =
      ∑ t : ZMod Nt, ∑ t' : ZMod Nt,
        ∫ ψ, asymSliceObsTrunc (g t) K (ψ t) * asymSliceObsTrunc (g t') K (ψ t') ∂μ := by
    have hsq : ∀ ψ : ZMod Nt → SpatialField Ns, (asymSliceFamilyTrunc g K ψ) ^ 2 =
        ∑ t : ZMod Nt, ∑ t' : ZMod Nt,
          asymSliceObsTrunc (g t) K (ψ t) * asymSliceObsTrunc (g t') K (ψ t') := by
      intro ψ
      rw [pow_two]
      exact Finset.sum_mul_sum _ _ _ _
    rw [integral_congr_ae (Filter.Eventually.of_forall hsq)]
    rw [integral_finsetSum _ fun t _ =>
      integrable_finsetSum _ fun t' _ => hint_prod t t']
    exact Finset.sum_congr rfl fun t _ =>
      integral_finsetSum _ fun t' _ => hint_prod t t'
  -- Step 3: the one-point functions vanish.
  have hmean : ∀ (t s : ZMod Nt),
      finiteVolumeMean (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass)
        (A t) Nt s = 0 := fun t s =>
    asymSliceObsTrunc_pathMeasure_mean_zero (Nt := Nt) (Ns := Ns) P a mass ha hmass
      (g t) hK.le s
  -- Step 4: pair correlations are connected two-point functions at separation.
  have hpair : ∀ t t' : ZMod Nt,
      ∫ ψ, asymSliceObsTrunc (g t) K (ψ t) * asymSliceObsTrunc (g t') K (ψ t') ∂μ =
        pathConnectedTwoPoint (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass)
          (A t) (A t') Nt (t' - t) := by
    intro t t'
    unfold pathConnectedTwoPoint
    rw [hmean t 0, hmean t' (t' - t), zero_mul, sub_zero]
    exact pathMeasure_pair_eq_pathTwoPoint
      (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass) Nt (A t) (A t') t t'
  -- Step 5+6a: off-diagonal bound via the bridge envelope + residual + AM-GM.
  have hoff : ∀ t t' : ZMod Nt, t' ≠ t →
      pathConnectedTwoPoint (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass)
          (A t) (A t') Nt (t' - t) ≤
        (1 / 2) * (b t + b t') * w (t' - t) + r t t' * R := by
    intro t t' hne
    have hd0 : (t' - t : ZMod Nt) ≠ 0 := sub_ne_zero.mpr hne
    have hdval : 0 < (t' - t : ZMod Nt).val :=
      Nat.pos_of_ne_zero fun hcon => hd0 ((ZMod.val_eq_zero (t' - t)).mp hcon)
    have hdlt : (t' - t : ZMod Nt).val < Nt := ZMod.val_lt _
    have hres := hRes t t' (t' - t) hdval hdlt
    have hresid : finitePeriodicBridgeResidual
        (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass)
        (A t) (A t') G γ Nt (t' - t) =
        |pathConnectedTwoPoint (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass)
          (A t) (A t') Nt (t' - t)| -
        finitePeriodicPerpEnvelope
          (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass)
          (A t) (A t') G γ Nt (t' - t) := rfl
    have henv : finitePeriodicPerpEnvelope
        (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass)
        (A t) (A t') G γ Nt (t' - t) =
        ‖G.vacuumPerp ((A t).M G.vacuum)‖ * ‖G.vacuumPerp ((A t').M G.vacuum)‖ *
          w (t' - t) := rfl
    have hAM : ‖G.vacuumPerp ((A t).M G.vacuum)‖ * ‖G.vacuumPerp ((A t').M G.vacuum)‖ ≤
        (1 / 2) * (b t + b t') := by
      have hsq := sq_nonneg
        (‖G.vacuumPerp ((A t).M G.vacuum)‖ - ‖G.vacuumPerp ((A t').M G.vacuum)‖)
      simp only [hbdef]
      nlinarith
    have habs : |pathConnectedTwoPoint
        (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass)
        (A t) (A t') Nt (t' - t)| ≤
        (1 / 2) * (b t + b t') * w (t' - t) + r t t' * R := by
      have h1 : |pathConnectedTwoPoint
          (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass)
          (A t) (A t') Nt (t' - t)| ≤
          ‖G.vacuumPerp ((A t).M G.vacuum)‖ * ‖G.vacuumPerp ((A t').M G.vacuum)‖ *
            w (t' - t) + r t t' * R := by
        rw [hresid, henv] at hres
        linarith
      refine h1.trans ?_
      have h2 := mul_le_mul_of_nonneg_right hAM (hw_nonneg (t' - t))
      linarith
    exact (le_abs_self _).trans habs
  -- Assemble the double sum.
  set I : ZMod Nt → ZMod Nt → ℝ := fun t t' =>
    ∫ ψ, asymSliceObsTrunc (g t) K (ψ t) * asymSliceObsTrunc (g t') K (ψ t') ∂μ
    with hIdef
  have hIdiag : ∀ t : ZMod Nt, I t t ≤ gsv t + C_diag * R := by
    intro t
    have heq : I t t = ∫ ψ, (asymSliceObsTrunc (g t) K (ψ t)) ^ 2 ∂μ := by
      simp only [hIdef]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ψ => ?_)
      change asymSliceObsTrunc (g t) K (ψ t) * asymSliceObsTrunc (g t) K (ψ t) =
        asymSliceObsTrunc (g t) K (ψ t) ^ 2
      rw [pow_two]
    rw [heq]
    exact hDiag t
  have hIoff : ∀ t : ZMod Nt, ∀ t' ∈ Finset.univ.erase t,
      I t t' ≤ (1 / 2) * (b t + b t') * w (t' - t) + r t t' * R := by
    intro t t' ht'
    have hne : t' ≠ t := Finset.ne_of_mem_erase ht'
    simp only [hIdef]
    rw [hpair t t']
    exact hoff t t' hne
  -- Off-diagonal envelope sum: reindex, swap, and apply the wrap-around bound.
  have hre : ∀ t : ZMod Nt,
      ∑ t' ∈ Finset.univ.erase t, (1 / 2) * (b t + b t') * w (t' - t) =
        ∑ s ∈ Finset.univ.erase (0 : ZMod Nt), (1 / 2) * (b t + b (t + s)) * w s := by
    intro t
    refine Finset.sum_nbij' (i := fun t' => t' - t) (j := fun s => t + s)
      ?_ ?_ ?_ ?_ ?_
    · intro t' ht'
      have hne : t' ≠ t := Finset.ne_of_mem_erase ht'
      exact Finset.mem_erase.mpr ⟨sub_ne_zero.mpr hne, Finset.mem_univ _⟩
    · intro s hs
      have hne : s ≠ 0 := Finset.ne_of_mem_erase hs
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro hcon
      exact hne (by linear_combination hcon)
    · intro t' _
      ring
    · intro s _
      ring
    · intro t' _
      have hrw : t + (t' - t) = t' := by ring
      rw [hrw]
  have hshift : ∀ s : ZMod Nt, ∑ t : ZMod Nt, b (t + s) = ∑ t : ZMod Nt, b t :=
    fun s => Fintype.sum_equiv (Equiv.addRight s) _ _ fun t => rfl
  have hinner : ∀ s : ZMod Nt,
      ∑ t : ZMod Nt, (1 / 2) * (b t + b (t + s)) * w s =
        (∑ t : ZMod Nt, b t) * w s := by
    intro s
    calc ∑ t : ZMod Nt, (1 / 2) * (b t + b (t + s)) * w s
        = ∑ t : ZMod Nt, (b t + b (t + s)) * ((1 / 2) * w s) := by
          refine Finset.sum_congr rfl fun t _ => by ring
      _ = (∑ t : ZMod Nt, (b t + b (t + s))) * ((1 / 2) * w s) := by
          rw [Finset.sum_mul]
      _ = (2 * ∑ t : ZMod Nt, b t) * ((1 / 2) * w s) := by
          rw [Finset.sum_add_distrib, hshift s]
          ring
      _ = (∑ t : ZMod Nt, b t) * w s := by ring
  have hwsum : ∑ s ∈ Finset.univ.erase (0 : ZMod Nt), w s ≤ (1 + γ) / (1 - γ) := by
    have h1 : ∑ s ∈ Finset.univ.erase (0 : ZMod Nt), w s ≤ ∑ s : ZMod Nt, w s :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        fun s _ _ => hw_nonneg s
    have h2 : ∑ s : ZMod Nt, w s = ∑ d ∈ Finset.range Nt, (γ ^ d + γ ^ (Nt - d)) := by
      rw [sum_zmod_eq_sum_range]
      refine Finset.sum_congr rfl fun d hd => ?_
      simp only [hwdef]
      rw [ZMod.val_natCast_of_lt (Finset.mem_range.mp hd)]
    calc ∑ s ∈ Finset.univ.erase (0 : ZMod Nt), w s
        ≤ ∑ s : ZMod Nt, w s := h1
      _ = ∑ d ∈ Finset.range Nt, (γ ^ d + γ ^ (Nt - d)) := h2
      _ ≤ (1 + γ) / (1 - γ) := geom_wrap_sum_le γ hγ0 hγ1 Nt
  have hB_nonneg : (0 : ℝ) ≤ ∑ t : ZMod Nt, b t :=
    Finset.sum_nonneg fun t _ => hb_nonneg t
  have hB_le : ∑ t : ZMod Nt, b t ≤
      groundSliceVarianceSum (Nt := Nt) (Ns := Ns) P a mass ha hmass g := by
    unfold groundSliceVarianceSum
    exact Finset.sum_le_sum fun t _ => hb_le t
  have hEnv : ∑ t : ZMod Nt, ∑ t' ∈ Finset.univ.erase t,
      (1 / 2) * (b t + b t') * w (t' - t) ≤
      ((1 + γ) / (1 - γ)) *
        groundSliceVarianceSum (Nt := Nt) (Ns := Ns) P a mass ha hmass g := by
    have hgeom_nonneg : (0 : ℝ) ≤ (1 + γ) / (1 - γ) :=
      div_nonneg (by linarith) (by linarith)
    calc ∑ t : ZMod Nt, ∑ t' ∈ Finset.univ.erase t,
          (1 / 2) * (b t + b t') * w (t' - t)
        = ∑ t : ZMod Nt, ∑ s ∈ Finset.univ.erase (0 : ZMod Nt),
            (1 / 2) * (b t + b (t + s)) * w s := Finset.sum_congr rfl fun t _ => hre t
      _ = ∑ s ∈ Finset.univ.erase (0 : ZMod Nt), ∑ t : ZMod Nt,
            (1 / 2) * (b t + b (t + s)) * w s := Finset.sum_comm
      _ = ∑ s ∈ Finset.univ.erase (0 : ZMod Nt), (∑ t : ZMod Nt, b t) * w s :=
          Finset.sum_congr rfl fun s _ => hinner s
      _ = (∑ t : ZMod Nt, b t) * ∑ s ∈ Finset.univ.erase (0 : ZMod Nt), w s := by
          rw [Finset.mul_sum]
      _ ≤ (∑ t : ZMod Nt, b t) * ((1 + γ) / (1 - γ)) :=
          mul_le_mul_of_nonneg_left hwsum hB_nonneg
      _ ≤ groundSliceVarianceSum (Nt := Nt) (Ns := Ns) P a mass ha hmass g *
            ((1 + γ) / (1 - γ)) := mul_le_mul_of_nonneg_right hB_le hgeom_nonneg
      _ = ((1 + γ) / (1 - γ)) *
            groundSliceVarianceSum (Nt := Nt) (Ns := Ns) P a mass ha hmass g := by ring
  -- Cardinality bookkeeping for the residual terms.
  have hcard_univ : (Finset.univ : Finset (ZMod Nt)).card = Nt := by
    rw [Finset.card_univ, ZMod.card]
  -- The erased off-diagonal residual sums are dominated by the full double sum.
  have hRsum_le : ∑ t : ZMod Nt, ∑ t' ∈ Finset.univ.erase t, r t t' ≤
      ∑ t : ZMod Nt, ∑ t' : ZMod Nt, r t t' :=
    Finset.sum_le_sum fun t _ =>
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        fun t' _ _ => hr t t'
  -- Put everything together.
  have hgsvsum_eq : ∑ t : ZMod Nt, gsv t =
      groundSliceVarianceSum (Nt := Nt) (Ns := Ns) P a mass ha hmass g := rfl
  have hden : (0 : ℝ) < 1 - γ := by linarith
  calc ∫ ψ, (asymSliceFamilyTrunc g K ψ) ^ 2 ∂μ
      = ∑ t : ZMod Nt, ∑ t' : ZMod Nt, I t t' := hexpand
    _ = ∑ t : ZMod Nt, (I t t + ∑ t' ∈ Finset.univ.erase t, I t t') := by
        refine Finset.sum_congr rfl fun t _ => ?_
        exact (Finset.add_sum_erase Finset.univ (I t) (Finset.mem_univ t)).symm
    _ ≤ ∑ t : ZMod Nt, ((gsv t + C_diag * R) +
          ∑ t' ∈ Finset.univ.erase t,
            ((1 / 2) * (b t + b t') * w (t' - t) + r t t' * R)) := by
        refine Finset.sum_le_sum fun t _ => ?_
        exact add_le_add (hIdiag t) (Finset.sum_le_sum fun t' ht' => hIoff t t' ht')
    _ = (∑ t : ZMod Nt, gsv t) + (Nt : ℝ) * (C_diag * R) +
          (∑ t : ZMod Nt, ∑ t' ∈ Finset.univ.erase t,
            (1 / 2) * (b t + b t') * w (t' - t)) +
          (∑ t : ZMod Nt, ∑ t' ∈ Finset.univ.erase t, r t t') * R := by
        have h3 : ∀ t : ZMod Nt, ∑ t' ∈ Finset.univ.erase t,
            ((1 / 2) * (b t + b t') * w (t' - t) + r t t' * R) =
            (∑ t' ∈ Finset.univ.erase t, (1 / 2) * (b t + b t') * w (t' - t)) +
              (∑ t' ∈ Finset.univ.erase t, r t t') * R := by
          intro t
          rw [Finset.sum_add_distrib, ← Finset.sum_mul]
        calc ∑ t : ZMod Nt, ((gsv t + C_diag * R) +
              ∑ t' ∈ Finset.univ.erase t,
                ((1 / 2) * (b t + b t') * w (t' - t) + r t t' * R))
            = ∑ t : ZMod Nt, ((gsv t + C_diag * R) +
                ((∑ t' ∈ Finset.univ.erase t, (1 / 2) * (b t + b t') * w (t' - t)) +
                  (∑ t' ∈ Finset.univ.erase t, r t t') * R)) :=
              Finset.sum_congr rfl fun t _ => by rw [h3 t]
          _ = _ := by
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
                Finset.sum_const, hcard_univ, nsmul_eq_mul, ← Finset.sum_mul]
              ring
    _ ≤ groundSliceVarianceSum (Nt := Nt) (Ns := Ns) P a mass ha hmass g +
          (Nt : ℝ) * (C_diag * R) +
          ((1 + γ) / (1 - γ)) *
            groundSliceVarianceSum (Nt := Nt) (Ns := Ns) P a mass ha hmass g +
          (∑ t : ZMod Nt, ∑ t' : ZMod Nt, r t t') * R := by
        rw [hgsvsum_eq]
        have h4 : (∑ t : ZMod Nt, ∑ t' ∈ Finset.univ.erase t, r t t') * R ≤
            (∑ t : ZMod Nt, ∑ t' : ZMod Nt, r t t') * R :=
          mul_le_mul_of_nonneg_right hRsum_le hR
        have := hEnv
        linarith
    _ = (2 / (1 - γ)) *
          groundSliceVarianceSum (Nt := Nt) (Ns := Ns) P a mass ha hmass g +
          (C_diag * Nt) * R + (∑ t : ZMod Nt, ∑ t' : ZMod Nt, r t t') * R := by
        have hne : (1 : ℝ) - γ ≠ 0 := ne_of_gt hden
        field_simp
        ring

/-- **Finite-`K` slice-family susceptibility bound, scalar back-compat form.**
The constant per-pair residual bound `r ≡ C_off` collapses the double sum to
`C_off·Nt²`, recovering the original remainder shape
`(C_diag·Nt + C_off·Nt²)·R`. -/
theorem asymSliceFamilyTrunc_pathMeasure_second_moment_le
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hnorm : ∀ v : L2SpatialField Ns,
      ⟪asymGroundVector Nt Ns P a mass ha hmass, v⟫ = 0 →
        ‖asymTransferNormalized Nt Ns P a mass ha hmass v‖ ≤ γ * ‖v‖)
    (g : ZMod Nt → SpatialField Ns)
    (hInt : ∀ t : ZMod Nt, Integrable (fun ψ => (asymSliceObsLinear (g t) ψ) ^ 2 *
        ((asymGroundVector Nt Ns P a mass ha hmass) ψ) ^ 2) ν)
    (C_diag C_off : ℝ) (hCoff : 0 ≤ C_off) (R : ℝ) (hR : 0 ≤ R)
    {K : ℝ} (hK : 0 < K)
    (hDiag : ∀ t : ZMod Nt,
      ∫ ψ : ZMod Nt → SpatialField Ns, (asymSliceObsTrunc (g t) K (ψ t)) ^ 2
          ∂((asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).pathMeasure Nt) ≤
        groundSliceVariance (Nt := Nt) (Ns := Ns) P a mass ha hmass (g t) +
          C_diag * R)
    (hRes : ∀ t t' d : ZMod Nt, 0 < d.val → d.val < Nt →
      finitePeriodicBridgeResidual
          (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass)
          (asymSliceObsTruncContract (Ns := Ns) (g t) hK)
          (asymSliceObsTruncContract (Ns := Ns) (g t') hK)
          (asymGappedTransfer Nt Ns P a mass ha hmass γ hγ0 hγ1 hnorm) γ Nt d ≤
        C_off * R) :
    ∫ ψ : ZMod Nt → SpatialField Ns, (asymSliceFamilyTrunc g K ψ) ^ 2
        ∂((asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).pathMeasure Nt) ≤
      (2 / (1 - γ)) * groundSliceVarianceSum (Nt := Nt) (Ns := Ns) P a mass ha hmass g +
        (C_diag * Nt + C_off * Nt ^ 2) * R := by
  refine (asymSliceFamilyTrunc_pathMeasure_second_moment_le_pairwise (Nt := Nt) (Ns := Ns)
    P a mass ha hmass hγ0 hγ1 hnorm g hInt C_diag (fun _ _ => C_off)
    (fun _ _ => hCoff) R hR hK hDiag hRes).trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  ring

/-! ## Hole B-I headline: the `K → ∞` transfer to the linear observable -/

/-- **Slice-family susceptibility bound, per-pair form (`K → ∞`).**  The
finite-`K` per-pair bound is uniform in `K`, so the dominated-convergence
engine (`asymSliceObsLinear_pathMeasure_two_point_bound`) transfers it to the
untruncated linear slice-family observable. -/
theorem asymSliceFamily_pathMeasure_second_moment_le_pairwise
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hnorm : ∀ v : L2SpatialField Ns,
      ⟪asymGroundVector Nt Ns P a mass ha hmass, v⟫ = 0 →
        ‖asymTransferNormalized Nt Ns P a mass ha hmass v‖ ≤ γ * ‖v‖)
    (g : ZMod Nt → SpatialField Ns)
    (hInt : ∀ t : ZMod Nt, Integrable (fun ψ => (asymSliceObsLinear (g t) ψ) ^ 2 *
        ((asymGroundVector Nt Ns P a mass ha hmass) ψ) ^ 2) ν)
    (C_diag : ℝ) (r : ZMod Nt → ZMod Nt → ℝ) (hr : ∀ t t' : ZMod Nt, 0 ≤ r t t')
    (R : ℝ) (hR : 0 ≤ R)
    (hDiag : ∀ (K : ℝ), 0 < K → ∀ t : ZMod Nt,
      ∫ ψ : ZMod Nt → SpatialField Ns, (asymSliceObsTrunc (g t) K (ψ t)) ^ 2
          ∂((asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).pathMeasure Nt) ≤
        groundSliceVariance (Nt := Nt) (Ns := Ns) P a mass ha hmass (g t) +
          C_diag * R)
    (hRes : ∀ (K : ℝ) (hK : 0 < K), ∀ t t' d : ZMod Nt, 0 < d.val → d.val < Nt →
      finitePeriodicBridgeResidual
          (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass)
          (asymSliceObsTruncContract (Ns := Ns) (g t) hK)
          (asymSliceObsTruncContract (Ns := Ns) (g t') hK)
          (asymGappedTransfer Nt Ns P a mass ha hmass γ hγ0 hγ1 hnorm) γ Nt d ≤
        r t t' * R) :
    ∫ ψ : ZMod Nt → SpatialField Ns, (asymSliceFamilyLinear g ψ) ^ 2
        ∂((asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).pathMeasure Nt) ≤
      (2 / (1 - γ)) * groundSliceVarianceSum (Nt := Nt) (Ns := Ns) P a mass ha hmass g +
        (C_diag * Nt) * R + (∑ t : ZMod Nt, ∑ t' : ZMod Nt, r t t') * R :=
  asymSliceObsLinear_pathMeasure_two_point_bound (Nt := Nt) (Ns := Ns)
    P a mass ha hmass g _
    (fun K hK => asymSliceFamilyTrunc_pathMeasure_second_moment_le_pairwise
      (Nt := Nt) (Ns := Ns) P a mass ha hmass hγ0 hγ1 hnorm g hInt
      C_diag r hr R hR hK (hDiag K hK) (hRes K hK))

/-- **Hole B-I: slice-family susceptibility bound (`hPiece3`).**

`∫ (Σ_t ⟨g_t, ψ_t⟩)² dμ_path ≤ (2/(1-γ))·Σ_t Var_Ω(g_t)
   + (C_diag·Nt + C_off·Nt²)·γ^Nt.`

The finite-`K` bound is uniform in `K`, so the landed dominated-convergence
engine (`asymSliceObsLinear_pathMeasure_two_point_bound`) transfers it to the
untruncated linear slice-family observable.  The remainder shape
`(C_diag·Nt + C_off·Nt²)·γ^Nt` plugs into the abstract `rem` slot of the B5b
shell `piece3_pathMeasure_bound_to_freeCovariance_sum`.

The hypotheses `hDiag` (diagonal one-point ground dominance) and `hRes`
(`K`-uniform finite-periodic bridge residual) are the two finite-volume
inputs not derivable from the landed bricks; see the module docstring. -/
theorem asymSliceFamily_pathMeasure_second_moment_le
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hnorm : ∀ v : L2SpatialField Ns,
      ⟪asymGroundVector Nt Ns P a mass ha hmass, v⟫ = 0 →
        ‖asymTransferNormalized Nt Ns P a mass ha hmass v‖ ≤ γ * ‖v‖)
    (g : ZMod Nt → SpatialField Ns)
    (hInt : ∀ t : ZMod Nt, Integrable (fun ψ => (asymSliceObsLinear (g t) ψ) ^ 2 *
        ((asymGroundVector Nt Ns P a mass ha hmass) ψ) ^ 2) ν)
    (C_diag C_off : ℝ) (hCoff : 0 ≤ C_off) (R : ℝ) (hR : 0 ≤ R)
    (hDiag : ∀ (K : ℝ), 0 < K → ∀ t : ZMod Nt,
      ∫ ψ : ZMod Nt → SpatialField Ns, (asymSliceObsTrunc (g t) K (ψ t)) ^ 2
          ∂((asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).pathMeasure Nt) ≤
        groundSliceVariance (Nt := Nt) (Ns := Ns) P a mass ha hmass (g t) +
          C_diag * R)
    (hRes : ∀ (K : ℝ) (hK : 0 < K), ∀ t t' d : ZMod Nt, 0 < d.val → d.val < Nt →
      finitePeriodicBridgeResidual
          (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass)
          (asymSliceObsTruncContract (Ns := Ns) (g t) hK)
          (asymSliceObsTruncContract (Ns := Ns) (g t') hK)
          (asymGappedTransfer Nt Ns P a mass ha hmass γ hγ0 hγ1 hnorm) γ Nt d ≤
        C_off * R) :
    ∫ ψ : ZMod Nt → SpatialField Ns, (asymSliceFamilyLinear g ψ) ^ 2
        ∂((asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).pathMeasure Nt) ≤
      (2 / (1 - γ)) * groundSliceVarianceSum (Nt := Nt) (Ns := Ns) P a mass ha hmass g +
        (C_diag * Nt + C_off * Nt ^ 2) * R :=
  asymSliceObsLinear_pathMeasure_two_point_bound (Nt := Nt) (Ns := Ns)
    P a mass ha hmass g _
    (fun K hK => asymSliceFamilyTrunc_pathMeasure_second_moment_le
      (Nt := Nt) (Ns := Ns) P a mass ha hmass hγ0 hγ1 hnorm g hInt
      C_diag C_off hCoff R hR hK (hDiag K hK) (hRes K hK))

/-! ## S2: the fixed-`Ls` a-uniform transfer gap (γ-form) -/

/-- **S2 (17a): fixed-`Ls` a-uniform spectral gap of the asym transfer
operator, γ-form.**  At fixed spatial circumference `Ls = Ns·a` there exist a
uniform physical mass `m₀ > 0` and a spacing threshold `a₀ > 0` such that for
all lattices with `Ns·a = Ls` and `a ≤ a₀`, the normalized asym transfer
operator contracts by `γ = exp(-m₀·a)` on the orthogonal complement of the
Jentzsch ground vector — uniformly in `Nt`, `Ns`, and `a`.  (NOT VERIFIED)

Reference: Glimm–Jaffe Ch. 6, 19; Simon, *The P(φ)₂ Euclidean (Quantum) Field
Theory*, Ch. VI (semigroup convergence `T_a → e^{-aH(Ls)}` and the positive
Hamiltonian gap on the spatial circle); `reflection-positivity/docs/`
`B2_UNIFORMITY_QUESTION.md`.

Strategy: the transfer operator is the lattice approximation of `e^{-aH(Ls)}`
for the spatially cut-off `P(φ)₂` Hamiltonian on the circle of circumference
`Ls`, which has compact resolvent and a strictly positive spectral gap
`m(Ls) > 0`; compact-resolvent (norm-resolvent) convergence of the lattice
transfer generators as `a → 0` makes the lattice gap uniform for `a ≤ a₀`.
The `Nt`-dependence through `wickConstantAsym` is harmless:
`wickConstantAsym(Nt, Ns, a) → c(∞, Ns, a)` as `Nt → ∞` at fixed `(Ns, a)`,
Schrödinger eigenvalues are continuous in the polynomial coefficients, and
every finite `Nt` has a positive gap (compact resolvent, bounded-below even
polynomial), so `inf_{Nt} m_gap > 0`.  Vet record (Gemini 3.1-pro,
2026-07-12): statement pinned in `planning/b2-route-a-statements.md` §S2 —
carrier corrected to the proved operator-norm contraction object
(`asymTransferNormalized`, not `exp(-a·asymMassGap)`); the coupled
`Ns·a = Ls` quantifier is what the removed false predecessor lacked (PR #60). -/
axiom asymTransferGap_uniform_fixedLs
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) (Ls : ℝ) (hLs : 0 < Ls) :
    ∃ m₀ : ℝ, 0 < m₀ ∧ ∃ a₀ : ℝ, 0 < a₀ ∧
    ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (ha : 0 < a),
      (Ns : ℝ) * a = Ls → a ≤ a₀ →
      ∀ v, ⟪asymGroundVector Nt Ns P a mass ha hmass, v⟫ = 0 →
        ‖asymTransferNormalized Nt Ns P a mass ha hmass v‖ ≤ Real.exp (-(m₀ * a)) * ‖v‖

/-- **S2 consumer: the `γ := exp(-m₀·a)` specialization of hole B-I.**

At fixed `Ls`, the S2 gap supplies the contraction hypothesis with
`γ = exp(-m₀·a)` uniformly for `a ≤ a₀`, so the slice-family susceptibility
bound holds with the a-uniformly controlled prefactor `2/(1 - exp(-m₀·a))`
(`≤ 2/(m₀·a·(1-ε))` for small `a`).  The `hDiag`/`hRes` finite-volume inputs
are quantified over the gap data so the caller can discharge them for the
specific `γ`. -/
theorem asymSliceFamily_pathMeasure_second_moment_le_fixedLs
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (Ls : ℝ) (hLs : 0 < Ls) :
    ∃ m₀ : ℝ, 0 < m₀ ∧ ∃ a₀ : ℝ, 0 < a₀ ∧
    ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (ha : 0 < a),
      (Ns : ℝ) * a = Ls → a ≤ a₀ →
      ∀ (g : ZMod Nt → SpatialField Ns),
        (∀ t : ZMod Nt, Integrable (fun ψ => (asymSliceObsLinear (g t) ψ) ^ 2 *
            ((asymGroundVector Nt Ns P a mass ha hmass) ψ) ^ 2)
          (volume : Measure (SpatialField Ns))) →
        ∀ (C_diag C_off : ℝ), 0 ≤ C_off →
        (∀ (K : ℝ), 0 < K → ∀ t : ZMod Nt,
          ∫ ψ : ZMod Nt → SpatialField Ns, (asymSliceObsTrunc (g t) K (ψ t)) ^ 2
              ∂((asymTransferSystem (Nt := Nt) (Ns := Ns)
                  P a mass ha hmass).pathMeasure Nt) ≤
            groundSliceVariance (Nt := Nt) (Ns := Ns) P a mass ha hmass (g t) +
              C_diag * Real.exp (-(m₀ * a)) ^ Nt) →
        (∀ (hγ0 : (0:ℝ) ≤ Real.exp (-(m₀ * a))) (hγ1 : Real.exp (-(m₀ * a)) < 1)
          (hnorm : ∀ v : L2SpatialField Ns,
            ⟪asymGroundVector Nt Ns P a mass ha hmass, v⟫ = 0 →
              ‖asymTransferNormalized Nt Ns P a mass ha hmass v‖ ≤
                Real.exp (-(m₀ * a)) * ‖v‖)
          (K : ℝ) (hK : 0 < K), ∀ t t' d : ZMod Nt, 0 < d.val → d.val < Nt →
          finitePeriodicBridgeResidual
              (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass)
              (asymSliceObsTruncContract (Ns := Ns) (g t) hK)
              (asymSliceObsTruncContract (Ns := Ns) (g t') hK)
              (asymGappedTransfer Nt Ns P a mass ha hmass
                (Real.exp (-(m₀ * a))) hγ0 hγ1 hnorm)
              (Real.exp (-(m₀ * a))) Nt d ≤
            C_off * Real.exp (-(m₀ * a)) ^ Nt) →
        ∫ ψ : ZMod Nt → SpatialField Ns, (asymSliceFamilyLinear g ψ) ^ 2
            ∂((asymTransferSystem (Nt := Nt) (Ns := Ns)
                P a mass ha hmass).pathMeasure Nt) ≤
          (2 / (1 - Real.exp (-(m₀ * a)))) *
            groundSliceVarianceSum (Nt := Nt) (Ns := Ns) P a mass ha hmass g +
            (C_diag * Nt + C_off * Nt ^ 2) * Real.exp (-(m₀ * a)) ^ Nt := by
  obtain ⟨m₀, hm₀, a₀, ha₀, hgap⟩ := asymTransferGap_uniform_fixedLs P mass hmass Ls hLs
  refine ⟨m₀, hm₀, a₀, ha₀, ?_⟩
  intro Nt Ns _ _ a ha hLsa haa g hInt C_diag C_off hCoff hDiag hRes
  have hγ0 : (0:ℝ) ≤ Real.exp (-(m₀ * a)) := (Real.exp_pos _).le
  have hγ1 : Real.exp (-(m₀ * a)) < 1 := by
    have h1 : Real.exp (-(m₀ * a)) < Real.exp 0 :=
      Real.exp_lt_exp.mpr (by nlinarith)
    simpa using h1
  have hnorm := hgap Nt Ns a ha hLsa haa
  exact asymSliceFamily_pathMeasure_second_moment_le (Nt := Nt) (Ns := Ns)
    P a mass ha hmass hγ0 hγ1 hnorm g hInt C_diag C_off hCoff
    (Real.exp (-(m₀ * a)) ^ Nt) (pow_nonneg (Real.exp_pos _).le _) hDiag
    (hRes hγ0 hγ1 hnorm)

/-! ## τ-form K-uniform finite-periodic inputs (IUC at fixed physical time) and the
hypothesis-free corollaries

The finite-volume inputs `hDiag`/`hRes` are supplied by the following axioms, stated in the
**τ-form** (planning/b2-stageB-holes-spec.md §"Item-1 upgrade", Gemini-vetted 2026-07-12):
the per-step intrinsic-ultracontractivity constant blows up as `a → 0`, so the kernel bound
is attached to a fixed physical reference time `τ > 0` (proviso `2τ ≤ Nt·a`): operator-norm
contraction `γ^k` on the short arcs, IUC only across a `τ`-window
(`Q^{⌈τ/a⌉}(x,x) ≤ C(Ls,τ)·Ω(x)²`), total damping `γ^(Nt − ⌈τ/a⌉)`.  The constants depend
only on `(P, mass, Ls, τ)` — uniform in `(Nt, Ns, a, γ`-data`, g, K, d, t, t')` under
`Ns·a = Ls` — which is what closes the Stage-C `a → 0` corner:
`C·Nt·γ^(Nt−⌈τ/a⌉)·(1−γ) ≈ C·Lt·m₀·e^{−m₀(Lt−τ)}`, bounded in `a` and decaying in `Lt`.
Both collapse with `asymFinitePeriodicBridge_remainder_bound` in the trace-bridge
discharge.  The small-`Lt` regime (`Nt·a < 2τ`) is handled separately at Stage C. -/

/-- **Axiom (finite-periodic GNS remainder, τ-form, a-uniform at fixed `Ls`).**
(NOT VERIFIED — statement IUC-vetted 2026-07-12 with proof blueprint; see section
docstring.) -/
axiom asymFinitePeriodicBridge_remainder_bound_uniform
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (Ls : ℝ) (hLs : 0 < Ls) (τ : ℝ) (hτ : 0 < τ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (ha : 0 < a),
        (Ns : ℝ) * a = Ls → 2 * τ ≤ (Nt : ℝ) * a →
        ∀ {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
          (hnorm : ∀ v : L2SpatialField Ns,
            ⟪asymGroundVector Nt Ns P a mass ha hmass, v⟫ = 0 →
              ‖asymTransferNormalized Nt Ns P a mass ha hmass v‖ ≤ γ * ‖v‖)
          (g : ZMod Nt → SpatialField Ns) (K : ℝ) (hK : 0 < K),
        ∀ t t' d : ZMod Nt, 0 < d.val → d.val < Nt →
          finitePeriodicBridgeResidual
              (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass)
              (asymSliceObsTruncContract (Ns := Ns) (g t) hK)
              (asymSliceObsTruncContract (Ns := Ns) (g t') hK)
              (asymGappedTransfer Nt Ns P a mass ha hmass γ hγ0 hγ1 hnorm)
              γ Nt d ≤
            C * Real.sqrt (groundSliceVariance (Nt := Nt) (Ns := Ns)
                P a mass ha hmass (g t)) *
              Real.sqrt (groundSliceVariance (Nt := Nt) (Ns := Ns)
                P a mass ha hmass (g t')) *
              γ ^ (Nt - Nat.ceil (τ / a))

/-- **Axiom (finite-periodic diagonal ground dominance, τ-form, a-uniform at fixed
`Ls`).**  (NOT VERIFIED — statement IUC-vetted 2026-07-12; see section docstring.) -/
axiom asymFinitePeriodicBridge_diagonal_bound
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (Ls : ℝ) (hLs : 0 < Ls) (τ : ℝ) (hτ : 0 < τ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (ha : 0 < a),
        (Ns : ℝ) * a = Ls → 2 * τ ≤ (Nt : ℝ) * a →
        ∀ {γ : ℝ} (_hγ0 : 0 ≤ γ) (_hγ1 : γ < 1)
          (_hnorm : ∀ v : L2SpatialField Ns,
            ⟪asymGroundVector Nt Ns P a mass ha hmass, v⟫ = 0 →
              ‖asymTransferNormalized Nt Ns P a mass ha hmass v‖ ≤ γ * ‖v‖)
          (g : ZMod Nt → SpatialField Ns) (K : ℝ), 0 < K → ∀ t : ZMod Nt,
        ∫ ψ : ZMod Nt → SpatialField Ns, (asymSliceObsTrunc (g t) K (ψ t)) ^ 2
            ∂((asymTransferSystem (Nt := Nt) (Ns := Ns)
                P a mass ha hmass).pathMeasure Nt) ≤
          (1 + C * γ ^ (Nt - Nat.ceil (τ / a))) *
            groundSliceVariance (Nt := Nt) (Ns := Ns) P a mass ha hmass (g t)

/-- **Hole B-I, hypothesis-free τ-form.**  At fixed `Ls` and reference time `τ` with
`2τ ≤ Lt`, the slice-family susceptibility bound holds with the a-uniform remainder
exponent `γ^(Nt − ⌈τ/a⌉)` and instance constants in `groundSliceVarianceSum` units. -/
theorem asymSliceFamily_pathMeasure_second_moment_le'
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (Ls : ℝ) (hLs : 0 < Ls) (τ : ℝ) (hτ : 0 < τ)
    (hLsa : (Ns : ℝ) * a = Ls) (hLta : 2 * τ ≤ (Nt : ℝ) * a)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hnorm : ∀ v : L2SpatialField Ns,
      ⟪asymGroundVector Nt Ns P a mass ha hmass, v⟫ = 0 →
        ‖asymTransferNormalized Nt Ns P a mass ha hmass v‖ ≤ γ * ‖v‖)
    (g : ZMod Nt → SpatialField Ns)
    (hInt : ∀ t : ZMod Nt, Integrable (fun ψ => (asymSliceObsLinear (g t) ψ) ^ 2 *
        ((asymGroundVector Nt Ns P a mass ha hmass) ψ) ^ 2) ν) :
    ∃ C_diag C_off : ℝ, 0 ≤ C_off ∧
      ∫ ψ : ZMod Nt → SpatialField Ns, (asymSliceFamilyLinear g ψ) ^ 2
          ∂((asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).pathMeasure Nt) ≤
        (2 / (1 - γ)) * groundSliceVarianceSum (Nt := Nt) (Ns := Ns) P a mass ha hmass g +
          (C_diag * Nt + C_off * Nt ^ 2) * γ ^ (Nt - Nat.ceil (τ / a)) := by
  obtain ⟨C₁, hC₁, hDiagAx⟩ :=
    asymFinitePeriodicBridge_diagonal_bound P mass hmass Ls hLs τ hτ
  obtain ⟨C₂, hC₂, hResAx⟩ :=
    asymFinitePeriodicBridge_remainder_bound_uniform P mass hmass Ls hLs τ hτ
  have hgsv : ∀ t : ZMod Nt,
      0 ≤ groundSliceVariance (Nt := Nt) (Ns := Ns) P a mass ha hmass (g t) := by
    intro t
    exact integral_nonneg fun ψ => by positivity
  set S := groundSliceVarianceSum (Nt := Nt) (Ns := Ns) P a mass ha hmass g with hS
  have hS_nonneg : 0 ≤ S :=
    Finset.sum_nonneg fun t _ => hgsv t
  have hgsv_le : ∀ t : ZMod Nt,
      groundSliceVariance (Nt := Nt) (Ns := Ns) P a mass ha hmass (g t) ≤ S := by
    intro t
    exact Finset.single_le_sum (fun t _ => hgsv t) (Finset.mem_univ t)
  have hγpow : (0:ℝ) ≤ γ ^ (Nt - Nat.ceil (τ / a)) := pow_nonneg hγ0 _
  refine ⟨C₁ * S, C₂ * S, mul_nonneg hC₂ hS_nonneg,
    asymSliceFamily_pathMeasure_second_moment_le (Nt := Nt) (Ns := Ns)
      P a mass ha hmass hγ0 hγ1 hnorm g hInt (C₁ * S) (C₂ * S)
      (mul_nonneg hC₂ hS_nonneg) (γ ^ (Nt - Nat.ceil (τ / a))) hγpow ?_ ?_⟩
  · intro K hK t
    refine le_trans (hDiagAx Nt Ns a ha hLsa hLta hγ0 hγ1 hnorm g K hK t) ?_
    have h1 := hgsv t
    have h2 := hgsv_le t
    nlinarith [mul_nonneg (mul_nonneg hC₁ hγpow) (sub_nonneg.mpr h2)]
  · intro K hK t t' d hd hdlt
    refine le_trans (hResAx Nt Ns a ha hLsa hLta hγ0 hγ1 hnorm g K hK t t' d hd hdlt) ?_
    have h1 := hgsv t
    have h2 := hgsv t'
    have hsq : Real.sqrt (groundSliceVariance (Nt := Nt) (Ns := Ns)
          P a mass ha hmass (g t)) *
        Real.sqrt (groundSliceVariance (Nt := Nt) (Ns := Ns)
          P a mass ha hmass (g t')) ≤ S := by
      have hs1 := Real.sq_sqrt h1
      have hs2 := Real.sq_sqrt h2
      have hle1 := hgsv_le t
      have hle2 := hgsv_le t'
      nlinarith [sq_nonneg (Real.sqrt (groundSliceVariance (Nt := Nt) (Ns := Ns)
          P a mass ha hmass (g t)) -
        Real.sqrt (groundSliceVariance (Nt := Nt) (Ns := Ns)
          P a mass ha hmass (g t')))]
    nlinarith [mul_nonneg (mul_nonneg hC₂ hγpow) (sub_nonneg.mpr hsq)]

/-- **Hole B-I at the S2 gap, hypothesis-free τ-form.**  Combines
`asymTransferGap_uniform_fixedLs` with the τ-form axioms: at fixed `Ls` and reference
time `τ` there are `m₀, a₀ > 0` such that for every admissible lattice with `2τ ≤ Nt·a`
and every slice family, the susceptibility bound holds with `γ = exp(-m₀·a)` and the
a-uniform remainder exponent. -/
theorem asymSliceFamily_pathMeasure_second_moment_le_fixedLs'
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (Ls : ℝ) (hLs : 0 < Ls) (τ : ℝ) (hτ : 0 < τ) :
    ∃ m₀ : ℝ, 0 < m₀ ∧ ∃ a₀ : ℝ, 0 < a₀ ∧
    ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (ha : 0 < a),
      (Ns : ℝ) * a = Ls → a ≤ a₀ → 2 * τ ≤ (Nt : ℝ) * a →
      ∀ (g : ZMod Nt → SpatialField Ns),
        (∀ t : ZMod Nt, Integrable (fun ψ => (asymSliceObsLinear (g t) ψ) ^ 2 *
            ((asymGroundVector Nt Ns P a mass ha hmass) ψ) ^ 2)
          (volume : Measure (SpatialField Ns))) →
        ∃ C_diag C_off : ℝ, 0 ≤ C_off ∧
          ∫ ψ : ZMod Nt → SpatialField Ns, (asymSliceFamilyLinear g ψ) ^ 2
              ∂((asymTransferSystem (Nt := Nt) (Ns := Ns)
                  P a mass ha hmass).pathMeasure Nt) ≤
            (2 / (1 - Real.exp (-(m₀ * a)))) *
              groundSliceVarianceSum (Nt := Nt) (Ns := Ns) P a mass ha hmass g +
              (C_diag * Nt + C_off * Nt ^ 2) *
                Real.exp (-(m₀ * a)) ^ (Nt - Nat.ceil (τ / a)) := by
  obtain ⟨m₀, hm₀, a₀, ha₀, hgap⟩ := asymTransferGap_uniform_fixedLs P mass hmass Ls hLs
  refine ⟨m₀, hm₀, a₀, ha₀, ?_⟩
  intro Nt Ns _ _ a ha hLsa haa hLta g hInt
  have hγ0 : (0:ℝ) ≤ Real.exp (-(m₀ * a)) := (Real.exp_pos _).le
  have hγ1 : Real.exp (-(m₀ * a)) < 1 := by
    have h1 : Real.exp (-(m₀ * a)) < Real.exp 0 :=
      Real.exp_lt_exp.mpr (by nlinarith)
    simpa using h1
  exact asymSliceFamily_pathMeasure_second_moment_le' (Nt := Nt) (Ns := Ns)
    P a mass ha hmass Ls hLs τ hτ hLsa hLta hγ0 hγ1 (hgap Nt Ns a ha hLsa haa) g hInt

/-! ## Stage C task C3: the sharp `Nt·gSVSum` remainder via Cauchy–Schwarz

Instantiating the per-pair theorem with `r t t' := C₂·√gSV(g t)·√gSV(g t')` from the
τ-form remainder axiom and collapsing the double sum by Cauchy–Schwarz
(`(Σ_t √gSV_t)² ≤ Nt·Σ_t gSV_t`) improves the remainder from `Nt²·γ^†·gSVSum` to
`Nt·γ^†·gSVSum`.  With `γ = e^{-m₀a}` and `† = Nt - ⌈τ/a⌉` the remainder-to-main ratio is
`≈ C·Lt·m₀·e^{-m₀(Lt-τ)}` — bounded as `a → 0` and decaying in `Lt`, which closes the
Stage-C corner (planning/b2-stageB-holes-spec.md §"Stage C work plan", task C3). -/

/-- Cauchy–Schwarz collapse of a product-form double sum: for `v ≥ 0`,
`Σ_{t,t'} C·√v_t·√v_{t'} = C·(Σ_t √v_t)² ≤ C·n·Σ_t v_t`. -/
private theorem sum_sum_mul_sqrt_le (n : ℕ) [NeZero n] (C : ℝ) (hC : 0 ≤ C)
    (v : ZMod n → ℝ) (hv : ∀ t, 0 ≤ v t) :
    ∑ t : ZMod n, ∑ t' : ZMod n, C * Real.sqrt (v t) * Real.sqrt (v t') ≤
      C * ((n : ℝ) * ∑ t : ZMod n, v t) := by
  have h1 : ∑ t : ZMod n, ∑ t' : ZMod n, C * Real.sqrt (v t) * Real.sqrt (v t') =
      C * (∑ t : ZMod n, Real.sqrt (v t)) ^ 2 := by
    calc ∑ t : ZMod n, ∑ t' : ZMod n, C * Real.sqrt (v t) * Real.sqrt (v t')
        = ∑ t : ZMod n, C * Real.sqrt (v t) * ∑ t' : ZMod n, Real.sqrt (v t') :=
          Finset.sum_congr rfl fun t _ => by rw [← Finset.mul_sum]
      _ = (∑ t : ZMod n, C * Real.sqrt (v t)) * ∑ t' : ZMod n, Real.sqrt (v t') := by
          rw [← Finset.sum_mul]
      _ = C * (∑ t : ZMod n, Real.sqrt (v t)) ^ 2 := by
          rw [← Finset.mul_sum]
          ring
  have h2 : (∑ t : ZMod n, Real.sqrt (v t)) ^ 2 ≤ (n : ℝ) * ∑ t : ZMod n, v t := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (ZMod n)))
      (f := fun t => Real.sqrt (v t))
    rw [Finset.card_univ, ZMod.card] at h
    refine h.trans (le_of_eq ?_)
    congr 1
    exact Finset.sum_congr rfl fun t _ => Real.sq_sqrt (hv t)
  rw [h1]
  exact mul_le_mul_of_nonneg_left h2 hC

/-- **Hole B-I, sharp τ-form (Stage C task C3).**  Same hypotheses as
`asymSliceFamily_pathMeasure_second_moment_le'`, but the per-pair remainder bounds are
collapsed by Cauchy–Schwarz to the sharp remainder `C_rem·Nt·γ^(Nt-⌈τ/a⌉)·gSVSum`
(one power of `Nt`, not two). -/
theorem asymSliceFamily_pathMeasure_second_moment_le_sharp
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (Ls : ℝ) (hLs : 0 < Ls) (τ : ℝ) (hτ : 0 < τ)
    (hLsa : (Ns : ℝ) * a = Ls) (hLta : 2 * τ ≤ (Nt : ℝ) * a)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hnorm : ∀ v : L2SpatialField Ns,
      ⟪asymGroundVector Nt Ns P a mass ha hmass, v⟫ = 0 →
        ‖asymTransferNormalized Nt Ns P a mass ha hmass v‖ ≤ γ * ‖v‖)
    (g : ZMod Nt → SpatialField Ns)
    (hInt : ∀ t : ZMod Nt, Integrable (fun ψ => (asymSliceObsLinear (g t) ψ) ^ 2 *
        ((asymGroundVector Nt Ns P a mass ha hmass) ψ) ^ 2) ν) :
    ∃ C_rem : ℝ, 0 ≤ C_rem ∧
      ∫ ψ : ZMod Nt → SpatialField Ns, (asymSliceFamilyLinear g ψ) ^ 2
          ∂((asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).pathMeasure Nt) ≤
        ((2 / (1 - γ)) + C_rem * Nt * γ ^ (Nt - Nat.ceil (τ / a))) *
          groundSliceVarianceSum (Nt := Nt) (Ns := Ns) P a mass ha hmass g := by
  obtain ⟨C₁, hC₁, hDiagAx⟩ :=
    asymFinitePeriodicBridge_diagonal_bound P mass hmass Ls hLs τ hτ
  obtain ⟨C₂, hC₂, hResAx⟩ :=
    asymFinitePeriodicBridge_remainder_bound_uniform P mass hmass Ls hLs τ hτ
  have hgsv : ∀ t : ZMod Nt,
      0 ≤ groundSliceVariance (Nt := Nt) (Ns := Ns) P a mass ha hmass (g t) := by
    intro t
    exact integral_nonneg fun ψ => by positivity
  set S := groundSliceVarianceSum (Nt := Nt) (Ns := Ns) P a mass ha hmass g with hS
  have hS_nonneg : 0 ≤ S :=
    Finset.sum_nonneg fun t _ => hgsv t
  have hgsv_le : ∀ t : ZMod Nt,
      groundSliceVariance (Nt := Nt) (Ns := Ns) P a mass ha hmass (g t) ≤ S := by
    intro t
    exact Finset.single_le_sum (fun t _ => hgsv t) (Finset.mem_univ t)
  have hγpow : (0:ℝ) ≤ γ ^ (Nt - Nat.ceil (τ / a)) := pow_nonneg hγ0 _
  refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, ?_⟩
  refine le_trans (asymSliceFamily_pathMeasure_second_moment_le_pairwise (Nt := Nt)
    (Ns := Ns) P a mass ha hmass hγ0 hγ1 hnorm g hInt (C₁ * S)
    (fun t t' => C₂ * Real.sqrt (groundSliceVariance (Nt := Nt) (Ns := Ns)
        P a mass ha hmass (g t)) *
      Real.sqrt (groundSliceVariance (Nt := Nt) (Ns := Ns) P a mass ha hmass (g t')))
    (fun t t' => mul_nonneg (mul_nonneg hC₂ (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
    (γ ^ (Nt - Nat.ceil (τ / a))) hγpow ?_ ?_) ?_
  · intro K hK t
    refine le_trans (hDiagAx Nt Ns a ha hLsa hLta hγ0 hγ1 hnorm g K hK t) ?_
    have h1 := hgsv t
    have h2 := hgsv_le t
    nlinarith [mul_nonneg (mul_nonneg hC₁ hγpow) (sub_nonneg.mpr h2)]
  · intro K hK t t' d hd hdlt
    exact hResAx Nt Ns a ha hLsa hLta hγ0 hγ1 hnorm g K hK t t' d hd hdlt
  · -- Cauchy–Schwarz collapse of the double sum: Σ_{t,t'} r ≤ C₂·Nt·S.
    have hrs : (∑ t : ZMod Nt, ∑ t' : ZMod Nt,
        C₂ * Real.sqrt (groundSliceVariance (Nt := Nt) (Ns := Ns)
            P a mass ha hmass (g t)) *
          Real.sqrt (groundSliceVariance (Nt := Nt) (Ns := Ns)
            P a mass ha hmass (g t'))) ≤ C₂ * ((Nt : ℝ) * S) :=
      sum_sum_mul_sqrt_le Nt C₂ hC₂
        (fun t => groundSliceVariance (Nt := Nt) (Ns := Ns) P a mass ha hmass (g t)) hgsv
    have h2 : (∑ t : ZMod Nt, ∑ t' : ZMod Nt,
        C₂ * Real.sqrt (groundSliceVariance (Nt := Nt) (Ns := Ns)
            P a mass ha hmass (g t)) *
          Real.sqrt (groundSliceVariance (Nt := Nt) (Ns := Ns)
            P a mass ha hmass (g t'))) * γ ^ (Nt - Nat.ceil (τ / a)) ≤
        C₂ * ((Nt : ℝ) * S) * γ ^ (Nt - Nat.ceil (τ / a)) :=
      mul_le_mul_of_nonneg_right hrs hγpow
    calc (2 / (1 - γ)) * S + (C₁ * S * Nt) * γ ^ (Nt - Nat.ceil (τ / a)) +
          (∑ t : ZMod Nt, ∑ t' : ZMod Nt,
            C₂ * Real.sqrt (groundSliceVariance (Nt := Nt) (Ns := Ns)
                P a mass ha hmass (g t)) *
              Real.sqrt (groundSliceVariance (Nt := Nt) (Ns := Ns)
                P a mass ha hmass (g t'))) * γ ^ (Nt - Nat.ceil (τ / a))
        ≤ (2 / (1 - γ)) * S + (C₁ * S * Nt) * γ ^ (Nt - Nat.ceil (τ / a)) +
          C₂ * ((Nt : ℝ) * S) * γ ^ (Nt - Nat.ceil (τ / a)) := by linarith
      _ = ((2 / (1 - γ)) + (C₁ + C₂) * Nt * γ ^ (Nt - Nat.ceil (τ / a))) * S := by ring

/-- **Hole B-I at the S2 gap, sharp τ-form (Stage C task C3).**  Combines
`asymTransferGap_uniform_fixedLs` with the sharp Cauchy–Schwarz corollary: at fixed `Ls`
and reference time `τ` there are `m₀, a₀ > 0` such that for every admissible lattice with
`2τ ≤ Nt·a`, the susceptibility bound holds with `γ = exp(-m₀·a)` and the sharp remainder
`C_rem·Nt·γ^(Nt-⌈τ/a⌉)·gSVSum`. -/
theorem asymSliceFamily_pathMeasure_second_moment_le_fixedLs_sharp
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (Ls : ℝ) (hLs : 0 < Ls) (τ : ℝ) (hτ : 0 < τ) :
    ∃ m₀ : ℝ, 0 < m₀ ∧ ∃ a₀ : ℝ, 0 < a₀ ∧
    ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (ha : 0 < a),
      (Ns : ℝ) * a = Ls → a ≤ a₀ → 2 * τ ≤ (Nt : ℝ) * a →
      ∀ (g : ZMod Nt → SpatialField Ns),
        (∀ t : ZMod Nt, Integrable (fun ψ => (asymSliceObsLinear (g t) ψ) ^ 2 *
            ((asymGroundVector Nt Ns P a mass ha hmass) ψ) ^ 2)
          (volume : Measure (SpatialField Ns))) →
        ∃ C_rem : ℝ, 0 ≤ C_rem ∧
          ∫ ψ : ZMod Nt → SpatialField Ns, (asymSliceFamilyLinear g ψ) ^ 2
              ∂((asymTransferSystem (Nt := Nt) (Ns := Ns)
                  P a mass ha hmass).pathMeasure Nt) ≤
            ((2 / (1 - Real.exp (-(m₀ * a)))) +
                C_rem * Nt * Real.exp (-(m₀ * a)) ^ (Nt - Nat.ceil (τ / a))) *
              groundSliceVarianceSum (Nt := Nt) (Ns := Ns) P a mass ha hmass g := by
  obtain ⟨m₀, hm₀, a₀, ha₀, hgap⟩ := asymTransferGap_uniform_fixedLs P mass hmass Ls hLs
  refine ⟨m₀, hm₀, a₀, ha₀, ?_⟩
  intro Nt Ns _ _ a ha hLsa haa hLta g hInt
  have hγ0 : (0:ℝ) ≤ Real.exp (-(m₀ * a)) := (Real.exp_pos _).le
  have hγ1 : Real.exp (-(m₀ * a)) < 1 := by
    have h1 : Real.exp (-(m₀ * a)) < Real.exp 0 :=
      Real.exp_lt_exp.mpr (by nlinarith)
    simpa using h1
  exact asymSliceFamily_pathMeasure_second_moment_le_sharp (Nt := Nt) (Ns := Ns)
    P a mass ha hmass Ls hLs τ hτ hLsa hLta hγ0 hγ1 (hgap Nt Ns a ha hLsa haa) g hInt

/-- **Hole B-I at the S2 gap, sharp τ-form with the remainder constant hoisted (Stage C
task C4).**  Same content as `asymSliceFamily_pathMeasure_second_moment_le_fixedLs_sharp`,
but the remainder constant `C_rem = C₁ + C₂` (from the two τ-form bridge axioms, which are
a-uniform at fixed `(Ls, τ)`) is extracted BEFORE the lattice quantifier, so a single
`C_rem` serves all admissible `(Nt, Ns, a, g)`.  This is the form consumed by the Stage-C
master assembly, whose headline constant must be instance-free. -/
theorem asymSliceFamily_pathMeasure_second_moment_le_fixedLs_sharp_uniform
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (Ls : ℝ) (hLs : 0 < Ls) (τ : ℝ) (hτ : 0 < τ) :
    ∃ m₀ : ℝ, 0 < m₀ ∧ ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ C_rem : ℝ, 0 ≤ C_rem ∧
    ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (ha : 0 < a),
      (Ns : ℝ) * a = Ls → a ≤ a₀ → 2 * τ ≤ (Nt : ℝ) * a →
      ∀ (g : ZMod Nt → SpatialField Ns),
        (∀ t : ZMod Nt, Integrable (fun ψ => (asymSliceObsLinear (g t) ψ) ^ 2 *
            ((asymGroundVector Nt Ns P a mass ha hmass) ψ) ^ 2)
          (volume : Measure (SpatialField Ns))) →
          ∫ ψ : ZMod Nt → SpatialField Ns, (asymSliceFamilyLinear g ψ) ^ 2
              ∂((asymTransferSystem (Nt := Nt) (Ns := Ns)
                  P a mass ha hmass).pathMeasure Nt) ≤
            ((2 / (1 - Real.exp (-(m₀ * a)))) +
                C_rem * Nt * Real.exp (-(m₀ * a)) ^ (Nt - Nat.ceil (τ / a))) *
              groundSliceVarianceSum (Nt := Nt) (Ns := Ns) P a mass ha hmass g := by
  obtain ⟨m₀, hm₀, a₀, ha₀, hgap⟩ := asymTransferGap_uniform_fixedLs P mass hmass Ls hLs
  obtain ⟨C₁, hC₁, hDiagAx⟩ :=
    asymFinitePeriodicBridge_diagonal_bound P mass hmass Ls hLs τ hτ
  obtain ⟨C₂, hC₂, hResAx⟩ :=
    asymFinitePeriodicBridge_remainder_bound_uniform P mass hmass Ls hLs τ hτ
  refine ⟨m₀, hm₀, a₀, ha₀, C₁ + C₂, add_nonneg hC₁ hC₂, ?_⟩
  intro Nt Ns _ _ a ha hLsa haa hLta g hInt
  have hγ0 : (0:ℝ) ≤ Real.exp (-(m₀ * a)) := (Real.exp_pos _).le
  have hγ1 : Real.exp (-(m₀ * a)) < 1 := by
    have h1 : Real.exp (-(m₀ * a)) < Real.exp 0 :=
      Real.exp_lt_exp.mpr (by nlinarith)
    simpa using h1
  have hnorm := hgap Nt Ns a ha hLsa haa
  set γ : ℝ := Real.exp (-(m₀ * a)) with hγ_def
  have hgsv : ∀ t : ZMod Nt,
      0 ≤ groundSliceVariance (Nt := Nt) (Ns := Ns) P a mass ha hmass (g t) := by
    intro t
    exact integral_nonneg fun ψ => by positivity
  set S := groundSliceVarianceSum (Nt := Nt) (Ns := Ns) P a mass ha hmass g with hS
  have hS_nonneg : 0 ≤ S :=
    Finset.sum_nonneg fun t _ => hgsv t
  have hgsv_le : ∀ t : ZMod Nt,
      groundSliceVariance (Nt := Nt) (Ns := Ns) P a mass ha hmass (g t) ≤ S := by
    intro t
    exact Finset.single_le_sum (fun t _ => hgsv t) (Finset.mem_univ t)
  have hγpow : (0:ℝ) ≤ γ ^ (Nt - Nat.ceil (τ / a)) := pow_nonneg hγ0 _
  refine le_trans (asymSliceFamily_pathMeasure_second_moment_le_pairwise (Nt := Nt)
    (Ns := Ns) P a mass ha hmass hγ0 hγ1 hnorm g hInt (C₁ * S)
    (fun t t' => C₂ * Real.sqrt (groundSliceVariance (Nt := Nt) (Ns := Ns)
        P a mass ha hmass (g t)) *
      Real.sqrt (groundSliceVariance (Nt := Nt) (Ns := Ns) P a mass ha hmass (g t')))
    (fun t t' => mul_nonneg (mul_nonneg hC₂ (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
    (γ ^ (Nt - Nat.ceil (τ / a))) hγpow ?_ ?_) ?_
  · intro K hK t
    refine le_trans (hDiagAx Nt Ns a ha hLsa hLta hγ0 hγ1 hnorm g K hK t) ?_
    have h1 := hgsv t
    have h2 := hgsv_le t
    nlinarith [mul_nonneg (mul_nonneg hC₁ hγpow) (sub_nonneg.mpr h2)]
  · intro K hK t t' d hd hdlt
    exact hResAx Nt Ns a ha hLsa hLta hγ0 hγ1 hnorm g K hK t t' d hd hdlt
  · -- Cauchy–Schwarz collapse of the double sum: Σ_{t,t'} r ≤ C₂·Nt·S.
    have hrs : (∑ t : ZMod Nt, ∑ t' : ZMod Nt,
        C₂ * Real.sqrt (groundSliceVariance (Nt := Nt) (Ns := Ns)
            P a mass ha hmass (g t)) *
          Real.sqrt (groundSliceVariance (Nt := Nt) (Ns := Ns)
            P a mass ha hmass (g t'))) ≤ C₂ * ((Nt : ℝ) * S) :=
      sum_sum_mul_sqrt_le Nt C₂ hC₂
        (fun t => groundSliceVariance (Nt := Nt) (Ns := Ns) P a mass ha hmass (g t)) hgsv
    have h2 : (∑ t : ZMod Nt, ∑ t' : ZMod Nt,
        C₂ * Real.sqrt (groundSliceVariance (Nt := Nt) (Ns := Ns)
            P a mass ha hmass (g t)) *
          Real.sqrt (groundSliceVariance (Nt := Nt) (Ns := Ns)
            P a mass ha hmass (g t'))) * γ ^ (Nt - Nat.ceil (τ / a)) ≤
        C₂ * ((Nt : ℝ) * S) * γ ^ (Nt - Nat.ceil (τ / a)) :=
      mul_le_mul_of_nonneg_right hrs hγpow
    calc (2 / (1 - γ)) * S + (C₁ * S * Nt) * γ ^ (Nt - Nat.ceil (τ / a)) +
          (∑ t : ZMod Nt, ∑ t' : ZMod Nt,
            C₂ * Real.sqrt (groundSliceVariance (Nt := Nt) (Ns := Ns)
                P a mass ha hmass (g t)) *
              Real.sqrt (groundSliceVariance (Nt := Nt) (Ns := Ns)
                P a mass ha hmass (g t'))) * γ ^ (Nt - Nat.ceil (τ / a))
        ≤ (2 / (1 - γ)) * S + (C₁ * S * Nt) * γ ^ (Nt - Nat.ceil (τ / a)) +
          C₂ * ((Nt : ℝ) * S) * γ ^ (Nt - Nat.ceil (τ / a)) := by linarith
      _ = ((2 / (1 - γ)) + (C₁ + C₂) * Nt * γ ^ (Nt - Nat.ceil (τ / a))) * S := by ring

end Pphi2

end
