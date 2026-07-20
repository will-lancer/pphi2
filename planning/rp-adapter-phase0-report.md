# Phase 0 Report: Asym-Torus RP Adapter

Date: 2026-07-20

## Outcome

Go for Phase 1. No genuinely new mathematical fact is missing for the lattice adapter.

Phase 2 is also still viable, but the implementation route needs one correction:
the existing dependency theorem
`MeasureTheory.Measure.IsReflectionPositive.weak_limit`
is too strong for the convergence the repo currently proves in the UV limit
(it asks convergence of reflection forms for all `mPos`-measurable integrable observables,
while the available UV limit theorems only give bounded-continuous / characteristic-functional
convergence). The cylinder step therefore has to use the existing matrixwise weak-limit route
already foreshadowed in `Pphi2/IRLimit/CylinderOS.lean:290-299`, not the stronger abstract
`IsReflectionPositive.weak_limit` theorem directly.

## (a) Exact `EPos` and `J`

Let `Nt = 2 * M` with `M > 0`, and let

- `ι := Fin M × ZMod Ns`
- `e : Sum ι ι ≃ AsymLatticeSites Nt Ns`
  by
  `e (Sum.inl (t,x)) = (t,x)` and
  `e (Sum.inr (t,x)) = (Nt - 1 - t, x)`.

This is the vetted link-reflection block split:
under `e`, `evenTheta` is exactly the link reflection
`θ_L(t,x) = (Nt - 1 - t, x)`.

Write `ψ : ι → ℝ` for a half-field. The correct half-action is

`EPos ψ =`

- `((1/2) * withinTimeBondsPlus ψ)`
- `+ ((1/2) * withinSpaceBondsPlus ψ)`
- `+ ((a^2 * mass^2) / 2) * onsiteSqPlus ψ`
- `+ (1/2) * boundarySq0 ψ`
- `+ (1/2) * boundarySqLast ψ`
- `+ a^2 * wickPlus ψ`

where:

- `withinTimeBondsPlus` sums `(ψ(t+1,x) - ψ(t,x))^2` over `t = 0, ..., M-2`
- `withinSpaceBondsPlus` sums `(ψ(t,x+1) - ψ(t,x))^2` over all `t = 0, ..., M-1`
- `onsiteSqPlus` sums `ψ(t,x)^2` over all `t = 0, ..., M-1`
- `boundarySq0` sums `ψ(0,x)^2`
- `boundarySqLast` sums `ψ(M-1,x)^2`
- `wickPlus` sums
  `wickPolynomial P (wickConstantAsym Nt Ns a mass) (ψ(t,x))`
  over all `t = 0, ..., M-1`.

The two crossing bonds are exactly:

- `(0,x) ↔ (Nt-1,x)`
- `(M-1,x) ↔ (M,x)`

and under the block map both are of the form `inl i ↔ inr i`.
After rewriting

`(1/2) * (u - v)^2 = (1/2) * u^2 + (1/2) * v^2 - u * v`

the crossing self-terms are absorbed into `EPos` and the cross term is

`+ crossingEnergy a b = + ∑_{i ∈ edges} J i * a i * b i`

with

- `edges = {(0,x)} ∪ {(M-1,x)}`
- `J i = 1`.

Important correction: the older design note’s `J = 1 / a^2` is not correct for this adapter.
After the density bridge to
`normalizedQuadraticGaussianMeasure (a^2 • massOperatorAsym ...)`,
the `a^2` cancels the `a^-2` in the mass operator quadratic form, so the bond coefficient in the
Lebesgue density is `1/2`, not `1/(2a^2)`, and therefore the RP crossing coupling is `J = 1`.

## (b) Exact `latticeGaussianMeasureAsym` ↔ density identity

The needed identity is not a direct equality on configuration space; it is the pushforward along
the coordinate measurable equivalence `evalMapAsym`.

Precisely:

- `evalMapAsymMeasurableEquiv Nt Ns :
    Configuration (AsymLatticeField Nt Ns) ≃ᵐ AsymLatticeField Nt Ns`
- `((latticeGaussianMeasureAsym Nt Ns a mass ha hmass).map (evalMapAsym Nt Ns))
    = latticeGaussianFieldLawAsym Nt Ns a mass ha hmass`
- `latticeGaussianFieldLawAsym Nt Ns a mass ha hmass
    = normalizedQuadraticGaussianMeasure (a^2 • massOperatorAsym Nt Ns a mass)`
  by
  `GaussianField.latticeGaussianFieldLawAsym_eq_normalizedQuadraticGaussianMeasure`.

This exact pushforward identity is already used in
`Pphi2/AsymTorus/AsymMeasureFactorization.lean`:
the local `hfree` step in
`interactingLatticeMeasureAsym_slice_pushforward_eq_pathMeasure`
rewrites the free part as

- `(gaussianDensityNormConstAsym Nt Ns a mass)^(-1) •
    volume.withDensity (gaussianDensityWeightAsym Nt Ns a mass)`.

So the density bridge assumed by the adapter is present.

## (c) Generic theorem entry point and residual

The entry point is the current theorem

- `MeasureTheory.Measure.isReflectionPositive_of_evenNearestNeighbour`.

It no longer asks for an abstract `h_square`, but it still asks for the explicit Fubini hypothesis

- `hFubini :
    ∀ G, Measurable G →
      Integrable (fun φ => G (positivePart φ) * G (negativePart φ)) d.μ →
      Integrable (hsSquareIntegrand d G)
        (((halfBaseMeasure ι).prod (halfBaseMeasure ι)).prod (stdGaussianPi ι))`.

This residual does not need a new pphi2-specific analytic fact. It can be discharged abstractly
from the integrability hypothesis itself, because:

1. `hsHalfFactor` and `posPartIntegrand` are nonnegative.
2. Therefore `|hsSquareIntegrand d G|` is the nonnegative integrand
   `|G a| * |G b| * posPartIntegrand a z * posPartIntegrand b z`.
3. Tonelli plus `density_hs_factor` gives
   `∫ |hsSquareIntegrand| = ∫ |G (positivePart φ) * G (negativePart φ)| d.μ`
   after the block split `EvenConfig ι ≃ (ι → ℝ) × (ι → ℝ)`.
4. The last quantity is finite by the assumed integrability under `d.μ`.

So the adapter can prove the required `hFubini` locally without touching the dependency.

## (d) Genuine new-math gaps

None for Phase 1.

For Phase 2, the only correction is architectural, not mathematical:

- finite-`Lt` cylinder pullbacks are not automatically full RP for arbitrary positive-time
  cylinder Schwartz tests, because periodization wraps the positive-time tails around the torus;
  this is already explicitly noted in `Pphi2/IRLimit/CylinderOS.lean:290-299`.
- the correct route is:
  1. prove exact finite-lattice RP for no-wrap compact-support positive-time tests;
  2. use one-step time-translation invariance to convert the through-bond link reflection to the
     exact cylinder reflection;
  3. pass UV limits with the existing matrixwise weak-limit theorem
     `cylinderMeasureReflectionPositive_of_tendsto_cf` (or the older
     `OS3_RP_Inheritance.rp_closed_under_weak_limit` style argument), not the stronger abstract
     `IsReflectionPositive.weak_limit`;
  4. extend from compact-support tests to the full positive-time submodule by density plus
     continuity.

The extra local lemmas needed for that route are standard:

- positive time-translation preserves `cylinderPositiveTimeSubmodule`
- compact-support positive-time Schwartz functions are dense in the positive-time Schwartz space
  (hence in the cylinder positive-time submodule)
- no-wrap periodization lemmas using
  `GaussianField.periodizeCLM_eq_on_large_period`
  and the already-present comment plan in `CylinderOS.lean`.

These are implementation obligations, not new conjectures.
