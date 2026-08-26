/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Layer A / Layer B2 input axioms for the volume-uniform exp-moment

Defines two upstream-input axioms consumed by the Layer C assembly. Layer A
is restricted to `P.n = 4` with `hf : ∀ x, 0 ≤ f x`; the old all-`P` type is
**FALSE** (one-site sextic) and must not be restored or discharged. The torus
Layer B2 wrapper does not discharge the lattice axiom. The Layer C assembly
inherits both footprints.

## What this file does

States two clean, individually-vettable axioms:

* **`asymInteracting_mgf_gaussianDominated`** — Layer A Newman MGF
  comparison, restricted to `P.n = 4` with `hf : ∀ x, 0 ≤ f x`. The
  old all-`InteractionPolynomial` type is **FALSE**: a one-site sextic
  (Simon–Griffiths double-well family, nonnegative source) reverses the
  claimed `K = 2` bound. Do **not** discharge this axiom; do not restore
  the all-`P` quantifier. Signed `f` is recovered only as a consumer of
  this quartic axiom (`AsymSignedSplit.lean`).

* **`asymInteractingVariance_le_freeVariance_lattice_Lt_uniform`** —
  Layer B2 Route-A lattice output: the Lt-uniform interacting/free
  variance bound on the lattice. The torus wrapper
  `asymInteractingVariance_le_freeVariance_Lt_uniform` is a pushforward
  theorem whose axiom footprint is exactly this lattice axiom; it does
  not discharge the mathematical content.

The **Layer C assembly theorem**
`asymInteracting_expMoment_volume_uniform_proof` — combining Layer A +
Layer B2 + the joint-↔-torus pushforward — lives in
`Pphi2/AsymTorus/AsymSignedSplit.lean`. It **inherits** the quartic Layer A
axiom; do not treat the assembly as a Newman discharge.

## Why these are pphi2 axioms

These are interface contracts, not a claim that Layer A is a vetted
provable theorem on the full even-polynomial class. The all-`P` Newman
statement is false (see Status). The Layer C wiring can still be checked
against the live quartic types.

**Net axiom-count impact**: the original
`asymInteracting_expMoment_volume_uniform` axiom sits alongside the
two factored axioms (Layer A + Layer B2). Layer A is **not** a textbook
Newman instance on general even `P` (the all-`P` type is false; see Status).
Layer B2 remains an open lattice axiom; the torus wrapper below does not
remove it.

## Status

* Layer A axiom (`asymInteracting_mgf_gaussianDominated`): live type is
  `P.n = 4` with `hf : ∀ x, 0 ≤ f x`. The old all-`P` type is **FALSE**
  (one-site sextic, 2026-08). Sign-restricted 2026-07-13 after the
  mixed-sign quantifier was found FALSE. Do not discharge; do not
  restore all-`P`. See `AXIOM_AUDIT.md` and
  `planning/layer-a-lee-yang-scoping.md`.
* Layer B2 Route-A lattice axiom
  (`asymInteractingVariance_le_freeVariance_lattice_Lt_uniform`):
  factored 2026-06-23 as the remaining lattice assembly input; still an
  axiom.
* Layer C theorem: proved in `AsymSignedSplit.lean` as a wrapper
  (split-seminorm form); axiom footprint includes quartic Layer A and Layer B2.

## References

* `docs/asym-interacting-expmoment-volume-uniform-discharge-plan.md`
  — full discharge architecture.
* `docs/asym-expmoment-discharge-via-lee-yang-vet-request.md`
  — deep-think vet of Layer A architecture.
* `docs/asym-l2-operator-port-scoping.md` — Layer B1 (Phases 1-4 done).
* `lee-yang/PLAN.md` — Layer A's upstream home.
-/

import Pphi2.AsymTorus.AsymVarianceBound

noncomputable section

open MeasureTheory GaussianField

namespace Pphi2

/-! ## Layer A axiom (lee-yang adapter output) -/

/-- **Layer A: Newman MGF Gaussian-domination, quartic only.**

Live type: `P.n = 4` and sitewise-nonnegative source `hf : ∀ x, 0 ≤ f x`.
Do **not** discharge this axiom. Do not restore the all-`P` quantifier.

Newman (1975) compares the MGF to a Gaussian with the *interacting*
variance, but only for measures in the Lee–Yang class. Simon–Griffiths
supply that class for quartic site laws `exp(-a s^4 - b s^2)`, not for
the repository's full even-polynomial family.

**The unrestricted (all-`P`) type is FALSE.** A one-site sextic
(Simon–Griffiths double-well family, nonnegative source) reverses the
claimed `K = 2` bound: take `Nt = Ns = 1`, `mass = 1`, and an admissible
`P` with `P.n = 6`. The unique field coordinate has a normalized
even-sextic law whose `q → ∞` limit is `ν = (δ₋₁ + 16 δ₀ + δ₁)/18`. For
the sitewise-nonnegative source `f(*) = 9`,
`E_ν exp(9|X|) ≰ 2 exp((81/2) E_ν X²)`. Finite large-`q` models are exact
instances of `interactingLatticeMeasureAsym`. Thus `hf : ∀ x, 0 ≤ f x`
does **not** save `n ≥ 6`.

**SIGN RESTRICTION (2026-07-12/13)** remains: the unrestricted
quantifier over mixed-sign `f` is separately FALSE (2-spin counterexample;
Lebowitz-κ₄). Signed consumers in `AsymSignedSplit.lean` inherit this
quartic axiom at `f₊`, `f₋` and are not a discharge.

**Adapter (2026-08-18).** `lee-yang` at `d48ee59` is pinned in
`lakefile.toml`. `asymInteracting_mgf_gaussianDominated_of_griffithsSimon`
(`AsymInteractingLeeYang.lean`) proves this inequality from
`GriffithsSimonMGFData` for the pushforward along `ω ↦ ω f`. That data is
**not** constructed for Wick `:P(φ):` on `interactingLatticeMeasureAsym`
(lee-yang A3 deferred; finite Ising Newman is the wrong polynomial class).
Keep this axiom. Do not apply free-field OS or Gaussian MGF in its place.

**Reference**: C. M. Newman, Comm. Math. Phys. 41 (1975), Theorem 3;
Simon–Griffiths, Comm. Math. Phys. 33 (1973). -/
axiom asymInteracting_mgf_gaussianDominated
    (P : InteractionPolynomial) (hP : P.n = 4) (mass : ℝ) (hmass : 0 < mass)
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (ha : 0 < a)
    (f : AsymLatticeField Nt Ns) (hf : ∀ x, 0 ≤ f x) :
    Integrable (fun ω => Real.exp (|ω f|))
      (interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) ∧
    ∫ ω, Real.exp (|ω f|)
      ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) ≤
    2 * Real.exp ((1/2) *
      ∫ ω, (ω f) ^ 2
        ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass))

/-! ## Layer B2 axiom (chessboard / reflection-positivity output) -/

/-- **Layer B2 Route-A lattice output: `Lt`-uniform interacting-vs-free
variance bound on the lattice**.

There exists a single constant `C > 0` such that, for **every** time
period `Lt` (with `Ls` fixed), every refinement `(Nt, Ns, a)` with
`Nt · a = Lt`, `Ns · a = Ls`, and every lattice test function
`G : AsymLatticeField Nt Ns`,
`∫(ω G)² dμ_int ≤ C · ∫(ω G)² dμ_free`.

**Comparison to the existing Layer B1 bound**:
`asymTorusIso_interacting_second_moment_density_transfer`
(`Pphi2/AsymTorus/AsymContinuumLimit.lean:48`) and the Layer B1 wrapper
`asymInteractingVariance_le_freeVariance_torus`
(`Pphi2/AsymTorus/AsymVarianceBound.lean`) give the same bound but with
`C = C(Lt, Ls)` *depending on `Lt`* (because the Nelson exp-moment
constant `K(Lt, Ls)` from `asymNelson_exponential_estimate_iso` depends
on `Lt`). Layer B2 is the **uniformity-in-`Lt`** refinement: the bound
holds with a single constant uniformly as `Lt → ∞` at fixed `Ls`.

**Mathematical content**: the cylinder mass gap (which IS unconditional
in the cylinder regime — `Ls` fixed, `Lt → ∞` is a 1D thermodynamic
limit with isolated transfer-matrix top eigenvalue by infinite-dim
Perron-Frobenius, see `Pphi2/AsymTorus/AsymPositivity.lean`) controls
the interacting susceptibility via the lattice Källén-Lehmann sum
rule. The uniformity-in-`Lt` then follows from chessboard / FSS
(Fröhlich-Simon-Spencer) estimates that bound the interacting
2-point function by the free 2-point function via reflection
positivity, without needing a full spatial cluster expansion.

**Upstream discharge plan**: a new `reflection-positivity` repo
(scoped 2026-05-31) will provide the abstract chessboard / multiple-
reflection algebra; a pphi2 adapter then specializes to the asym
lattice's reflection structure and produces this bound. The cylinder
transfer-matrix infrastructure (`AsymL2Operator`, `AsymJentzsch`,
`AsymPositivity`) is the foundation. See
`docs/asym-l2-operator-port-scoping.md` for the Layer B2 sub-plan
and the noted "shares discharge path with the square's open
`spectral_gap_uniform`" connection.

**Reference**: Glimm-Jaffe Ch. 6, 10, 19 (chessboard estimates);
Fröhlich-Simon-Spencer (1976), "Phase Transitions and Reflection
Positivity I", Comm. Math. Phys. 50, 79-95 (the original FSS bound);
Simon, *The P(φ)₂ Euclidean QFT* (1974) Ch. V.

✅ Vetted: deep-think-gemini (2026-06-02) — confirmed the Lt-uniform
variance bound from chessboard + cylinder mass gap (Källén-Lehmann
sum rule) is the standard result; the cylinder shortcut (no full 2D
cluster expansion needed) is mathematically sound and computationally
tractable.

**Discharge update (2026-06-02; see `docs/layer-B2-discharge-plan.md`).**
The "chessboard / FSS … shares discharge path with the square's open
`spectral_gap_uniform`" framing above is SUPERSEDED: at fixed `Ls` the
cylinder mass gap is uniform via compact-resolvent convergence
(`T_a → e^{−aH(Ls)}`, Simon Ch. VI), so **no chessboard is needed** (FSS is
only for the thermodynamic `Ls → ∞` limit; see
`reflection-positivity/docs/B2_UNIFORMITY_QUESTION.md`). The transfer-matrix
spectral gap is now **proved**: `asymGappedTransfer'` /
`susceptibility_le` (via `AsymGappedTransfer.lean` + `AsymSpectralGap.lean`
+ the `reflection-positivity` dep). The remaining discharge is the 3-piece
plan: (1) the interacting Källén-Lehmann/Feynman-Kac representation
(the un-formalized measure↔operator bridge — a more-fundamental axiom-to-be);
(2) the free representation (provable, Gaussian); (3) the int/free ratio,
whose `1/a` cancellation is essential — a naive `Var_int ≤ 1/(1−γ)·Var_free`
is `a`-non-uniform and WRONG.

**Piece-5 factoring note (2026-06-23).** The former torus-level axiom
`asymInteractingVariance_le_freeVariance_Lt_uniform` is a **pushforward
wrapper** of this lattice axiom (via
`asymTorusInteractingMeasureIso = (interactingLatticeMeasureAsym).map
asymTorusEmbedLiftIso` and
`(asymTorusEmbedLiftIso ω) f = ω (asymLatticeTestFnIso f)`). The lattice
axiom remains in the torus theorem's axiom footprint; this is not a
discharge of the interacting-vs-free bound. The remaining Route-A
obligation stays at the lattice level, where Piece 4
`interacting_second_moment_bound_to_lattice_free_covariance` is stated.

MIGRATION NOTE (2026-07-13): the thresholded form is now a THEOREM
(`asymInteractingVariance_le_freeVariance_torus_thresholded` /
`asymInteractingVariance_le_freeVariance_lattice_thresholded`, 5 vetted axioms);
this all-(Lt,a) axiom remains only for the legacy Layer-C wiring and is
over-broad at small Lt / coarse a (true but unproved there) — consumers should
migrate to the thresholded form (planning/b2-stageB-holes-spec.md §C4 design). -/
axiom asymInteractingVariance_le_freeVariance_lattice_Lt_uniform
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (Ls : ℝ) [Fact (0 < Ls)] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Lt : ℝ) [Fact (0 < Lt)]
        (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (ha : 0 < a),
        (Nt : ℝ) * a = Lt → (Ns : ℝ) * a = Ls →
        ∀ (G : AsymLatticeField Nt Ns),
          ∫ ω : Configuration (AsymLatticeField Nt Ns), (ω G) ^ 2
            ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) ≤
          C * ∫ ω : Configuration (AsymLatticeField Nt Ns),
            (ω G) ^ 2
              ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass)

/-- **Layer B2 torus pushforward wrapper.** Same bound as the lattice axiom
`asymInteractingVariance_le_freeVariance_lattice_Lt_uniform`, transported
along `asymTorusEmbedLiftIso`. Not a discharge: the mathematical content
is exactly that axiom. -/
theorem asymInteractingVariance_le_freeVariance_Lt_uniform
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (Ls : ℝ) [Fact (0 < Ls)] :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Lt : ℝ) [Fact (0 < Lt)]
        (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (ha : 0 < a),
        (Nt : ℝ) * a = Lt → (Ns : ℝ) * a = Ls →
        ∀ (f : AsymTorusTestFunction Lt Ls),
          ∫ ω : Configuration (AsymTorusTestFunction Lt Ls), (ω f) ^ 2
            ∂(asymTorusInteractingMeasureIso Lt Ls Nt Ns a P mass ha hmass) ≤
          C * ∫ ω : Configuration (AsymLatticeField Nt Ns),
            (ω (asymLatticeTestFnIso Lt Ls Nt Ns a f)) ^ 2
              ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) := by
  obtain ⟨C, hC_pos, hC_bound⟩ :=
    asymInteractingVariance_le_freeVariance_lattice_Lt_uniform P mass hmass Ls
  refine ⟨C, hC_pos, ?_⟩
  intro Lt _hLt Nt Ns _ _ a ha hvolt hvols f
  set g := asymLatticeTestFnIso Lt Ls Nt Ns a f
  set μ_int_T := asymTorusInteractingMeasureIso Lt Ls Nt Ns a P mass ha hmass
  set μ_int_L := interactingLatticeMeasureAsym Nt Ns P a mass ha hmass
  have hι_meas : Measurable (asymTorusEmbedLiftIso Lt Ls Nt Ns a) :=
    asymTorusEmbedLiftIso_measurable Lt Ls Nt Ns a
  have h_eval : ∀ ω : Configuration (AsymLatticeField Nt Ns),
      (asymTorusEmbedLiftIso Lt Ls Nt Ns a ω) f = ω g :=
    asymTorusEmbedLiftIso_eval_eq Lt Ls Nt Ns a f
  have h_pushforward : μ_int_T =
      Measure.map (asymTorusEmbedLiftIso Lt Ls Nt Ns a) μ_int_L := rfl
  have h_F_sq_meas :
      AEStronglyMeasurable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
        (ω f) ^ 2) μ_int_T :=
    ((configuration_eval_measurable f).pow_const 2).aestronglyMeasurable
  rw [h_pushforward]
  rw [integral_map hι_meas.aemeasurable h_F_sq_meas]
  have h_integrand :
      ∫ ω : Configuration (AsymLatticeField Nt Ns),
          (asymTorusEmbedLiftIso Lt Ls Nt Ns a ω f) ^ 2 ∂μ_int_L =
        ∫ ω : Configuration (AsymLatticeField Nt Ns), (ω g) ^ 2 ∂μ_int_L := by
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun ω => ?_
    simpa using congrArg (fun x : ℝ => x ^ 2) (h_eval ω)
  rw [h_integrand]
  exact hC_bound Lt Nt Ns a ha hvolt hvols g

/-! ## Layer C: assembly theorem

**Moved (2026-07-13).** The Layer C assembly theorem
`asymInteracting_expMoment_volume_uniform_proof` now lives in
`Pphi2/AsymTorus/AsymSignedSplit.lean`. It consumes the quartic
Layer A axiom (see its docstring above) via the signed split
`asymInteracting_expMoment_of_signed`; do not discharge Layer A there.
The assembly's free-variance seminorm is the split form
`C · (Var_free(f₊) + Var_free(f₋))`. -/

end Pphi2

end
