# Cylinder OS3 `hRP` — pphi2 adapter design (uses the generic RP theorem via link-reflection)

**Date**: 2026-07-20. **Goal**: discharge `hRP` in `cylinderIso_OS_of_RP_OS2`
(`Pphi2/AsymTorus/AsymContinuumLimit.lean`) — i.e. prove
`CylinderMeasureSequenceEventuallyReflectionPositive` — by instantiating the now-proved generic
`MeasureTheory.Measure.isReflectionPositive_of_evenNearestNeighbour`
(`reflection-positivity/ReflectionPositivity/LatticeInstance.lean`, GJ 6.2.2, bare trio modulo
one `hFubini` integrability hyp). Bonus on landing: retires pphi2's private axiom
`gaussian_rp_cov_perfect_square` (`OSProofs/OS3_RP_Lattice.lean`).

## THE KEY DESIGN FINDING (vetted, Gemini 3.1-pro 2026-07-20)

pphi2 currently uses the **through-site** time reflection `θ: t ↦ −t (mod N)` (`timeReflectSites`),
which FIXES two sites `t=0, t=N/2` (positive-time = strict `0<t<N/2`) — a periodic two-fixed-plane
geometry that the generic `ι⊕ι` theorem does **not** match. **Resolution (vetted): use the
link-reflection `θ_L: t ↦ −t−1 (mod N)` at the lattice level for RP.**
- On the **even** torus `2t ≡ −1 (mod N)` has no solution ⟹ **zero fixed sites**; the torus splits
  cleanly `Λ₊ = {0,…,N/2−1}`, `Λ₋ = {N/2,…,N−1}` = exactly `ι⊕ι` (`ι = Λ₊ × spatial`).
- Exactly **two crossing time-bonds** per spatial column: `(N−1 ↔ 0)` and `(N/2−1 ↔ N/2)`.
- `θ_L` differs from `θ` (`t↦−t`) by a **one-lattice-spacing shift** (`a`), which **vanishes as
  a→0**; the continuum limit inherits exact OS reflection positivity about `t=0` (the cylinder
  `cylinderTimeReflection` reflection). So the link-reflection is a legitimate, standard
  constructive-QFT discretization choice (reflection through bonds vs through sites) that makes the
  generic `ι⊕ι` theorem apply **verbatim**. NO theorem rewrite needed.

(Gemini also noted: for the NN Laplacian there are strictly no bonds Λ₊↔Λ₋ except the two crossing
links; the generic theorem's crossing-edge machinery handles exactly those two — HS applies as-is.)

## Adapter deliverables

1. **`EvenFerroReflectionData` instance** for the asym torus lattice measure. `ι := (Fin (Nt/2)) ×
   AsymSpatialSites Ns` (positive-time-half × spatial); the block map `ι⊕ι ≃ AsymLatticeSites Nt Ns`
   sends `inl (t,x) ↦ (t, x)`, `inr (t,x) ↦ (θ_L(t), x)` where `θ_L t = N−1−t` on the half. `EPos`
   = the half-lattice action (within-Λ₊ NN kinetic bonds + `Σ_x V(φ_x)` + the crossing-bond
   self-terms). `edges` = the 2 crossing time-bonds per spatial column; `J = 1/a²`, `hJ: 0 ≤ 1/a²` ✓.
2. **Density-vs-covariance bridge (the substantive analytic step).** Show
   `interactingLatticeMeasureAsym Nt Ns P a mass = EvenFerroReflectionData.μ` for this instance.
   pphi2's measure is `latticeGaussianMeasureAsym.withDensity(boltzmannWeightAsym)`, and
   `latticeGaussianMeasureAsym` is defined **via its covariance** `latticeCovarianceAsymGJ`
   (`= (massOperatorAsym)⁻¹` spectral), NOT the explicit `exp(−½⟨φ,Qφ⟩)` density form the bundle
   uses. **Tool: `GaussianField/DensityAsym.lean`** (the asym density↔covariance identity;
   `normalizedGaussianDensityMeasure`-family — verify it gives `GaussianField.measure Q =
   (pi volume).withDensity(Z⁻¹ exp(−½⟨φ,Qφ⟩))`, and that `massOperatorAsym = −Δ_NN + m²` unfolds to
   the NN quadratic `½Σ_NN (1/a²)(φx−φy)² + ½Σ m²φx²` matching `EPos + crossing`). This bridge is
   the main work; scope it first (may need a lemma linking the GJ-normalized covariance to the
   precision-matrix density).
3. **`hFubini`.** The HS-square integrand is integrable on the product measure — discharge from
   pphi2's Nelson/exp-moment integrability (`asymInteracting_expMoment_of_signed` /
   `boltzmannWeightAsym_integrable` + Gaussian moments). Bounded side-condition.
4. **Apply the generic theorem** ⟹ `IsReflectionPositive (interactingLatticeMeasureAsym…) θ_L mPos`.
5. **Link→continuum bridge + sequence.** (a) Transfer the lattice link-reflection RP through the
   asym-torus→cylinder pullback (`cylinderPullbackMeasure`) — the `θ_L` vs continuum `t↦−t`
   one-spacing shift vanishes in the observables' support as `Lt→∞, a→0`. (b) Feed
   `IsReflectionPositive.weak_limit` over the `Lt→∞` sequence ⟹
   `CylinderMeasureSequenceEventuallyReflectionPositive` = `hRP`. (Match `weak_limit`'s convergence
   hyp to pphi2's characteristic-functional convergence, as in `rp_closed_under_weak_limit`.)

## Staging / effort
Deliverable 2 (density bridge) is the crux and should be scoped/attempted first (it's a real
gaussian-field-level identity; check `DensityAsym.lean` covers it before committing). 1,3,4 are
mechanical given 2 + the generic theorem. 5 has the link→continuum shift argument (bounded but
needs care matching pphi2's cylinder pullback + the `weak_limit` interface). Recommend: land 1–4
first (unconditional lattice RP for the asym measure under `θ_L`), then 5 as a second step.

## Downstream
Landing this: (i) discharges cylinder OS3 `hRP` ⟹ with the near-done `hOS2` (`.of_torusOS`),
`cylinderIso_OS_of_RP_OS2` becomes conditional only on the CYL-1a exp-moment axiom (the B2/|f|-form
target); (ii) retires `gaussian_rp_cov_perfect_square`. Also: pphi2 should switch its lattice RP
formulation to `θ_L` (the through-site `t↦−t` stays for OS2 time-reflection invariance, which is a
separate symmetry — no conflict).
