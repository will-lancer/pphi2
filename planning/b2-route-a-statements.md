# B2 route (a) — statement package (FSS ⊕ gap band-split)

**Date**: 2026-07-12. **Status**: **FINALIZED — extraction done, Gemini a-power vet PASSED
(same day)**; statements below are Lean-ready shapes with vetted constants. Vet record inline.
**Parent**: [`layer-b2-freeside-designpass.md`](layer-b2-freeside-designpass.md) (the verdict
and route decision). Target axiom: `asymInteractingVariance_le_freeVariance_lattice_Lt_uniform`
(`AsymExpMomentDischarge.lean:215`).

## Architecture (four statements)

```
S1 (FSS spacetime IR bound)      S2 (17a: fixed-Ls a-uniform gap)
        │                                  │
        ▼                                  ▼
   high-k_t / all k_s≠0 branch      band branch (k_s = 0, |k_t| ≲ κ)
        └──────────────┬───────────────────┘
                       ▼
        S3 (band-stitching / mode-split master lemma)
                       │  + S4 (spectral form of Var_int/Var_free — DFT layer)
                       ▼
        the B2 axiom becomes a theorem
```

## S1 — FSS infrared bound, INTEGRATED quadratic form (NEW AXIOM, Standard) — VETTED

Refinement over the draft (decisive, from the extraction): state FSS as a **quadratic-form
bound on the zero-mode complement**, not per-mode — this eliminates the interacting momentum
two-point object, the interacting Parseval, AND interacting translation invariance from the
whole package. Lean-ready shape (`c_k(h) = Σ_x e_k(x)·h(x)` in the proved eigenbasis
`massEigenvectorBasisAsym`; the zero-mode condition is `Σ_x h x = 0`):

```lean
/-- FSS/Gaussian-domination infrared bound, integrated form: on the zero-mode complement the
    interacting second moment is dominated by the MASSLESS free quadratic form, uniformly in
    (a, Nt, Ns), at all couplings.  Reference: Fröhlich–Simon–Spencer CMP 50 (1976); Simon
    P(φ)₂; GJ.  Strategy: Gaussian domination Z[h] ≤ Z[0]·exp(½⟨h,(−Δ)⁻¹h⟩) via lattice RP
    over the kinetic bonds (single-site factor — including mass and Wick terms — is untouched),
    then the t²-expansion at the Z₂-even measure. -/
axiom fss_infrared_quadratic (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (h : AsymLatticeField Nt Ns) (hzero : ∑ x, h x = 0) :
    ∫ ω, (ω h)^2 ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) ≤
      (a^2)⁻¹ * ∑ k, (if k = 0 then 0 else (massEigenvaluesAsym Nt Ns a 0 k)⁻¹ * (c_k h)^2)
```
(Implementation detail: the massless RHS can equivalently be the DFT form via
`abstract_spectral_eq_dft_spectral_2d_asym` at `mass = 0` on nonzero modes, i.e.
`D̂₀(m₁,m₂) = latticeEigenvalue1d Nt a m₁ + latticeEigenvalue1d Ns a m₂`; mind
`latticeFourierNormSq` ≠ 1 at Nyquist. The mass-0 eigenbasis vs mass-m eigenbasis coincide —
the operator differs by a multiple of the identity.)

**Vet record (Gemini 3.1-pro, 2026-07-12): constant `c₀ = 1` is EXACT** in this GJ
normalization — reconstruction: the kinetic action is `½⟨φ,(−Δ_unscaled)φ⟩` with
`−Δ_unscaled = a²(−Δ_lattice)` (coupling β = ½, no a-prefactors), the classical bound
`⟨|φ̂|²⟩ ≤ 1/D̂_unscaled = 1/(a²D̂₀)` matches the free-variance prefactor `(a²)⁻¹` exactly;
mass + Wick terms sit in the single-site factor and never enter the denominator.
Discharge route (later, shares Layer A's Griffiths–Simon machinery): RP/chessboard over
kinetic bonds → Gaussian domination → second derivative.

## S2 — 17a: fixed-`Ls` a-uniform gap, γ-form (NEW AXIOM, Standard; shared with OS4) — VETTED

Carrier correction from the extraction: the PROVED gap object is the operator-norm contraction
`γ_op = ‖A_W‖/λ₀ < 1` on the ground-orthogonal complement (`asymTransferNormalized_gap`,
`AsymSpectralGap.lean:29`), NOT `exp(−a·asymMassGap)`; and the transfer operator genuinely
depends on `Nt` through `wickConstantAsym`. State S2 on the consumable object:

```lean
axiom asymTransferGap_uniform_fixedLs
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) (Ls : ℝ) (hLs : 0 < Ls) :
    ∃ m₀ : ℝ, 0 < m₀ ∧ ∃ a₀ : ℝ, 0 < a₀ ∧
    ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (ha : 0 < a),
      (Ns : ℝ) * a = Ls → a ≤ a₀ →
      ∀ v, ⟪asymGroundVector Nt Ns P a mass ha hmass, v⟫ = 0 →
        ‖asymTransferNormalized Nt Ns P a mass ha hmass v‖ ≤ Real.exp (-(m₀ * a)) * ‖v‖
```
NO coupling hypothesis (regime (ii); the coupled `Ns·a = Ls` quantifier is what the removed
false predecessor lacked — PR #60). **Vet record: `Nt`-dependence harmless** —
`wickConstantAsym(Nt, Ns, a) → c(∞, Ns, a)` as `Nt → ∞` at fixed `(Ns, a)`, Schrödinger
eigenvalues are continuous in the polynomial coefficients, every finite `Nt` has a positive
gap (compact resolvent, bounded-below even polynomial), so `inf_{Nt} m_gap > 0`. Expert story:
`T_a → e^{−aH(Ls)}` compact-resolvent convergence
(`reflection-positivity/docs/B2_UNIFORMITY_QUESTION.md`, Simon Ch. VI). Enters the build with
S3 (no-consumer policy); also the OS4/M4 brick.

## S3 — three-way split master theorem (THEOREM, not an axiom) — constants VETTED

With `κ := min(mass, m₀)`, split `G = G₀ + G_low + G_high` **in the free eigenbasis** (S4):
`G₀` = zero mode, `G_low` = spatially-constant modes with `0 < D̂₀ ≤ κ²`, `G_high` = rest.

1. `Var_int(G) ≤ 3(Var_int G₀ + Var_int G_low + Var_int G_high)` — Cauchy–Schwarz inside the
   integral; **no interacting orthogonality/translation invariance needed anywhere**.
2. High branch: S1 + `D̂_m/D̂₀ ≤ 1 + m²·max(Ls²/c_s, 1/κ²)` on High ⟹
   `Var_int(G_high) ≤ C_high·Var_free(G_high)`.
3. Zero+low branch (spatially constant, band-limited): Pieces 1–3 susceptibility bound + B5b,
   then the **band-limited free-side comparison**, whose a-ledger is now VETTED:
   `LHS ≤ (2/(m₀a))·Σ_t C_slice(g_t)` with the slice zero-mode variance `1/(2m)`
   (a-, Ns-free) giving `LHS ~ (Ns²/(m·m₀·a))·Σ_t g_t²`; RHS
   `Var_free(G_band) ≥ (Ns/(a²(κ²+m²)))·Σ_t g_t²` (temporal Parseval, symbol ≤ κ²);
   ratio `≤ Ns·a·(κ²+m²)/(m·m₀) = Ls·(κ²+m²)/(m·m₀)` — **the a's cancel via `Ns·a = Ls`**;
   `C_band = C_band(Ls, m, m₀)`.
4. Free-side reassembly is EXACT: `Var_free G₀ + Var_free G_low + Var_free G_high = Var_free G`
   (eigenbasis diagonality). Final `C = 3·max(C_high, C_band, C_zero)`.

## S4 — free-side spectral/DFT layer (THEOREMS; **delegable**; shrunk by the S1 refinement)

Only free-measure obligations remain (no interacting Parseval, no interacting translation
invariance):
- [ ] Assemble the named lemma `Var_free(G) = (a²)⁻¹·Σ_k λ_k⁻¹·c_k(G)²` from the proved chain
  `latticeGaussianMeasureAsym_cross_moment` (`AsymLatticeMeasure.lean:64`) →
  `latticeCovarianceAsymGJ_inner_eq_inv_a_sq_spectral` (`AsymWickVariance.lean:267`) →
  `covariance_spectralLatticeCovarianceAsym_eq` (`AsymCovariance.lean:688`).
- [ ] Eigenbasis projections (zero/low/high) + the additivity of `Var_free` across them
  (diagonal form) + `Σ_x (G_band)_t x`-type slice extraction for the band branch.
- [ ] The closed-form dispersion on the band/high sets via
  `massOperator_product_eigenvector_asym` (`AsymCovariance.lean:650`) +
  `latticeEigenvalue1d`; mind `latticeFourierNormSq` at Nyquist and the signed
  `fourierFreq` indexing.

## Sequencing (updated 2026-07-12, evening)

1. ~~Extraction~~ DONE; ~~Gemini a-power vet~~ **PASSED** (c₀ = 1; band ratio
   `Ls(κ²+m²)/(m·m₀)`; 3-way split exact on the free side; `Nt` harmless in S2).
2. ~~S4~~ **LANDED** (`6234206`, `Pphi2/AsymTorus/AsymFreeSpectral.lean`, 0 axioms/sorries;
   orthogonality lemma `massEigenvectorBasisAsym_orthogonal` derived from the Hermitian API).
3. ~~S1 + high branch~~ **LANDED** (`af9579e`, `Pphi2/AsymTorus/AsymInfraredBound.lean`):
   axiom `fss_infrared_quadratic` (pinned statement verbatim; audit + vetting record in the
   same commit) + proved consumer `asymHighModes_variance_le_freeVariance` —
   kernel-verified footprint `[trio, fss_infrared_quadratic]`. Supporting proved lemmas:
   `massOperatorAsym_const`, `sum_massEigenvectorBasisAsym_eq_zero_of_ne` (the
   constants-are-`m²`-eigenvectors pairing), `sum_asymModeProj_eq_zero`,
   `inv_sub_le_one_add_div_mul_inv`.
4. **REMAINING — the band/zero branch + stitching** (the last B2 analytic arc):
   a. S2 (`asymTransferGap_uniform_fixedLs`, γ-form) enters with its consumer (b);
   b. the band-limited free-side comparison (vetted ledger — pure Gaussian/DFT computation,
      `C_band = Ls(κ²+m²)/(m·m₀)`) + Pieces 1–3 applied to the band projection + B5b;
   c. the three-way stitching (`3·max(C_high, C_band, C_zero)`) closing
      `asymInteractingVariance_le_freeVariance_lattice_Lt_uniform` → theorem (Piece 5).
   The zero/band split needs the spatially-constant-mode set characterization (the
   `k_s = 0` column) — the one S4 deliverable deliberately skipped (zero-mode
   identification); scope it as the first task of arc 4.

### Arc-4 staging (2026-07-12, evening)

**Stage A — LANDED (`74746c2`, `AsymSpatialConstant.lean`, 462 lines, 0 axioms/sorries;
all headline declarations kernel-verified to the bare trio; sharp `spatialGap` constant, and
A6 delivered `16/Ls² ≤ spatialGap` — use the 16/Ls² form for κ-selection):** new file
`AsymSpatialConstant.lean` with (A1) `sliceAvgProj` (spatial average per time slice, linear),
(A2) commutation with `massOperatorAsym` (from `massOperatorAsym_translation_commute` —
`sliceAvgProj` is the average of spatial shifts), (A3) discrete spatial Poincaré:
`sliceAvgProj v = 0 → ⟨v, A v⟩ ≥ (spatialGap + mass²)·‖v‖²` with
`spatialGap Ns a := (4/a²)·sin(π/Ns)²` (per-slice 1D DFT), (A4) the punchline —
eigenvectors with `λ_k < mass² + spatialGap` are spatially constant (quadratic-form
squeeze via A2+A3: `(λ_k − m² − g_s)·‖(1−Π)e_k‖² ≥ 0`), (A5) `asymModeProj` of a
sub-`spatialGap` mode set is slice-constant, plus (A6) the a-uniformity
`Ns·a = Ls → spatialGap ≥ (16/π²)·(π/Ls)²`-type bound (the `sin x ≥ (2/π)x` trick) for the
κ selection.

**Stage B — interface extraction DONE (2026-07-12, evening). Two holes remain, everything
else composes.** The algebraic shell `interacting_second_moment_bound_to_freeCovariance_sum`
(`AsymB5bSingleSlice.lean:273`, with `piece3_pathMeasure_bound_to_freeCovariance_sum:224`)
already stitches B3 + Piece 3 + B5b into
`∫(ωG)² ≤ (2/(1−γ)·C_B5b + C_rem_free)·freeSingleSliceCovarianceSum` — but takes `hPiece3`
and `hRem` as hypotheses. The full brick inventory with verbatim signatures is in the Stage-B
extraction (agent report, 2026-07-12): B3 bridge `interacting_second_moment_eq_pathMeasure`
(`AsymVarianceDischarge.lean:64`, arbitrary `G`), the reflection-positivity engine
(`GappedTransfer`, `susceptibility_le`, `averaged_susceptibility_bound` at `(1+γ)/(1−γ)`,
`connected_two_point_le`), `asymGappedTransfer'` (γ = existential operator-norm contraction —
S2 must be stated on exactly this γ), Piece 1 (`norm_sq_proj_obsTrunc_omega_le`, RHS =
`groundSliceVariance`), the finite-K bridge theorems (`AsymBridgeInstance.lean:288/:320/:346`,
single-`g` diagonal form, constant `2/(1−γ)`, tail `C_rem·Nt·γ^Nt`), the Piece-3 K→∞ engine
(**complete**: `AsymBridgeKLimit.lean:296/:320`), and the slice API (`asymSliceEquiv`,
`singleSliceLatticeField`, `slicePairing`).

**Hole B-I (`hPiece3`) — substantive:** `∫(slicePairing G ψ)² dpath ≤
(2/(1−γ))·groundSliceVarianceSum + C_rem·Nt·γ^Nt·(…)` for slice FAMILIES (the landed finite-K
bounds are diagonal single-`g`). Route = the 7 steps of `layer-b2-completion-route.md:24`:
square expansion into the double time sum, **pathMeasure cyclic translation invariance**
(unproved), discharge of `twoPoint_dictionary`'s bounded-observable hypotheses for the
truncated observables, kernel→operator pairing, then `connected_two_point_le` +
`averaged_susceptibility_bound`, and the landed K→∞ transfer. ~400–800 lines.

**Hole B-II (free-side band comparison) — substantive but pure Gaussian, ledger pre-vetted:**
for slice-constant band-limited `G` (Stage A modeset, `κ² < spatialGap`):
`freeSingleSliceCovarianceSum ≤ C(Ls, m, κ, m₀)·Var_free(G)` — needs the temporal 1D-DFT /
temporal-symbol lemma (nothing temporal exists yet; `AsymSpatialConstant` built the spatial
direction) + the one-slice free covariance zero-mode evaluation. This replaces the flagged
`hFreeAssemble` trap hypothesis (`AsymB5bSingleSlice.lean:319`) **on the band only** — the
all-`G` version is impossible (the design-pass verdict); the band restriction is what makes
the vetted `Ls(κ²+m²)/(m·m₀)` ledger close.

**S2 lands with B-I** (its γ-uniformity is what makes `2/(1−γ)` a-uniform): Pieces 2–3 of the Route-A
blueprint (finite-K time-family susceptibility estimate + K→∞ DCT), applied to slice-constant
fields, + B5b; plus the band-limited free comparison with the vetted `Ls(κ²+m²)/(m·m₀)`
ledger. S2 (`asymTransferGap_uniform_fixedLs`) enters the build here with its consumer.

**Stage C — stitching:** the 3-way split (`G_high` via the landed high-branch theorem with
`S_high = {k : m² + κ² ≤ λ_k}`, complement = band/zero which is slice-constant by Stage A
when `κ² < spatialGap`), `3·max(C_high, C_band)`, Piece-5 assembly → the B2 axiom becomes a
theorem.
5. Clustering axioms 14/15 ride the same trace bridge afterward (`cyl-2a-spectral-gap.md`).
