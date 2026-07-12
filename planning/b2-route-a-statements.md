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

## Sequencing (updated)

1. ~~Extraction~~ DONE; ~~Gemini a-power vet~~ **PASSED 2026-07-12** (c₀ = 1; band ratio
   `Ls(κ²+m²)/(m·m₀)`; 3-way split exact on the free side; `Nt` harmless in S2).
2. **S4 — next delegable item** (free-side DFT assembly, all ingredients named above).
3. S1 + S2 enter Lean together with S3's statement (consumers in place); audit rows +
   `audit/vetting/` records citing this doc's vet record, in the same PR.
4. S3 proof: high branch (computation from S1 + S4), band branch (Pieces 1–3 + B5b + the
   vetted band comparison), stitching; then Piece-5 assembly converts the B2 axiom to a
   theorem; clustering axioms 14/15 ride the same trace bridge (`cyl-2a-spectral-gap.md`).
