# B2 route (a) — statement package (FSS ⊕ gap band-split)

**Date**: 2026-07-12. **Status**: DRAFT — normalization slots pending the asym-Fourier
extraction; Gemini a-power vet required before any statement enters Lean.
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

## S1 — FSS infrared bound, spacetime-momentum form (NEW AXIOM, Standard)

⚠ This is the **full spacetime** `k = (k_t, k_s) ≠ (0,0)` version — NOT the parked spatial
version in `docs/fss-infrared-bound-spec.md` (which was drafted for the `Ls → ∞` spatial IR
and whose "not for B2" banner is superseded by the design-pass verdict). Mathematical shape:

  `S_int(k) ≤ c₀ / D̂₀(k)`  for all `k ≠ 0`,

with `S_int(k)` the interacting momentum two-point of `interactingLatticeMeasureAsym` and
`D̂₀(k)` the **massless** spacetime lattice symbol (the `mass = 0` part of the asym
eigenvalues). Uniform in `(a, Nt, Ns)`; valid at all couplings; robust to the Wick counterterm
(Griffiths–Simon class single-site measure; RP/Gaussian-domination proof — NOT Brascamp–Lieb).
Normalization slots (fill from the extraction; then Gemini-vet):
- [ ] exact `D̂₀(k)` formula and its a-powers in the GJ convention;
- [ ] the constant `c₀` (GJ field normalization may make it ≠ 1; classical form is
  `1/(2·Σᵢ(1−cos kᵢa)/a²)`-type — pin against `massEigenvaluesAsym`);
- [ ] whether `S_int(k)` is defined via a cos/sin real basis (no complex layer needed) —
  preferred, matching the existing eigenbasis machinery.
Reference: Fröhlich–Simon–Spencer CMP 50 (1976); Simon *P(φ)₂*; GJ. Vetting: carries the
2026-06-03 deep-think rank-#1 verdict for the k≠0 domination question + this session's
design-pass confirmation; needs a fresh protocol vet of the FINAL normalized statement.
Discharge route (later): Gaussian domination `Z[h] ≤ Z[0]·exp(½⟨h, kinetic⁻¹h⟩)` via lattice
RP over kinetic bonds — shares the Griffiths–Simon machinery with Layer A (A3).

## S2 — 17a: fixed-`Ls` a-uniform transfer gap (NEW AXIOM, Standard; shared with OS4)

  `∃ m₀ > 0, ∃ a₀ > 0, ∀ (Ns, a) with Ns·a = Ls and a ≤ a₀: m₀ ≤ asymMassGap(Ns, a, P, mass)`

(Exact carrier object per the extraction — the gap should depend only on the spatial slice
data `(Ns, a, P, mass)`, not `Nt`.) NO coupling hypothesis needed (regime (ii): spatially
cutoff Hamiltonian, trace-class semigroup, simple ground state at all couplings). This is the
statement whose fixed-`Ns` predecessor was removed as false in PR #60; the coupled `Ns·a = Ls`
quantifier is exactly what neutralizes the wrong-counterterm mechanism (the Wick zero-mode
term is `m⁻²/Ls²`, finite). Expert-vetted story: `T_a → e^{−aH(Ls)}` compact-resolvent
convergence (`reflection-positivity/docs/B2_UNIFORMITY_QUESTION.md`, Simon Ch. VI).
Consumer: S3's band branch (and later the OS4/M4 campaign — same brick). Enters the build
with S3, not before (no-consumer policy).

## S3 — band-stitching master lemma (THEOREM to prove, not an axiom)

Shape: for `κ := min(mass, m₀)` (with `m₀` from S2),

  `Var_int(G) ≤ C_high·Σ_{k ∈ High} |Ĝ(k)|²/D̂₀(k) + C_band·(band branch via Pieces 2–5 + B5b)`
  `           ≤ C(P, mass, Ls) · Var_free(G)`

where `High = {k : k_s ≠ 0 or |k̂_t| ≥ κ}` and the band is the complement minus the FSS
region. Constants to pin: the massless→massive comparison `sup_{High}(D̂_m/D̂₀) ≤ 1 + m²·
max(Ls²/c_s, 1/κ²)` and the band phase-loss factor `sup_{|k_t| ≤ κ}(…)` from the
oscillation-blind susceptibility applied to the band-projected `G`. Slots:
- [ ] Fourier projection of `G` onto the band: needs S4's real-basis Parseval;
- [ ] the band branch consumes Pieces 2–3 exactly as landed, applied to `G_band` (verify the
  slice family of a band-projected vector stays in the Piece-1/2 hypotheses);
- [ ] cross terms vanish by orthogonality of the mode spaces under BOTH quadratic forms
  (free: diagonal; interacting: needs translation invariance of `μ_int` — check the
  extraction's item 5; if asym translation invariance is unproved, it is a small port of the
  square machinery and becomes S4's second obligation).

## S4 — spectral/DFT layer (THEOREMS, mostly exist or port)

- [ ] Free side: `Var_free(G) = Σ_k λ_k⁻¹·|Ĝ(k)|²` with the GJ a-powers (should exist as the
  spectral form of `latticeCovarianceAsymGJ`; extraction item 6).
- [ ] Interacting side: define `S_int(k)` (real cos/sin form) and prove
  `Var_int(G) = Σ_k |Ĝ(k)|²·S_int(k)` from translation invariance of
  `interactingLatticeMeasureAsym` (extraction item 5; port from the square symmetry cores
  landed on this branch if missing — the weight-generic `latticeWithDensity_symmetry_invariant`
  was built precisely to make such ports cheap).

## Sequencing

1. Extraction report → fill slots → **Gemini a-power vet of S1 + S3's constants** (protocol).
2. S4 (DFT/translation-invariance layer) — largely mechanical once specced; **delegable**.
3. S1 + S2 enter Lean together with S3's skeleton (consumers in place, no-consumer policy
   satisfied); audit rows + vetting records in the same PR.
4. S3 proof: high branch (pure computation from S1 + S4), band branch (Pieces 2–5 + B5b as
   landed), stitching.
5. Piece-5 assembly then converts the B2 axiom to a theorem; clustering axioms 14/15 ride
   the same trace bridge per `cyl-2a-spectral-gap.md`.
