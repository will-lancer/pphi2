# CYL-2a addendum — volume scaling of the spectral-gap axioms (Phase 3.2 scoping)

**Date**: 2026-07-12. **Refines**: [`cyl-2a-spectral-gap.md`](cyl-2a-spectral-gap.md) (whose
regime caveat is correct in spirit but conflates three different limits). **Read before the
mandated design pass; do not start route-1 formalization until the questions below are pinned.**

## Finding: the axioms live at FIXED `Ns` — a shrinking-volume limit

`spectral_gap_uniform` and `spectral_gap_lower_bound` (`TransferMatrix/SpectralGap.lean:89,100`)
quantify `∀ a ≤ a₀` at **fixed section-variable `Ns`** (spatial sites). So their limit is
`a → 0` with physical spatial size `Ns·a → 0`: the continuum limit of `Ns` coupled anharmonic
oscillators (quantum mechanics), NOT the fixed-`L` field-theory limit and NOT the thermodynamic
limit. Three regimes must be kept apart:

| Regime | Physics | Gap behavior | Regime hypothesis needed? |
|---|---|---|---|
| **(i) fixed `Ns`, `a → 0`** (the axioms as stated) | degenerate dimensional reduction with the WRONG (2D) counterterm hard-coded | **gap CLOSES: `~ (1/a)·e^{−c/a²} → 0`** — see resolution of Q1 below | moot — **axioms FALSE as stated** |
| **(ii) fixed `L = N·a`, `a → 0`** (fixed-volume field theory; the cylinder story at fixed `Ls`) | spatially-cutoff P(φ)₂ Hamiltonian `H(Ls)`; `e^{−tH}` trace class; ground state simple | open at ALL couplings at fixed volume (gap may be tiny but positive) | none for positivity; weak coupling only for *quantitative* `c·mass` bounds |
| **(iii) `N·a → ∞`** (thermodynamic) | infinite-volume mass gap | **closes at criticality** (GJS phase transition) | **weak coupling required** |

## ⚠ Q1 RESOLVED (2026-07-12, hand computation + Gemini 3.1-pro verification): the axioms are FALSE

With the Lean definitions (`latticeEigenvalue = (4/a²)Σᵢsin²(πkᵢ/N) + m²`,
`wickConstant = (a²N²)⁻¹ Σ_k λ_k⁻¹`, `massGap = −(1/a)log(λ₁/λ₀)`):

1. **Zero-mode divergence of the Wick constant at fixed `N`**: the `k = 0` term contributes
   `(a²N²m²)⁻¹` — in the coupled limit `N·a = L` this is the finite `m⁻²/L²` (and the nonzero
   modes give the usual `log` divergence), but at fixed `N` it makes `c_a ~ a⁻²`. The 2D
   counterterm is the *wrong* subtraction for the dimensionally-reduced (QM) limit, which has
   no UV divergence at all.
2. **Consequence for the spectrum** (Gemini-verified mechanism): the Wick-ordered quartic
   on-site term expands as `a²φ⁴ − (6/(N²m²))φ² + O(a⁻²)`; in the transfer Hamiltonian the
   spatial zero mode `y` sees a symmetric double well with minima at `|y| ~ a⁻¹` and barrier
   `~ a⁻³`; the gap is the tunneling splitting, instanton action `~ a⁻²`, so
   `massGap ~ (1/a)·exp(−c/a²) → 0`. This kills the `∃ m₀ > 0` uniformly-in-`a` claim at
   **every** coupling (the leading coefficient of any `InteractionPolynomial` is `1/n > 0`),
   so both `spectral_gap_uniform` AND `spectral_gap_lower_bound` are **false as stated** —
   a stronger and different failure than the criticality caveat.
3. **Mitigation — dead branch (3.1′ trace, 2026-07-12)**: at the proof-term level NOTHING
   consumes these two axioms or the lattice clustering chain (`two_point_clustering_lattice`,
   `general_clustering_lattice`, `clustering_uniform`, `os4_lattice`, `exponential_mixing`
   have zero external references); Main's OS4 comes from the standalone
   `continuum_exponential_clustering` axiom. So the headline kernel trace is uncontaminated —
   consistent with the 2026-06 finding that the gap axioms are dormant. **But false axioms in
   the build are a standing soundness hazard** (any future consumer inherits inconsistency
   potential) and must be removed or restated promptly, independent of campaign scheduling.
4. **Physical-reach mismatch** (3.1′): even if true, a fixed-`Ns` gap could only give decay up
   to physical separation `(Ns/2)·a → 0`; `continuum_exponential_clustering` needs decay out
   to `‖a‖ → ∞`, i.e. regime (iii) along the `Nₙ·aₙ → ∞` sequence of
   `canonical_continuumMeasure_cf_tendsto`. The lattice OS4 chain must be rewired to feed the
   continuum axiom (today it is decorative).

The blanket "false at criticality" caveat in `cyl-2a-spectral-gap.md` (and echoed in the
completion plan's 3.1) was aimed at regime (iii); the axioms as literally stated fail earlier
and for a different reason (wrong-counterterm shrinking box).

## Consequences for statement design (do this before any proof work)

1. **Pin the consumer's regime first.** Trace which volume scaling
   `two_point_clustering_from_spectral_gap` / `general_clustering_from_spectral_gap` / the OS4
   inheritance chain actually use: if `continuum_exponential_clustering` needs the gap along the
   coupled `Nₙ·aₙ → ∞` sequence (it does — ℝ² OS4 is thermodynamic), then the *fixed-`Ns`*
   axioms are **too weak for the ℝ² headline** regardless of their truth, and the honest
   restatement is a split:
   - **17a (fixed spatial size)**: `a`-uniform gap at fixed `Ls` (regime (ii)) — no coupling
     hypothesis; this is the cylinder (M4) input and matches the expert-vetted
     compact-resolvent story (`reflection-positivity/docs/B2_UNIFORMITY_QUESTION.md`,
     `T_a → e^{−aH(Ls)}`, Simon Ch. VI).
   - **17b (volume-uniform)**: gap uniform in `Ls` — weak-coupling hypothesis mandatory
     (FSS infrared bound / cluster expansion; `docs/fss-infrared-bound-spec.md` is the parked
     tool). Only 17b needs the D3 regime threading; 17a does not.
2. **Q1 (design-pass question, crux-2 error class — do NOT hand-wave):** at fixed `Ns`, `a → 0`,
   what does the Wick constant `c_a = G_a(0,0)` do? The 2D `log(1/a)` divergence is a
   joint-limit phenomenon; at fixed `Ns` the spatial modes are finitely many and `a`-scaled —
   whether `c_a` converges (honest QM limit, zero-mode potential stable, gap open) or diverges
   (zero-mode double-well deepens, tunneling gap → 0, axiom (i) FALSE as stated) depends
   exactly on the `a`-weights in `latticeCovarianceGJ` at fixed `Ns`. This single computation
   decides whether the axioms-as-stated are true-but-useless (if consumers need (ii)/(iii)) or
   false. Assign to the Gemini/Codex design pass with the explicit GJ normalization in hand.
3. **`spectral_gap_lower_bound` (16)**: its constant `c` may depend on `(Ns, P, mass)` as
   quantified, which at fixed `Ns` makes it nearly a corollary of 17. Its *intended* strength
   (`c` independent of volume, `m_phys ≥ c·mass`) is a regime-(iii) statement at weak coupling.
   Same split recommendation: fold the fixed-volume version into 17a; state the quantitative
   version only under `IsWeakCoupling`.
4. **Square vs asym**: the proved finite-`a` gap machinery (`asymGappedTransfer'`,
   `AsymJentzsch`) is on the asym lattice; 16/17 are on the square (`FinLatticeField 2 Ns`).
   The restatement PR should decide the canonical home (recommend: asym, where the cylinder
   campaign lives, with a square corollary if the OS4 files stay square).

## Revised sequencing for Phase 3 (supersedes 3.1/3.2 bullets in the completion plan)

1. **3.1′** Consumer-regime trace (question 1) — half a day, read-only.
2. **3.2′** Design pass on Q1 (Wick-constant scaling at fixed `Ns`) + the (ii)-regime
   eigenvalue-convergence argument (`m_phys(a) = −log(λ₁/λ₀)/a → E₁ − E₀ > 0`) — Gemini +
   Codex, with the explicit `a`-power audit that the B2 plans mandate for this error class.
3. **3.3′** Restate 16/17 as 17a/17b per the split above (17b under `IsWeakCoupling`,
   coordinated with D3 of `r2-honest-headline-spec.md`); update INDEX rows + audit.
4. **3.4′** Formalize 17a via compact-resolvent convergence (the genuinely new ~3–6 wk
   campaign); 17b joins the keystone-18 / FSS track.
