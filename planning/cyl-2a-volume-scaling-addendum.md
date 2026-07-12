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

| Regime | Physics | Gap at strong coupling | Regime hypothesis needed? |
|---|---|---|---|
| **(i) fixed `Ns`, `a → 0`** (the axioms as stated) | QM limit of `Ns` oscillators | plausibly open at ALL couplings (discrete spectrum + Perron–Frobenius simple ground state) — see Q1 | plausibly **none** |
| **(ii) fixed `L = N·a`, `a → 0`** (fixed-volume field theory; the cylinder story at fixed `Ls`) | spatially-cutoff P(φ)₂ Hamiltonian `H(Ls)`; `e^{−tH}` trace class; ground state simple | open at ALL couplings at fixed volume (gap may be tiny but positive) | none for positivity; weak coupling only for *quantitative* `c·mass` bounds |
| **(iii) `Ls → ∞`** (thermodynamic) | infinite-volume mass gap | **closes at criticality** (GJS phase transition) | **weak coupling required** |

The blanket "false at criticality" caveat in `cyl-2a-spectral-gap.md` (and echoed in the
completion plan's 3.1) applies to regime (iii) — and to any use where the constants must be
`Ns`- or `Ls`-uniform. It does **not** obviously apply to the axioms as literally stated.

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
