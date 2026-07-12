# ℝ² honest headline — decision spec (Phase 4.1 of completion-plan-2026-07)

**Date**: 2026-07-12. **Status**: design complete, implementation not started.
**Builds on**: [`ispphi2limit-strengthening-scope.md`](ispphi2limit-strengthening-scope.md) (the
δ₀-exclusion mechanics + blast radius — authoritative for the edit list) and
[`weak-coupling-uniqueness.md`](weak-coupling-uniqueness.md) (keystone 18). This spec makes the
four decisions those docs left open and pins the statements. Gate: **no further ℝ²-specific
analytic work should land before this does** (else effort accrues to the δ₀-satisfiable target).

## Decisions

### D1 — Strengthen `IsPphi2Limit` via minimal-append (adopt the scope doc as-is)
The appended conjunct forces `ν k = continuumMeasure 2 (N k) P (a k) mass …` with
`N k → ∞`, `N k · a k → ∞` (UV *and* IR coupled). Twin-edit `IsPphi2ContinuumLimit`
(`Bridge.lean:110`) identically so `toIsPphi2Limit := h` still typechecks. Blast radius as
mapped: 3 destructure touch-ups, producers 1–4 break (intended).

### D2 — `pphi2_limit_exists` becomes ONE clearly-labeled textbook axiom (option (a))
The δ₀ proof dies by D1. Replace with:
```lean
/-- Existence of the infinite-volume P(φ)₂ continuum limit (OPEN in this repo).
    Reference: Guerra–Rosen–Simon (Ann. Math. 101, 1975) §II–IV (monotone/GKS infinite-volume
    limit of Schwinger functions, all couplings); Glimm–Jaffe Ch. 11; Simon *P(φ)₂* §II.
    Strategy: the repo's own route is Route B′/A — cylinder IR limit (Lt→∞) then Ls→∞ per
    docs/cylinder-master-plan.md; keystone 18's cluster expansion gives it with uniqueness at
    weak coupling. Until then this is the single existence input for the ℝ² headline. -/
axiom pphi2_limit_exists (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    ∃ (μ : Measure (Configuration (ContinuumTestFunction 2))),
      IsProbabilityMeasure μ ∧ IsPphi2Limit μ P mass
```
Rationale: existence (unlike gap/uniqueness) is literature-true at ALL couplings (GRS), so a
Standard-rated textbook axiom is admissible under the project's axiom rules; the alternative
(headline in conditional `∀ μ, IsPphi2Limit μ → …` form only) hides the existence debt instead
of labeling it. The conditional form already exists as `continuumLimit_satisfies_fullOS` and
stays. **Kernel footprint of `pphi2_existence` grows 4 → 5 axioms — that is the honest count.**
Add the axiom to `AXIOM_AUDIT.md` + `planning/INDEX.md` (new row; Rating: Standard, Sources: LP)
and vet the statement per the axiom protocol before commit.

### D3 — Regime-restrict the false-at-criticality axioms NOW; defer conjoining to keystone 18
Split the refactor that `weak-coupling-uniqueness.md` ("do WITH the discharge") bundles:
- **Now (soundness fix, this PR or its sibling):** add
  `(coupling : ℝ) (hP4 : isPhi4 P coupling) (hweak : IsWeakCoupling P mass coupling)` to
  `spectral_gap_uniform` (`TransferMatrix/SpectralGap.lean:89`), `spectral_gap_lower_bound`
  (`:100`), and `continuumLimit_nonGaussian` (`ContinuumLimit/Convergence.lean:256`), cascading
  through `two_point_clustering_from_spectral_gap` / `general_clustering_from_spectral_gap` /
  `os4_*` into `pphi2_exists`/`pphi2_existence`. These axioms are **false as stated** at
  criticality (φ⁴₂ phase transition; `cyl-2a-spectral-gap.md:37–46`) — an unsound axiom base is
  not acceptable to defer, independent of proof gain. ⚠ This overrides the "gate on keystone"
  note in `weak-coupling-uniqueness.md` §refactor — flagged for owner review; the *conjoining*
  half of that section stays gated.
- **Later (with keystone 18):** `pphi2_limit_unique` + the conjoined
  `pphi2_interacting_qft_exists` exactly as drafted there.
- Note `IsWeakCoupling`'s body (`Bridge.lean:178`, `coupling < mass²/4`) is a stand-in for the
  GJS convergence radius; acceptable for now, revisit at keystone discharge. `isPhi4`
  (`Bridge.lean:92`) is honest (`P.n = 4 ∧ 0 < coupling`) but does not pin the quartic
  coefficient — tightening it is part of the keystone PR, not this one.

### D4 — Reparametrization theorems: demote, don't fake
`mass_reparametrization_invariance` (`Main.lean:270`, currently `:= h_limit` — a vacuity
artifact) breaks under D1. Do NOT attempt the real lattice reparametrization lemma in this PR
(the shifted-measure equality is plausible but is its own bounded project). Demote both
`mass_reparametrization_invariance` and `mass_reparametrization_exists` to a `docs/`-recorded
conjecture (delete the declarations; keep the statement + strategy in `docs/plan.md` or a new
consistency-checks doc, per README's "Consistency checks" section). Nothing downstream consumes
them (verify with `lean_references` before deleting; expected: none).

### D5 — Headline text
Keep the name `pphi2_existence`; after D1+D2 it is meaningful (μ is forced to be an actual
coupled-limit of the interacting lattice family). Rewrite its docstring to state explicitly:
existence input = `pphi2_limit_exists` (GRS axiom), OS properties = the 4 inheritance axioms,
and interaction/nondegeneracy live in separate statements pending keystone 18 (link
`coherence-analysis.md`). Restate `pphi2_nontriviality` (`Main.lean:128`) in the
about-the-limit form (`IsPphi2Limit μ P mass → ∀ f ≠ 0, 0 < S₂(f,f)`) per the scope doc §net
effect — with D1 it stops being free-field-satisfiable-by-δ₀ and becomes a true statement about
the real limit; keep it an axiom (Rating: Standard — GRS two-point lower bound) or discharge
from FKG/Gaussian domination if cheap.

## Edit order (one PR, ~1–2 active days, mostly mechanical after the decisions)
1. D1 def + twin def; fix the 3 destructures (`CharacteristicFunctional.lean:365`,
   `OS2_WardIdentity.lean:406`, `:770`).
2. D2 axiom replaces the δ₀ proof of `pphi2_limit_exists` (Convergence.lean:282); Gemini-vet the
   axiom statement (protocol), add audit rows.
3. D4 deletions (after `lean_references` check).
4. D3 signature threading (single mechanical cascade; new `coupling` binder enters
   `pphi2_exists`/`pphi2_existence` signatures — callers are the audit generator + docs only).
5. D5 docstrings + `pphi2_nontriviality` restatement.
6. `audit/axiom_report.lean` regen, `count_axioms.sh`, status.md/README counts, INDEX.md rows
   (axiom 7 `canonical_continuumMeasure_cf_tendsto` note: with D1's forward-direction conjunct
   in place, re-examine whether its blocked converse form can be restated forward and
   discharged — the scope doc suggests the strengthened predicate carries exactly the CF
   convergence data it needs; if so, that closes the needs-human flag).

## Interaction with in-flight work
- The T² conjoined theorem (branch `t2-conjoined-os`, Phase 0.1) delivers the scope doc's
  "state the honest existence on T²" recommendation; this spec is the ℝ² statement-hygiene
  complement. No file overlap except `Main.lean` docstrings — sequence after 0.1 merges.
- The D2 axiom is exactly what the cylinder campaign (M2–M4) + keystone 18 will eventually
  discharge; its docstring should say so (single source: `docs/cylinder-master-plan.md`).
