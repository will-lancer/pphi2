# pphi2 — per-axiom vetting records

One file per architectural axiom, format per
[`templates/vetting-entry.md`](https://github.com/math-commons/formalization-assurance/blob/main/templates/vetting-entry.md)
in the assurance hub.

## Status (2026-08-20; source inventory reconciled)

The source inventory was reconciled on 2026-08-20. Declaration-level vetting remains
open. The directory currently carries **19 active records** in the tracked analytic-input
scope. The scope is these records:

1. `schwinger_agreement`
2. `os2_from_phi4`
3. `continuum_exponential_moment_bound`
4. `canonical_continuumMeasure_cf_tendsto`
5. `continuum_exponential_clustering`
6. `continuumLimit_nonGaussian`
7. `latticeGreenBilinear_basis_tendsto_continuum`
8. `pphi2_nontriviality`
9. `nelson_exponential_estimate_master_bounded`
10. `rotation_cf_defect_polylog_bound`
11. `two_point_clustering_from_spectral_gap`
12. `general_clustering_from_spectral_gap`
13. `asymInteracting_expMoment_volume_uniform`
14. `asymInteracting_mgf_gaussianDominated`
15. `asymInteractingVariance_le_freeVariance_lattice_Lt_uniform`
16. `asymTransferGap_uniform_fixedLs`
17. `fss_infrared_quadratic`
18. `groundVariance_le_freeCovariance`
19. `asymFinitePeriodicBridge_uniform_pair` (the paired remainder and diagonal inputs)

`pphi2_limit_exists` has no dedicated vetting record in this directory. The
current source inventory contains 27 declarations, so this record scope does not
claim declaration-level coverage. The directory retains detailed bridge records,
private scaffolding records, and removed or discharged records for provenance.

Statement hashes populated: **0 / 19** in the active scope; hashes are required
for L3 strictness.

Most active records are citation-form. They point at the existing vetting evidence in
[`../../docs/gemini_review.md`](../../docs/gemini_review.md) (Feb 2026 group
review), [`../../AXIOM_AUDIT.md`](../../AXIOM_AUDIT.md) (rolling log),
per-axiom discharge plans in [`../../docs/`](../../docs/), and the live status
machine [`../../planning/INDEX.md`](../../planning/INDEX.md).

The detailed records (items 1, 2, 3, 17) capture verbatim verdict summaries
where the vetting was rich enough to quote. The citation-form records assert
the vetting happened, name the source doc, and carry forward the verdict; they
do not reproduce the full verbatim transcript (which lives in the cited doc).

**Strictness ladder.** [`policy.yml`](policy.yml) is at **L1** (warn). The
project can raise to **L2** (coverage-enforce) once a CI gate reads the active
record scope and the source inventory is reconciled. Raising to **L3**
additionally requires populating `statement_hash` in each active record.

## Where the vetting evidence lives today

Vetting evidence for pphi2's axioms is currently scattered across:

- [`../../AXIOM_AUDIT.md`](../../AXIOM_AUDIT.md) — dated-entries narrative log
  (newest first); records gemini deep-think verdicts, codex cross-checks,
  literature citations, and discharge-plan revisions.
- [`../../planning/INDEX.md`](../../planning/INDEX.md) — per-axiom status,
  difficulty, dependencies, and link to the live discharge plan.
- [`../../docs/`](../../docs/) — per-axiom discharge plans (many gemini-vetted),
  e.g. `B4B5-design.md` for Layer B2, `asym-expmoment-discharge-via-lee-yang-vet-request.md`
  for Layer A, `cyl-1a-bridge-plan.md` for the Layer C assembly, etc.

The vetting records under this directory are intended to **consolidate**
that evidence into one record per axiom (with verbatim model prompts and
replies), in the hub's reproducible format.

## How to add a record

```bash
cp ~/Documents/GitHub/formalization-assurance/templates/vetting-entry.md \
   audit/vetting/<AxiomName>.md
$EDITOR audit/vetting/<AxiomName>.md
# Then add a `vetting:` row to AXIOM_AUDIT.md → Sources column.
```

A vetting record can cite a verbatim model prompt + reply (the strongest
form, used for new or strengthened axioms) **or** point to an existing
literature proof (LP code) **or** a previous deep-think vetting captured
in `AXIOM_AUDIT.md` (DT code with a date pointer). See `VETTING.md` in
the hub for the convention.

## Axiom inventory

The canonical source declaration inventory is the 27-entry list in
[`../../formalization.yaml`](../../formalization.yaml), with current planning
context in [`../../planning/INDEX.md`](../../planning/INDEX.md). The 19 records
above are a maintained vetting scope within that inventory. Private scaffolding,
removed declarations, discharged theorems, and bridge records remain linked for
provenance.
