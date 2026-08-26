# pphi2 — per-axiom vetting records

One file per architectural axiom, format per
[`templates/vetting-entry.md`](https://github.com/math-commons/formalization-assurance/blob/main/templates/vetting-entry.md)
in the assurance hub.

## Status (working-tree audit, 2026-08-18)

| Rung | Count | Notes |
|---|---|---|
| Active real axioms in the source tree | **25** | 23 public + 2 private; source-level count, pending remote kernel certificate |
| Vetting records | **historical / unreconciled** | The directory retains records for discharged bridge axioms and the removed fixed-volume spectral-gap pair. |
| Statement hashes populated | **not recomputed** | Required for L3 strictness after the inventory is reconciled. |

The old 26/26 coverage claim is stale. Four former ground-state bridge axioms
are now theorems, and the two fixed-volume spectral-gap axioms were removed.
The directory retains those records for provenance. Reconcile the records
against [`../../formalization.yaml`](../../formalization.yaml) before treating
coverage as complete or raising the assurance policy to L2.
Most are citation-form — they point at the existing vetting evidence in
[`../../docs/gemini_review.md`](../../docs/gemini_review.md) (Feb 2026 group
review), [`../../AXIOM_AUDIT.md`](../../AXIOM_AUDIT.md) (rolling log),
per-axiom discharge plans in [`../../docs/`](../../docs/), and the live status
machine [`../../planning/INDEX.md`](../../planning/INDEX.md).

The detailed records (items 1, 2, 3, 17) capture verbatim verdict summaries
where the vetting was rich enough to quote. The citation-form records assert
the vetting happened, name the source doc, and carry forward the verdict; they
do not reproduce the full verbatim transcript (which lives in the cited doc).

**Strictness ladder.** [`policy.yml`](policy.yml) is at **L1** (warn). Raise to
**L2** only after the historical records are reconciled with the 25-real-axiom
source inventory. Raising to **L3** additionally requires populating
`statement_hash` in each current record.

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

The 25 active real axioms (23 public + 2 private scaffolding) are the current
source-level target population. For the canonical list with file:line locations see
[`../../formalization.yaml`](../../formalization.yaml) and
[`../../planning/INDEX.md`](../../planning/INDEX.md).
