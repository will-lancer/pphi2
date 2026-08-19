# Axiom Status Snapshot — superseded

> ⚠️ **This file is superseded as of 2026-06-21.** The master per-axiom status
> machine is [`../planning/INDEX.md`](../planning/INDEX.md). The historical log
> of audit passes and discharges is [`../AXIOM_AUDIT.md`](../AXIOM_AUDIT.md).
> Live source counts come from `./scripts/count_axioms.sh`.
>
> This file used to be a consolidated snapshot. It accumulated drift faster
> than it could be refreshed and now serves only as a pointer.

## At a glance (refreshed 2026-08-19)

| Count | Value | Source |
|---|---|---|
| pphi2 axiom declarations | **27** | `count_axioms.sh` excludes docstring mentions |
| pphi2 sorries | **0** | `count_axioms.sh` |
| gaussian-field axioms | **2** | `count_axioms.sh` at the pinned `d63a285` |
| gaussian-field sorries | **0** | `count_axioms.sh` |

Net change since 2026-06-21: `spectral_gap_uniform`/`spectral_gap_lower_bound` removed
(false as stated), and cylinder-era + Phase-4.1 axioms added (the B2 route-(a) S1/S2/τ-bridge
pair, and `pphi2_limit_exists`). The authoritative live inventory is `AXIOM_AUDIT.md`;
this snapshot is a pointer only.

The superseded-chain `torus_weakCoupling_lattice_connectedFourPoint_strictNeg` axiom and
its sole consumer `torus_pphi2_isInteracting_weakCoupling` (carrier file
`Pphi2/TorusContinuumLimit/TorusInteractingResult.lean`) were **removed on 2026-06-21**
after Route A's `torus_pphi2_isInteractingStrict_weakCoupling` (PR #48, 2026-06-07)
subsumed them.

The counter requires a declaration name and binder or type delimiter, so prose
inside docstrings is excluded.

## Where to look

- **Live status of each axiom**: [`../planning/INDEX.md`](../planning/INDEX.md).
- **History (what discharged when)**: [`../AXIOM_AUDIT.md`](../AXIOM_AUDIT.md).
- **Branch map** (which branch is live for which axiom):
  [`../BRANCHES.md`](../BRANCHES.md).
- **Coherence analysis** (the architectural gap A/B/C and keystone 18):
  [`../planning/coherence-analysis.md`](../planning/coherence-analysis.md).
