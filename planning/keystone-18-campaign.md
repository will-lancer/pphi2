# Keystone 18 — weak-coupling uniqueness campaign design

**Date**: 2026-07-13. **Target**: `pphi2_limit_unique` (`planning/weak-coupling-uniqueness.md`) —
the coherence keystone closing Gaps A/B/C. **Basis**: declaration-level extraction of the
proved GibbsMeasure `Ch6Subtree/` cluster expansion (`origin/feat/ClusterExpansion`… branch
`origin/feat/Ch6InfVolume`; local branch is STALE and lacks the tree — fetch before any work).
⚠ Never cite/use the sibling `Ch6InfVolume/` tree (vacuous stubs).

## The decisive structural fact

The template splits cleanly (verified by `Fintype Spin` occurrence count per file):

- **Generic KP engine (zero spin dependence — import/mirror verbatim):** `PolymerSystem P`
  (`Cluster/KPBound.lean:28` — activities `W : P → ℝ≥0∞`, symmetric-reflexive `bad`, size
  `a ≥ 0`), `KPCondition` (`:90`), the KP convergence lemmas `kp_rooted_bound` (`:993`),
  `kp_pinned_bound` (`:1035`), `kp_total_bound` (`:1122`), the polymer partition function
  `Xi` + signed `clusterSeries` + `deltaProd` and the **headline generic identity**
  `Xi_eq_exp_clusterSeries` (`Cluster/Expansion.lean:801`, FV Prop 5.3/§5.6), plus all of
  `Graphs/Overlap/Counting/TsumFacts/Geometry`. Requirements on `P`: `[LinearOrder P]` only.
- **Finite-spin ℤ^d instantiation (irreducibly hardwired — REBUILD for P(φ)₂):**
  `polymerWeightBound`/`mayerF`/`spin_sum_factorizes` (`Cluster/PolymerRep.lean:330/141/472`)
  and the high-temp KP verification `kpSystem_condition` (`Cluster/KPVerification.lean:713`,
  FV 6.99) — these need finite normalized spin sums and the sup-norm-finite `Potential.norm`;
  both fail for the unbounded continuous single-site measure.
- **Mechanical ports:** `distanceToBoundary` exhaustion geometry
  (`AppendixProofs/ClusterExpansion.lean:12–160`), the boundary/exhaustion stabilization
  scaffolding (`Cluster/{Ratio,DeltaT}.lean` — structure ports, analytic inputs re-derived as
  Gaussian-integral estimates), and the uniqueness superstructure
  (`Uniqueness/{BoundarySensitivity,ClusterExpansionCriterion}.lean` —
  `boundaryInsensitive_unique` is already Site/Spin-generic; drop `[Fintype Spin]` for
  standard-Borel `Site → ℝ` configs + a Gaussian-integrable DCT dominator).

No extraction/abstraction of the KP core exists anywhere (checked): packaging it standalone
is a greenfield mechanical refactor.

## Campaign stages

| Stage | Content | Class | Est. |
|---|---|---|---|
| **K18-0** | Extract the generic KP core (`KPBound`+`Expansion`+4 support files) into a standalone lib (recommend: new repo `polymer-kp` in random-fields, or a `Polymer/` subtree of GibbsMeasure promoted to a lake lib; owner decision — it serves GibbsMeasure, pphi2, and future stat-mech work) | mechanical refactor, **delegable** | ~1 wk |
| **K18-1** | P(φ)₂ foundations: `Config Site ℝ` with product Borel (NOT compactness instances), single-site measure `e^{−a²:P:}dφ`, interaction "norm" as weighted-`L²`/Gaussian-integral functionals replacing the sup-norm `Potential.norm` | port + new defs, mixed | 1–2 wk |
| **K18-2** | **THE research core**: define the P(φ)₂ polymer activities and verify `KPCondition` at weak coupling via the **small-field / large-field split** (small field: analyticity/Gaussian estimates give convergent Mayer activities; large field: probabilistic suppression from `:P:` stability). No analog exists in the template. GJ Ch. 18 / GJS 1974. Needs its own statement-design + Gemini/Codex vetting cycle BEFORE Lean (crux-class a-power and log-coupling thresholds throughout). **Synergy: shares the single-site Griffiths–Simon/Gaussian analysis with Layer A (A3).** | ★★★ new analysis, Fable-led | 4–8 wk |
| **K18-3** | Boundary/exhaustion port + assembly: `Wterm/WtermInf/deltaT/Einf` structure with Gaussian-integral inputs; then `Xi_eq_exp_clusterSeries` + `boundaryInsensitive_unique` assemble the FIXED-SPACING uniqueness: at weak coupling, the infinite-volume `P(φ)₂` Gibbs/limit measure at lattice spacing `a` is unique with exponential boundary-independence | port + assembly | 2–3 wk |
| **K18-4** | **The coupled-limit step (Gap C proper — NOT in the template):** fixed-`a` uniqueness does not yet collapse pphi2's coupled `(aₖ, Nₖ)` subsequential limits. Route to design (own design pass, before implementation): the expansion's `a`-uniform convergence at weak coupling ⟹ the fixed-`a` infinite-volume Schwinger functions converge as `a → 0` (equicontinuity/analyticity in the expansion parameters) ⟹ all coupled limit points share the same Schwinger functions ⟹ coincide (moment determinacy via the exp-moment bounds). Interacts with `IsPphi2Limit`'s D1-strengthened form. | ★★★ design pass first | 2–4 wk after K18-2/3 |

Total: a genuine multi-month campaign, dominated by K18-2; K18-0/1 can start immediately and
in parallel with everything else in the program.

## Payoff (from `weak-coupling-uniqueness.md`, unchanged)

`pphi2_limit_unique` + the (now-honest, post-4.1) headline ⟹ the conjoined
`pphi2_interacting_qft_exists` — one μ carrying OS ∧ S₂>0 ∧ u₄≠0 at weak coupling — the
statement that actually means "an interacting φ⁴₂ QFT exists, in Lean."

## Immediate next actions

1. Owner: K18-0 home decision (standalone repo vs GibbsMeasure lib target).
2. Dispatchable now: K18-0 (once homed) and K18-1's config/measure foundations.
3. Fable next: K18-2's statement-design pass (the activity definitions + the KP-verification
   statement with the small/large-field thresholds pinned and vetted) — schedule as its own
   arc; do not let implementation start before that vet.
