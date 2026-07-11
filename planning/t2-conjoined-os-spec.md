# T² conjoined OS + interaction — implementation spec (Phase 0.1)

**Branch**: `t2-conjoined-os`. **Goal** (completion-plan 0.1): one theorem
`∃ g₀ ∈ (0,1], ∃ μ, IsProbabilityMeasure μ ∧ SatisfiesTorusOS L μ ∧ TorusIsInteractingStrict L μ`
with kernel-only axiom footprint.

## Why the `g•P` route is dead (do not revisit)

`InteractionPolynomial` hard-codes the leading coefficient to `1/n` (`Pphi2/Polynomial.lean:26-38`),
so `g·P` is not representable; that is exactly why `interactingLatticeMeasureCoupling`
(`InteractingMeasure/CouplingMeasure.lean:32`) exists as a separate `withDensity exp(−g·V)` family.
The conjoined theorem therefore needs an **OS bundle for the coupling family**.

## Key structural fact (audited 2026-07-12)

The entire OS bundle `torusInteracting_satisfies_OS` (`TorusInteractingOS.lean:2822`) depends on
the measure family through exactly **four per-cutoff facts**; everything else is generic in
`(μ, φ, hconv)`:

| # | Fact (g = 1 name) | Location | Used by |
|---|---|---|---|
| F1 | per-N exp-moment bound `torusInteractingMeasure_exponentialMomentBound_cutoff` | `TorusInteractingOS.lean:2133` | OS0, OS1 (via the limit exp-moment bound `:2312`) |
| F2 | per-N CF translation invariance `torusInteractingMeasure_gf_latticeTranslation_invariant` | `:364` | OS2 translation (via `torusInteractingLimit_translation_invariant :1611`) |
| F3 | per-N CF swap invariance `torusInteractingMeasure_gf_swap_invariant` | `:1785` | OS2 D4 |
| F4 | per-N CF time-reflection invariance `torusInteractingMeasure_gf_timeReflection_invariant` | `:1953` | OS2 D4 |

Note the `_hconv`/`_φ` underscore arguments of `torusInteracting_os0/os1` (`:2502`, `:2623`) —
they are consumed **only** to invoke the limit exp-moment bound. OS0/OS1 are theorems about any
`μ` with the limit bound.

## Architecture (three layers, all inside/next to `TorusInteractingOS.lean`)

### Layer 1 — family-generic OS kernel (new `section FamilyOS` appended to TorusInteractingOS.lean)

Generic in `ν : ℕ → Measure (Configuration (TorusTestFunction L))` (probability measures),
`φ : ℕ → ℕ` (cutoff index: `ν n` lives at cutoff `N = φ n + 1`), limit `μ`, and
`hconv : ∀ g, Continuous g → bounded g → Tendsto (fun n => ∫ g ∂(ν n)) atTop (nhds (∫ g ∂μ))`.

1. `torusFamily_exponentialMomentBound` — hypotheses `hexp` (F1-shape: `∃ C > 0, ∀ f n,`
   `Integrable (exp|ω f|) (ν n) ∧ ∫ exp|ω f| ∂(ν n) ≤ C · exp(torusEmbeddedTwoPoint L (φ n+1) mass hmass f f)`)
   + `hconv`; conclusion = the limit bound
   `∃ K > 0, ∀ f, Integrable (exp|ω f|) μ ∧ ∫ exp|ω f| ∂μ ≤ K · exp(torusContinuumGreen L mass hmass f f)`.
   **Proof**: verbatim adaptation of `:2312–2449` (truncation + `hconv` + `torus_propagator_convergence`
   + MCT); replace `hK_bound f (φ n + 1)` by `hexp f n`.
   ⚠ Quantifier hygiene: `C` in `hexp` must be bound **before** `(f, n)` — same shape as the g=1
   cutoff bound, which has `C` before `(f, N)`. Do not weaken to `∀ f n, ∃ C`.
2. `torusOS0_of_expMomentBound (μ) (hK : <limit bound>) : TorusOS0_Analyticity L μ` — body =
   `:2502–2606` with `torusInteracting_exponentialMomentBound … ` replaced by `hK`.
3. `torusOS1_of_expMomentBound` — body = `:2623–…` likewise.
4. `torusFamilyOS2_translation (ν φ hconv) (htrans : ∀ n …, <F2 for ν n>) :
   TorusOS2_TranslationInvariance L μ` — genericize `torusInteractingLimit_translation_invariant`
   (`:1611`) + `:2713`.
5. `torusFamilyOS2_D4 (ν φ hconv) (hswap : F3 for ν) (hrefl : F4 for ν)` — body = `:2737–2813`
   with the two per-n invariance inputs as hypotheses.
6. `torusFamily_satisfies_OS` — bundle 1–5, mirroring `:2822`.

The existing g=1 theorems stay untouched for now (golfing them to delegate to the generic kernel
is a later mechanical task).

Location constraint: this must live **in** `TorusInteractingOS.lean` (or de-privatize helpers):
the OS0/OS2 proof bodies use `private` lemmas (`compact_im_bound :2449`, `exp_mul_sum_le :2459`,
`cosEval_* / sinEval_* :1574–1586`, `gf_re_eq_cos_integral / gf_im_eq_sin_integral :1592–1600`).

### Layer 2 — coupling-family instances of F1–F4

1. **F1-coupling**: `torusInteractingMeasureCoupling_exponentialMomentBound_cutoff`
   (hypotheses `0 ≤ g`, `g ≤ 1`). Port of `:2133–2302` with the brick map:
   | g = 1 | coupling |
   |---|---|
   | `nelson_exponential_estimate` | `nelson_exponential_estimate_coupling` (`TorusCouplingLimit.lean:98`) |
   | `boltzmannWeight`, bound `exp B` | `fun ω => exp(−(g·V ω))`, bound `exp(g·B)` (needs `0 ≤ g`; cf. `expNegCoupling_integrable`, `CouplingMeasure.lean:41`) |
   | `partitionFunction_pos` / `_ge_one` | `partitionFn_pos_of_nonneg` / `partitionFn_ge_one` |
   | `density_transfer_bound` | `density_transfer_bound_coupling` (`CouplingMeasure.lean:149`; note: takes `hK` directly, no `hZ_ge_one` arg) |
   | `unfold interactingLatticeMeasure` | `unfold interactingLatticeMeasureCoupling` |
   | measurability `(V).neg.exp` | `((V).const_mul g).neg.exp` |
   Constants unchanged: `C = √(2K)` with `K` the g=1 Nelson constant (Jensen transfer inside
   `nelson_exponential_estimate_coupling`). `gaussian_exp_abs_moment` (`:2003`) and
   `torusEmbeddedTwoPoint_eq_lattice_second_moment` are family-agnostic — reuse.
2. **F2/F3/F4-coupling**: preferred route — extract the invariant-weight core of
   `interactingLatticeMeasure_symmetry_invariant` (`:131–318`) into
   `latticeWithDensity_symmetry_invariant` parameterized by a measurable weight
   `W : Configuration (FinLatticeField 2 N) → ℝ` with `W (ω.comp L_σ) = W ω` and the measure
   `Z⁻¹ • μ_GFF.withDensity (ofReal (exp (−W)))` (`Z > 0`); steps 2–5 of the existing proof are
   already weight-agnostic (step `hBW_config` is the only place `V` enters, via the site-relabel
   sum `Fintype.sum_equiv`; for `W = g·V` multiply that identity by `g`). Same for the
   translation core (`interactingLatticeMeasure_translation_invariant :319`). Then:
   - re-derive the three g=1 wrappers (optional golf), and
   - derive the coupling wrappers `torusInteractingMeasureCoupling_gf_{latticeTranslation,swap,timeReflection}_invariant`
     mirroring `:364 / :1785 / :1953` (the `finiteLaplacian_*_commute` / `massOperator_*_commute`
     private lemmas are weight-independent — reuse as-is).
   Fallback route (if extraction fights): clone the three lemmas for the coupling measure verbatim
   with `bw := exp(−g·V)`.
3. `torusCouplingInteracting_satisfies_OS (hg0 : 0 ≤ g) (hg1 : g ≤ 1) … hconv : SatisfiesTorusOS L μ`
   = Layer 1 bundle applied to `ν n := torusInteractingMeasureCoupling L (φ n + 1) P mass hmass g`
   with F1–F4-coupling.

### Layer 3 — conjoined headline (new file `Pphi2/TorusContinuumLimit/TorusAssembly.lean`)

```lean
theorem torus_pphi2_interactingTheory_weakCoupling
    (P : InteractionPolynomial) (hP : P.n = 4) (mass : ℝ) (hmass : 0 < mass) :
    ∃ (g₀ : ℝ), 0 < g₀ ∧ g₀ ≤ 1 ∧
      ∃ (μ : Measure (Configuration (TorusTestFunction L))) (_ : IsProbabilityMeasure μ),
        SatisfiesTorusOS L μ ∧ TorusIsInteractingStrict L μ
```

Proof: `torus_pphi2_isInteractingStrict_weakCoupling` (`TorusCouplingResult.lean:166`) already
returns `(g₀, μ, φ, hφ, hconv, TorusIsInteractingStrict)` where `hconv` is **exactly** the
bounded-continuous convergence the coupling OS bundle needs; feed it Layer 2.3 with
`hg0 := hg₀pos.le, hg1 := hg₀le1`. Then upgrade `TorusInteractingTheoryExists`
(`TorusNontriviality.lean:137`) to include OS, or add a new bundled `def` and prove it.
Import `TorusAssembly` from `Pphi2.lean` (this also completes plan item 0.2 for these files —
also add `TorusCouplingLimit`/`TorusCouplingResult` imports).

## Follow-ups after landing (from completion plan)

- Add the conjoined headline + coupling OS bundle to `audit/axiom_report.lean` (item 0.3).
- Golf the g=1 OS theorems to delegate to the Layer-1 kernel (mechanical, delegable).
- README/status.md updates in the same PR.

## Delegation markers

Layer 1 statements + Layer 2.1 constants + Layer 3: **Fable** (quantifier hygiene, constants).
Layer 1 proof-body adaptations and Layer 2.2 extraction/clone: **mechanical, delegable** —
the templates are named line ranges above; the compiler is the safety net. Any `sorry` left on
the branch must be one of the F1–F4 stubs with a `-- PORT TEMPLATE: <name>:<lines>` comment.
