# Cylinder RP adapter — Phase 2 plan (discharge `hRP` after Phase 1 landed)

**Date**: 2026-07-20. **Status**: Phase 1 DONE (`da8d134`,
`Pphi2/AsymTorus/AsymReflectionPositivity.lean`,
`interactingLatticeMeasureAsym_isReflectionPositive_link`, bare-trio, pushed). This doc scopes
Phase 2, which discharges the cylinder OS3 `hRP` gate in
`cylinderIso_OS_of_RP_OS2` / `routeBPrimeIso_cylinder_OS`
(`Pphi2/AsymTorus/AsymContinuumLimit.lean:650`, `:524`).

## THE ARCHITECTURAL BLOCKER (found 2026-07-20, must be fixed before any discharge)

`hRP` in both theorems is **over-quantified over `μ`**:
```lean
hRP : ∀ (Lt) (hLt) (μ : ∀ n, Measure (Configuration (AsymTorusTestFunction (Lt n) Ls))),
        CylinderMeasureSequenceEventuallyReflectionPositive Ls
          (fun n => cylinderPullbackMeasure (Lt n) Ls (μ n))
```
For an ARBITRARY `μ` this is FALSE (RP is a property of the specific measure), so `hRP` is
**not honestly dischargeable as stated** — supplying it is impossible without the concrete
interacting-measure structure.

Root cause: inside `cylinderIso_OS_of_RP_OS2`, the μ fed to `hRP` is produced by
`asymTorusIso_cylinderUniformGreenBound` (`AsymContinuumLimit.lean:462`), which does
`choose μ hμ_prob hμ_green using hbound` (`:505`). `hbound` (`:482`) comes from
`asymTorusIso_measureHasGreenMomentBound_of_cutoff` (`:490`) and its existential asserts ONLY
`IsProbabilityMeasure μ ∧ MeasureHasGreenMomentBound … μ`. The measure μ is a UV (k→∞) weak limit
of interacting lattice measures — it IS reflection-positive — but that RP is **thrown away** by
the existential, so it cannot be recovered at the `hRP` site.

## THE FIX — thread RP through the Green-bound existential

RP is a weak-limit-closed property (`OS3_RP_Inheritance.rp_closed_under_weak_limit:87`;
`CylinderOS.cylinderMeasureReflectionPositive_of_tendsto_cf:404`). The UV limit that builds μ
already establishes characteristic-functional convergence. So:

1. **Strengthen the existential** `asymTorusIso_measureHasGreenMomentBound_of_cutoff` (and, if
   needed, `MeasureHasGreenMomentBound`'s producer chain) to ALSO carry
   `CylinderMeasureReflectionPositive Ls (cylinderPullbackMeasure (Lt n) Ls μ)` — or the
   sequence-eventual form — for the μ it constructs, proved from:
   - Phase 1 lattice RP `interactingLatticeMeasureAsym_isReflectionPositive_link` for each finite
     even lattice `(Nt_k, Ns_k, a_k)` in the UV sequence, transported to the torus test-function
     pullback; PLUS
   - the no-wrap / time-translation link→cylinder-reflection bridge (Phase 0 report §(d)); PLUS
   - the UV weak-limit RP-closure theorem (matrixwise `…_of_tendsto_cf`, NOT the abstract
     `IsReflectionPositive.weak_limit`, which is too strong — Phase 0 report §Outcome).
2. **Thread it through** `asymTorusIso_cylinderUniformGreenBound`'s existential (add the RP
   conjunct to its `∃ … ∧ …` and to `AsymTorusSequenceHasUniformGreenMomentBound` or a sibling).
3. **Discharge `hRP` internally**: with the RP conjunct now available on the constructed μ,
   `cylinderIso_OS_of_RP_OS2` / `routeBPrimeIso_cylinder_OS` can DROP the `hRP` hypothesis and
   prove it inline (`CylinderMeasureSequenceEventuallyReflectionPositive.of_forall` bridges
   per-index full RP to the eventual form). Downstream callers lose an unprovable obligation.

## Route detail (from Phase 0 report §(d), unchanged)
1. exact finite-lattice RP for no-wrap compact-support positive-time tests (Phase 1 gives the
   lattice RP; restrict to `C_c^∞((0,R)×S¹)` tests with `Lt > 2R` so `embed f` doesn't wrap);
2. one-step time-translation invariance converts the through-bond link reflection `θ_L` to the
   exact cylinder reflection `cylinderTimeReflection`;
3. UV weak-limit via `cylinderMeasureReflectionPositive_of_tendsto_cf`;
4. extend compact-support → full positive-time submodule by density + continuity
   (`periodizeCLM_eq_on_large_period`, `cylinderPositiveTimeSubmodule`).

## Staging
- **2a**: strengthen + thread the existential (interface refactor). Build green; no new axioms.
- **2b**: discharge `hRP` internally in the two headline theorems; drop the hypothesis. Bare-trio
  `#print axioms` on the cylinder OS0/OS2/OS3 headline.
- **Bonus (separate, optional)**: retire `gaussian_rp_cov_perfect_square`
  (`OS3_RP_Lattice.lean:648`) — this is the SQUARE-torus (`ZMod N × ZMod N`) RP axiom, a
  *parallel* application of the generic GJ 6.2.2 theorem, orthogonal to the cylinder discharge.
  Do NOT bundle it into Phase 2.

## 2026-07-20 partial landed (green)

Landed in `Pphi2/IRLimit/CylinderOS.lean`:

- `cylinderPositiveTimeCompactPureTensors`
- `schwartzCutoffCLM_mem_positiveTime`
- `pure_mem_cylinderPositiveTimeSubmodule`
- `cylinderPositiveTimeSubmodule_eq_closure_span_compactPure`

This closes the **density/compact-support** leg of Phase 2a: the full cylinder positive-time
submodule is now the closure of the span of pure tensors whose temporal factors are both
positive-time and compactly supported. That is the exact no-wrap class needed for the finite-`Lt`
adapter (`Lt > 2R`).

What is **still missing** is the UV/link-RP closure theorem that produces RP for the concrete
UV-limit torus measure. The clean statement to target next is:

```lean
theorem asymTorusIso_measureHasGreenMomentBound_of_cutoff_withRP
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (K C : ℝ) (_hK_pos : 0 < K)
    (hcutoff : ...)
    (Nt Ns : ℕ → ℕ) (a : ℕ → ℝ)
    (hNt : ∀ k, NeZero (Nt k)) (hNs : ∀ k, NeZero (Ns k)) (ha : ∀ k, 0 < a k)
    (hvolt : ∀ k, (Nt k : ℝ) * a k = Lt) (hvols : ∀ k, (Ns k : ℝ) * a k = Ls)
    (ha0 : Filter.Tendsto a Filter.atTop (nhds 0)) :
    ∃ (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls))),
      IsProbabilityMeasure μ ∧
      MeasureHasGreenMomentBound Ls mass hmass K C μ ∧
      CylinderMeasureReflectionPositive Ls (cylinderPullbackMeasure Lt Ls μ)
```

Proof obligations inside that theorem:

1. finite-lattice/link RP for the no-wrap compact-support pure tensors;
2. one-step time-translation bridge from link reflection to exact cylinder reflection;
3. UV weak-limit closure that explicitly passes the reflection-operator limit `θ_a → θ`;
4. the new compact-support density theorem above to extend from no-wrap generators to all
   `cylinderPositiveTimeSubmodule`.

## External vet (Gemini 3.1-pro, 2026-07-20)
Confirmed flawless on all three points: (1) strengthen-existential-then-drop-hypothesis is the
correct pattern (can't discard the construction and reprove the property later); (2) RP is closed
under characteristic-functional weak limits (bounded-continuous `exp(iω(g))`, limit of ≥0 reals is
≥0) — **but the closure lemma MUST explicitly pass the reflection-operator limit `θ_a → θ`
(link→continuum, `θ_a f → θ f` uniformly for fixed smooth `f`), not just `μ_a → ν`**; (3) the
`Eventually (∀ᶠ k, Lt k > 2R)` no-wrap predicate is the exact standard formalization, and it
collapses to absolute RP for ν in the `Lt→∞` limit.

## Guards
No new `axiom`/`sorry`/`admit`. If the interface change forces a genuinely new fact, STOP and
report it as a named conjecture. Commit+push per green sub-stage with the
`Co-Authored-By: Claude Fable 5 (1M context)` trailer.
