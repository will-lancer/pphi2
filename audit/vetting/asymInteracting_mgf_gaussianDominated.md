# Vetting — `asymInteracting_mgf_gaussianDominated`

Captured soundness-review records for `asymInteracting_mgf_gaussianDominated`
(`Pphi2/AsymTorus/AsymExpMomentDischarge.lean`). Linked from
[`../../AXIOM_AUDIT.md`](../../AXIOM_AUDIT.md) and
[`../../planning/INDEX.md`](../../planning/INDEX.md) item 2.

---

```yaml
---
axiom: asymInteracting_mgf_gaussianDominated
file: Pphi2/AsymTorus/AsymExpMomentDischarge.lean
statement_hash: null
model: gemini-3.1-pro + codex-gpt-5.5
tool: mcp__gemini__chat_gemini + codex
source_code: GR, SA
date: 2026-07-12
questions: [quantifier-correctness, sign-restriction]
verdict: FALSE-AS-STATED (unrestricted); RESTATED 2026-07-13
rating: Standard (sign-restricted)
discharged: false
superseded_by: null
---
```

**Restatement (2026-07-13).** The 2026-07-12 vet (Gemini 3.1-pro; independently
confirmed by Codex GPT-5.5) found the axiom's quantifier over ALL
`f : AsymLatticeField Nt Ns` FALSE: Newman/Lee–Yang Gaussian domination requires
same-sign coefficients (2-spin mixed-sign counterexample; Lebowitz-κ₄ mechanism;
n-pair amplification defeats the `K = 2` `|·|`-form). The axiom now carries
`hf : ∀ x, 0 ≤ f x` (sitewise nonnegative). **Rating: Flagged → Standard
(sign-restricted).** Signed `f` is recovered by the theorem
`asymInteracting_expMoment_of_signed` (`Pphi2/AsymTorus/AsymSignedSplit.lean`):
`f = f₊ − f₋` split + Cauchy–Schwarz + the axiom at `2f₊`, `2f₋`, giving
`∫ e^{|⟨ω,f⟩|} dμ_int ≤ 2·exp(Var_int(f₊) + Var_int(f₋))`. Full record:
`AXIOM_AUDIT.md` entries 2026-07-12 (flag) and 2026-07-13 (resolution);
`planning/layer-a-lee-yang-scoping.md` §"Vet result".

---

```yaml
---
axiom: asymInteracting_mgf_gaussianDominated
file: Pphi2/AsymTorus/AsymExpMomentDischarge.lean:127
statement_hash: null
model: gemini-3-pro
tool: mcp__gemini__deep_think_gemini
source_code: DT, LP
date: 2026-05-31
questions: [architecture-correctness, factorization, dependencies]
verdict: SATISFIABLE
rating: Likely correct
discharged: false
superseded_by: null
---
```

**Statement form** (informal): the MGF of `⟨ω, f⟩` under the asymmetric-torus
interacting measure is Gaussian-dominated — `MGF(t) ≤ exp(t² · Var(f) / 2)`
(possibly with a constant prefactor, `K = 2`).

**Layer A** of the Layer-C assembly for
`asymInteracting_expMoment_volume_uniform` (item 1). The Newman MGF
Gaussian-domination inequality, instantiated for the asym-lattice
interacting measure.

**Vetting source.**
[`docs/asym-expmoment-discharge-via-lee-yang-vet-request.md`](../../docs/asym-expmoment-discharge-via-lee-yang-vet-request.md)
— a structured deep-think vet of the Layer-A reduction architecture (the
factorization `(LY) := (LY1) + (LY2) + (LY3)` plus the Newman MGF
inequality).

**Verdict summary (2026-05-31):**

Architecture **CONFIRMED** as correct; four recalibrations applied:

1. `IsLeeYang` is **multivariate** with a projection lemma to univariate
   marginals (was univariate + multivariate-as-add-on).
2. `iteratedAsano` lives over `SimpleGraph V` with edge weighting, not
   specialized to rectangular lattices.
3. `evenPolynomialWick` takes an explicit variance parameter (was
   hardcoded unit variance).
4. Pphi2-side adapter scope bumped from ~50-150 lines to **~200-400
   lines** — the global covariance representation does NOT admit a
   one-step disintegration into the site-wise product measure that
   Griffiths-Simon consumes; the adapter needs density-vs-flat-Lebesgue
   rewriting + nearest-neighbour coupling extraction.

The four planned files (`Polynomial/RealZeros.lean`, `Polynomial/Asano.lean`,
`Measure/Newman.lean`, `Measure/GriffithsSimon.lean`) stand; their content
has been refined in [`lee-yang/PLAN.md`](https://github.com/mrdouglasny/lee-yang/blob/main/PLAN.md)
accordingly.

**Conditions / follow-ups:**

- **Discharge depends on the [`lee-yang`](https://github.com/mrdouglasny/lee-yang)
  repo.** Phase 1 polynomial side is **DONE, 0 sorries, 0 axioms** (Asano main
  lemma + iteratedAsano fold, as of 2026-06-02). `Measure/Newman.lean`
  (`IsLeeYang` + projection + Newman MGF inequality, the consumer-facing
  surface for this axiom) is the next deliverable; not started.
- **Re-vet if strengthened**: any change to the `K` constant or the
  variance functional form requires a fresh deep-think pass.

**Cross-references:**

- Live discharge plan: [`../../docs/asym-expmoment-discharge-via-lee-yang-vet-request.md`](../../docs/asym-expmoment-discharge-via-lee-yang-vet-request.md).
- Upstream repo: [`lee-yang`](https://github.com/mrdouglasny/lee-yang) (Phase 1 polynomial side done).
- Downstream: [`asymInteracting_expMoment_volume_uniform.md`](asymInteracting_expMoment_volume_uniform.md) (Layer-C assembly).
- Status: [`../../planning/INDEX.md`](../../planning/INDEX.md) item 2.
