# K18-2 design draft — P(φ)₂ polymer activities + KP verification (stage 1: pre-vet)

**Date**: 2026-07-13. **Status**: **VETTED (Gemini 3.1-pro, same day) — design FINAL with
the corrections in the "Vet outcome" section below.** Implementable after K18-0/K18-1.
**Parent**: [`keystone-18-campaign.md`](keystone-18-campaign.md). Consumes the generic
`PolymerSystem`/KP engine (GibbsMeasure `Ch6Subtree`, to be extracted per K18-0).

## The architectural decision the campaign doc glossed (Q1 — decide first)

The GibbsMeasure template's Mayer expansion is a HIGH-TEMPERATURE expansion (weights =
Mayer factors of the *pair interaction*, smallness = β). P(φ)₂'s weak-coupling regime is
different: the Gaussian nearest-neighbor coupling is NOT small (it is the fixed `−Δ_a`
kinetic term); smallness lives in the interaction coupling `λ`. The classical resolutions:

- **(A) GJS/GJ-Ch.18 covariance interpolation**: decouple the *Gaussian covariance* across
  polymer boundaries with interpolation parameters `s`; activities carry `∂_s`-derivatives
  = covariance-contracted functional derivatives acting on `e^{−λV}`; convergence from
  per-derivative smallness (each `∂_s` brings a covariance line with mass-gap decay ×
  Wick/Nelson-bounded vertex factors ~ λ-powers).
- **(B) BKAR/Brydges–Kennedy forest formula**: the modern packaging of (A) — the forest
  interpolation formula gives directly a sum over forests of covariance lines connecting
  unit blocks, with positivity-preserving interpolated covariances; activities = explicit
  Gaussian integrals over forest-connected block families. Cleaner combinatorics, standard
  in the modern constructive literature, and maps ONTO the generic `PolymerSystem`
  interface naturally (polymer = forest-connected block family; `bad` = block overlap).
- **(C) hopping/coupling expansion**: expand the kinetic coupling itself — WRONG regime
  (needs small hopping), rejected.

**Draft decision: (B) BKAR at unit physical scale.** Polymers `γ` = connected finite unions
of closed unit squares of the physical lattice partition (each unit square contains ~1/a²
sites; unit scale is what makes all constants a-uniform and lets pphi2's existing per-block
Nelson machinery plug in directly).

## Draft activity definition (Q2/Q3)

For a finite box `Λ` (union of unit squares) with the free massive Gaussian `μ_C` and
interaction `V_B = λ·a²Σ_{x∈B}:P(φ_x):_{c_a}` per unit block `B`:

- BKAR: `Z_Λ/Z_Λ^{free-factorized} = Σ_{forests F on blocks} ∫dS_F ∂_F [∏_B e^{−V_B}]`
  evaluated at interpolated covariance `C(S_F)`; resumming forests by their connected
  supports gives the polymer representation `Z = Ξ(activities)` with
  `K(γ) = Σ_{spanning forests F of γ} ∫ dS_F E_{C(S_F)}[∂_F ∏_{B⊆γ} e^{−V_B}]`.
- **Dominating activity for KP**: `W(γ) := (C_0·ε(λ))^{|γ|}` target shape, `|γ|` = block
  count, via per-line and per-block bounds:
  - each covariance line: `‖C(x,y)‖`-weighted with the mass-gap decay `e^{−m·dist}` summed
    over line endpoints in the blocks (a-uniform: the UNIT-block-summed lattice covariance
    bounds are exactly pphi2's Cluster-B machinery);
  - each block: the **small/large-field split** — `χ_small = {sup_B |φ| ≤ M(λ)}` with
    `M(λ) ~ |log λ|^{1/2}`-scale: on small field, `|∂^k e^{−V_B}| ≤ poly(M)·λ^{k'}`-type
    analytic estimates (the λ-smallness source); on large field,
    `E[χ_large·(…)] ≤ e^{−c·M(λ)²}`-suppression from the Gaussian measure + the `:P:`
    lower bound `V_B ≥ −c'λ·(Wick constants)` (the stability input — pphi2's
    `wickPolynomial_uniform_bounded_below` family).
- KP size function `a(γ) := |γ|`; `KPCondition` reduces to
  `Σ_{γ ∋ B₀} W(γ)e^{|γ|} ≤ 1`-type row sums = `Σ_n (connectivity count n) ·(C₀·ε(λ)·e)^n`,
  closing for `λ ≤ λ₀` via the standard connected-subset counting (the template's generic
  `Counting.lean` should cover the combinatorics).

## Vet questions (stage 2 — send to Gemini + Codex)

1. Is (B) BKAR-at-unit-scale the right architecture for a LEAN formalization (vs (A))?
   Specifically: is there a formulation of the BKAR forest formula whose Lean cost is
   bounded (finite-dimensional Gaussians, finitely many blocks — the formula is a finite
   algebraic identity per Λ!), and does the interpolated covariance positivity
   (needed for the Gaussian measures `μ_{C(S)}` to exist) have a clean finite-dim proof?
2. The small-field threshold `M(λ)`: pin the standard choice (`|log λ|^{1/2}`? `λ^{−δ}`?)
   and the resulting `ε(λ)` decay in the dominating activity; which precise per-block
   estimate does the large-field suppression need beyond `:P:`-stability + Gaussian tails
   (pphi2 has: Nelson per-block, Wick lower bounds, exp-moments)?
3. a-uniformity audit: which of the per-line/per-block constants are genuinely a-uniform
   at unit scale, and where does the Wick log-divergence `c_a ~ log(1/a)` enter (through
   `M(λ)` vs the stability constant) — does the standard GJS treatment keep the KP radius
   `λ₀` a-uniform (it must, for K18-4)?
4. Derivative bookkeeping: BKAR's `∂_F` produces `∏` of `φ`-polynomials × `e^{−V}` — the
   Lean-friendliest bound (Wick/hypercontractive vs integration-by-parts)?
5. Boundary conditions: the template's `deltaT/Einf` layer stabilizes boundary terms; for
   the BKAR version, what is the finite-vs-infinite-volume comparison object (activities
   independent of Λ once `γ ⊂⊂ Λ`? — should hold by locality of `K(γ)`), and is the
   exponential boundary-independence then免 the same as the template's route?

## Not in scope for K18-2 (recorded to prevent creep)
Uniqueness assembly (K18-3), the coupled `a→0` step (K18-4), the KP-core extraction (K18-0).

## Vet outcome (stage 2, 2026-07-13) — MAJOR SIMPLIFICATION, design final

1. **Architecture confirmed**: Abdesselam–Rivasseau (1995) BKAR form — in finite dimensions
   it is a finite ALGEBRAIC identity (multivariate Taylor/forest formula), no functional
   calculus; PSD of the interpolated covariance is elementary (`C(s) = C ∘ S` Schur/Hadamard
   product of PSD matrices). Unit-scale blocks confirmed.
2. **NO small/large-field split needed** (Q2/Q3 merged): pointwise sup-cutoffs would inject
   `a`-dependence (sup over 1/a² sites diverges logarithmically) — instead:
   - exponential part: Hölder + **Nelson's per-block exponential bound** (pphi2's existing
     NelsonEstimate machinery!) — `E[e^{−qV_B}]` a-uniform for `qλ` small; the Wick
     `(log 1/a)`-lower-bound divergence is neutralized by measure concentration;
   - polynomial part: `∂_F`-factors bounded via Hölder + Gaussian **Wick moments**.
   **λ₀ is genuinely a-uniform.** The K18-2 "research core" therefore collapses to
   assembling EXISTING pphi2 bricks (Nelson per-block, Wick moments/hypercontractivity,
   Cluster-B covariance sums) into the AR framework.
3. **⚠ Coordinator correction to the vet** (adjacent blocks): the claim "forest lines
   evaluate at distance ≥ 1, so no log" fails for ADJACENT unit blocks (sites near the
   shared edge see the 2D `log|x−y|` singularity). The a-uniform bound for adjacent-block
   lines is the INTEGRATED form `a⁴·Σ_{x∈B}Σ_{y∈B'}|C(x,y)|^k ≤ C_k` (2D log is locally
   integrable — this is precisely pphi2's Phase-B/Cluster-B `canonicalRoughCovariance_pow_sum`
   estimate class), NOT a sup bound. Statement design must use block-pair line weights in
   integrated form throughout.
4. **Derivative bookkeeping**: option (a) — algebraic Wick expansion + hypercontractivity.
   (b) IBP rejected (combinatorial explosion in Lean); (c) BBK tree-graph positivity rejected
   (needs pointwise-positive interaction; Wick-ordered `:P:` is not).
5. **Boundary independence**: activities are Λ-independent by construction (BKAR decouples
   blocks); finite-vs-infinite-volume comparison = the KP cluster tail over polymers meeting
   both the observable support and `∂Λ`, on the **a-independent unit-block grid** — the
   lattice boundary (1/a sites) is invisible to the KP layer. The template's `deltaT/Einf`
   scaffolding is thus optional; the direct tail route is preferred.

**Revised effort**: K18-2 drops from ★★★/4–8 wk to **★★–★★★ / 2–4 wk** (the split is gone;
the new content is the AR identity + the activity assembly). Updated in
`keystone-18-campaign.md`.
