# Layer A (Lee–Yang / Newman MGF domination) — campaign scoping (Phase 2b.1)

**Date**: 2026-07-12. **Target axiom**: `asymInteracting_mgf_gaussianDominated`
(`Pphi2/AsymTorus/AsymExpMomentDischarge.lean:127`, ★★★, Gemini-vetted 2026-06-02) — for the
interacting asym lattice measure at fixed `(Nt, Ns, a)`:
`∫ e^{|ωf|} dμ_int ≤ 2 · exp(½ · Var_int(ωf))` plus integrability.
**Prior docs**: `docs/asym-expmoment-discharge-via-lee-yang-vet-request.md` (deep-think-vetted
architecture, 2026-05-31), `lee-yang/PLAN.md`, `lee-yang/README.md`.

## Current state of the `lee-yang` repo (audited 2026-07-12)

- **Polynomial side DONE** (commit `24722ca`): `Polynomial/RealZeros.lean` (293 ln) +
  `Polynomial/Asano.lean` (749 ln), 0 sorries / 0 axioms. The **master Asano theorem**
  (`asanoContract_no_zero_of_polydisk_no_zero`) and the multivariate in-place iterator
  (`iteratedAsano` + `iteratedAsano_isPolydiskZeroFree`) are landed. This was the hard algebra;
  it de-risks the campaign substantially relative to the 2026-05-31 estimates.
- **Measure side NOT started**: `Measure/Newman.lean` (77 ln) and `Measure/GriffithsSimon.lean`
  (81 ln) are docstring skeletons with no substantive declarations.

## ⚠ Recommended restructure of the measure side (Fable, 2026-07-12 — re-vet before building)

The vetted PLAN.md design routes through a **measure-level multivariate `IsLeeYang`** predicate
(entire CF on `V* ⊗ ℂ`, zeros on the Newman locus), Newman's Thm 3 for measures, and a
Hurwitz-type zero-transfer under the Griffiths–Simon limit. That machinery implicitly needs
**Hadamard factorization** (order-≤2 entire functions) and **Hurwitz's theorem** — neither
confirmed in Mathlib, each a heavy standalone project.

**Observation: pphi2's consumer never needs any of it.** The axiom is stated at *fixed finite
lattice*, and the GS approximants have *polynomial* partition functions. Route the proof as
**inequality-first**: prove Newman's bound where it is elementary (finite Ising, polynomial CF),
and pass the *inequality* — not the zero structure — through the GS limit:

1. **Finite-Ising Lee–Yang** (polynomial level, already 80% built): single-spin partition
   polynomial is trivially in the class; couple the (ferromagnetic) pair interactions by
   `iteratedAsano` over the edge list ⟹ the lattice Ising partition function in the field
   variables is polydisk-zero-free ⟹ zeros on the imaginary axis in each field variable after
   the fugacity↔field change of variables. *(New: the fugacity↔field bridge lemmas; the Asano
   engine itself is done.)*
2. **Newman's inequality for polynomial CFs** (elementary, no Hadamard): a normalized even real
   polynomial `φ(t) = ∏ⱼ (1 + t²/αⱼ²)` with imaginary zeros `±iαⱼ` satisfies
   `φ(t) ≤ exp(t² Σⱼ αⱼ⁻²) = exp(t² · Var/2)` termwise (`1 + x ≤ eˣ`), with
   `Var = φ''(0) = 2 Σⱼ αⱼ⁻²` by the product expansion. The `K = 2` `|·|`-form follows from
   `e^{|x|} ≤ e^x + e^{-x}` as in the axiom docstring.
3. **Griffiths–Simon limit passes the inequality**: approximate each site's Wick measure
   `Z⁻¹ e^{−a²:P(φ):_c} dφ` by Asano-rescaled sums of `n` Ising spins (Simon *P(φ)₂* §VIII.3;
   GJ §9.3(?) — pin the citation); the full-lattice approximants converge in distribution with
   MGFs and variances converging, so `MGF_n(t) ≤ exp(t² Var_n/2)` survives `n → ∞`. Needs
   *uniform* exponential integrability of the approximants (sub-Gaussian blocks; the coupling
   density `e^{J φ_x φ_y}` is unbounded, so this is the analytically careful step — see risks).
4. **pphi2 adapter** (`AsymInteractingLeeYang.lean` in pphi2): exhibit
   `interactingLatticeMeasureAsym` in the GS-approximable form — single-site Wick factors
   (matching `evenPolynomialWick c a P` with `c = wickConstantAsym`, per the PLAN's explicit-
   variance recalibration) × ferromagnetic nearest-neighbor couplings (off-diagonal of
   `−Δ_a` has the right sign; mass + Wick terms are single-site). Then instantiate 1–3.

**What this removes from scope**: measure-level `IsLeeYang`, Hadamard factorization, Hurwitz —
the PLAN's `Newman.lean` shrinks to the polynomial-CF inequality + limit-passage lemmas. The
measure-level API can be built later for Mathlib-upstream purposes; it is not on pphi2's path.

## Work breakdown (revised estimates)

| # | Deliverable | Repo | Est. lines | Est. effort | Risk |
|---|---|---|---|---|---|
| A1 | Fugacity↔field bridge + finite-Ising LY via `iteratedAsano` | lee-yang | 300–500 | 1–2 wk | conventions (see risks) |
| A2 | Newman inequality for polynomial CFs + `K=2` form + Var identification | lee-yang | 250–400 | ~1 wk | low (elementary) |
| A3 | GS single-site approximation + full-lattice limit passage | lee-yang | 500–900 | 2–3 wk | **highest** — uniform exp integrability |
| A4 | pphi2 adapter `AsymInteractingLeeYang.lean` → discharge the axiom | pphi2 | 300–500 | ~1 wk | ferromagnetic-sign bookkeeping |

Total: ~4–7 weeks at recalibrated norms, parallelizable A1/A2 (independent) then A3 → A4.
A2 is delegable once statements are pinned; A1's bridge lemmas and all of A3's statement design
are Fable-grade (convention traps, limit-interchange hygiene).

## Risks / pin-before-building

1. **Re-vet the restructure** (protocol): send this doc's route 1–3 to Gemini + Codex before
   writing A1 — specifically whether any step of the classical GS argument secretly needs
   zero-structure in the limit (it should not: the consumer is an inequality at fixed lattice).
2. **Fugacity↔field conventions** (A1): Lee–Yang "zeros on unit circle in fugacity `z = e^{−2h}`"
   vs "imaginary axis in `h`" vs the polydisk normalization used by `IsPolydiskZeroFree` — one
   Möbius/exponential bridge per formulation. Historically where sign errors enter; pin with a
   worked 1-spin and 2-spin example file before the general lemma.
3. **A3 uniform integrability**: the approximating blocks are sums of bounded spins, hence
   uniformly sub-Gaussian, but the pair-coupling density is unbounded — the clean route is to
   keep the coupling *inside* the GS-approximated Gibbs measure (approximate the full measure,
   not the free product) so every approximant is a genuine finite Ising Gibbs measure and only
   single-site marginals are approximated. Confirm this matches Simon §VIII.3's setup.
4. **Variance matching**: the axiom's RHS uses `Var_int` of the *limit* measure; A3 must give
   `Var_n → Var_int` (second moments converge — needs the same uniform integrability) so the
   bound lands in the exact form of the axiom (no `sup_n Var_n` weakening).
5. `nelson_exponential_estimate_master_bounded` (INDEX #25) is **not** part of this campaign —
   it is the square-lattice Nelson-engine compatibility wrapper (Cluster A lane), despite being
   listed alongside Layer A in some tables. Do not scope it here.

## Sequencing

- M2 (cylinder OS0–OS3 with retained vetted axioms) does **not** wait for this campaign.
- Start A1+A2 when a slot opens; A3 is the long pole; A4 discharges the axiom and (with B2 +
  Layer C) makes `asymInteracting_expMoment_volume_uniform` a theorem → M3.
