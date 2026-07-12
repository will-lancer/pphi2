# Vetting — `asymFinitePeriodicBridge_remainder_bound_uniform` + `asymFinitePeriodicBridge_diagonal_bound`

axiom: asymFinitePeriodicBridge_remainder_bound_uniform, asymFinitePeriodicBridge_diagonal_bound
file: Pphi2/AsymTorus/AsymSliceFamilySusceptibility.lean
rating: Standard
sources: GR (Gemini 3.1-pro, 2026-07-12), LP (Davies–Simon intrinsic ultracontractivity;
  Glimm–Jaffe trace bounds)
status: NOT VERIFIED (statement vetted; discharge = trace-bridge / IUC estimate, shared with
  asymFinitePeriodicBridge_remainder_bound)

## Statement content

K-uniform bounds for the finite-periodic GNS residual and the single-slice diagonal
correction, for the truncated slice-observable family `A_K = clamp(⟨g,·⟩,[−K,K])`:
`residual ≤ C·γ^Nt` and `∫A_K(ψ_t)² dpath ≤ groundSliceVariance + C·γ^Nt`, with `C`
uniform in `(K, d, t, t')` (may depend on `Nt, Ns, a, P, mass, γ`-data, `g`).

## Vet record (Gemini 3.1-pro, 2026-07-12)

Mechanism: intrinsic ultracontractivity of the P(φ)₂ transfer kernel
(`T(x,y) ≤ C·Ω(x)Ω(y)`; confining even polynomial potential). Consequences verified:
(i) `|Q^k(x,y)| ≤ Cγ^kΩ(x)Ω(y)` for the ground-orthogonal part `Q`;
(ii) `Tr(M_A Q^d M_B Q^{Nt−d}) ≤ C²γ^{Nt}‖AΩ‖₁‖BΩ‖₁ ≤ C²γ^{Nt}‖AΩ‖₂‖BΩ‖₂`;
(iii) diagonal `|Q^{Nt}(x,x)| ≤ Cγ^{Nt}Ω(x)²`. Pointwise clamp domination
`|A_K| ≤ |⟨g,·⟩|` transfers all bounds K-uniformly. Full exchange recorded in
`planning/b2-stageB-holes-spec.md` §"Hole B-I … adjudication".

## Caveat

IUC constants depend on `(a, Ls)`; NO a-uniformity claimed or used at this layer. The
`a→0`-at-fixed-`Lt` corner of the remainder is Stage-C design question #1.
