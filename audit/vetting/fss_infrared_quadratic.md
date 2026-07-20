# Vetting — `fss_infrared_quadratic`

```yaml
---
axiom: fss_infrared_quadratic
file: Pphi2/AsymTorus/AsymInfraredBound.lean
statement_hash: null
model: gemini-3.1-pro
tool: chat_gemini statement vet (B2 route (a) extraction pass)
source_code: GR, LP
date: 2026-07-12
questions: [a-power ledger, c0 constant, zero-mode guard, eigenbasis sharing]
verdict: PASSED — c0 = 1 exact in the GJ normalization
rating: Standard
discharged: false
superseded_by: null
---
```

**Statement form.** (S1 of `planning/b2-route-a-statements.md`.) For every
`(Nt, Ns, a, mass)` and every coupling `P`, and every lattice field `h` in the
zero-mode complement (`∑ x, h x = 0`),

`∫ (ω h)^2 dμ_int^lattice ≤ (a²)⁻¹ · Σ_k [m² < λ_k] (λ_k − m²)⁻¹ · c_k(h)²`

where `λ_k = massEigenvaluesAsym Nt Ns a mass k` and `c_k(h) = asymModeCoeff
Nt Ns a mass k h` are the proved Hermitian eigendata of `massOperatorAsym =
−Δ_a + m²`. The massless symbol is `λ_k − m²` (the operators differ by
`m² • 1`, so the eigenbasis is shared); the `if m² < λ_k` guard makes the zero
mode's exclusion explicit instead of relying on `(0 : ℝ)⁻¹ = 0`.

**Vet verdict (Gemini 3.1-pro, 2026-07-12).** Constant `c₀ = 1` is EXACT in
this GJ normalization: the kinetic action is `½⟨φ, (−Δ_unscaled)φ⟩` with
`−Δ_unscaled = a²(−Δ_lattice)` (coupling `β = ½`, no `a`-prefactors), so the
classical infrared bound `⟨|φ̂|²⟩ ≤ 1/D̂_unscaled = 1/(a²·D̂₀)` matches the
free-variance prefactor `(a²)⁻¹` exactly. Mass and Wick counterterms sit in the
single-site factor and never enter the denominator. Full reconstruction in the
§S1 vet record of `planning/b2-route-a-statements.md`.

**Citation.** Fröhlich–Simon–Spencer, "Infrared bounds, phase transitions and
continuous symmetry breaking", Comm. Math. Phys. 50 (1976) 79–95; Simon, *The
P(φ)₂ Euclidean (Quantum) Field Theory* (1974); Glimm–Jaffe, *Quantum Physics*.

**Discharge route (later).** Lattice reflection positivity over the kinetic
bonds → Gaussian domination `Z[h] ≤ Z[0]·exp(½⟨h, (−Δ)⁻¹h⟩)` → `t²`-expansion
at the Z₂-even measure. Shares the Griffiths–Simon machinery with Layer A.

**Consumer (proved in the same file).**
`asymHighModes_variance_le_freeVariance`: for mode sets `S` with
`m² + κ² ≤ λ_k` on `S`, `Var_int(P_S G) ≤ (1 + m²/κ²)·Var_free(P_S G)` — the
high branch of the S3 band-split master lemma. Uses the proved lemmas
`massOperatorAsym_const`, `sum_massEigenvectorBasisAsym_eq_zero_of_ne`, and
`sum_asymModeProj_eq_zero` (zero-mode complement) plus the S4 free-side toolkit
(`asymModeCoeff_proj`, `asymFreeVariance_eq_sum_modeCoeff_sq`).
