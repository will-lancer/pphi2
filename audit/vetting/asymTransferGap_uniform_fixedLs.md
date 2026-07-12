# Vetting — `asymTransferGap_uniform_fixedLs`

```yaml
---
axiom: asymTransferGap_uniform_fixedLs
file: Pphi2/AsymTorus/AsymSliceFamilySusceptibility.lean
statement_hash: null
model: gemini-3.1-pro
tool: chat_gemini statement vet (B2 route (a) extraction pass, §S2)
source_code: GR, LP
date: 2026-07-12
questions: [carrier object, Nt-dependence via wickConstantAsym, coupled Ns·a = Ls quantifier, γ-form vs mass-gap form]
verdict: PASSED — statement pinned in planning/b2-route-a-statements.md §S2
rating: Standard
discharged: false
superseded_by: null
---
```

**Statement form.** (S2 / "17a" of `planning/b2-route-a-statements.md`,
entered verbatim.) At fixed spatial circumference `Ls > 0` there exist
`m₀ > 0` and `a₀ > 0` such that for every lattice `(Nt, Ns, a)` with
`Ns·a = Ls` and `a ≤ a₀`, the normalized asym transfer operator
`asymTransferNormalized` contracts by `γ = exp(−m₀·a)` on the orthogonal
complement of the Jentzsch ground vector `asymGroundVector`:

`∀ v ⊥ Ω, ‖T̂ v‖ ≤ exp(−m₀·a)·‖v‖`, uniformly in `Nt`, `Ns`, `a`.

**Carrier correction (extraction pass, 2026-07-12).** The PROVED gap object
in pphi2 is the operator-norm contraction `γ_op = ‖A_W‖/λ₀ < 1` on the
ground-orthogonal complement (`asymTransferNormalized_gap`,
`AsymSpectralGap.lean:29`) — NOT `exp(−a·asymMassGap)` (the mass-gap object
is a gap to *an* excited eigenvalue, weaker than the operator-norm gap the
susceptibility machinery consumes). S2 is stated on exactly the consumable
object, in the same γ-form as `asymGappedTransfer`'s `hnorm` hypothesis.

**Vet verdict (Gemini 3.1-pro, 2026-07-12).** PASSED.
* **`Nt`-dependence harmless**: the transfer operator depends on `Nt` only
  through `wickConstantAsym(Nt, Ns, a)`, which converges as `Nt → ∞` at fixed
  `(Ns, a)`; Schrödinger eigenvalues are continuous in the polynomial
  coefficients, and every finite `Nt` has a positive gap (compact resolvent,
  bounded-below even polynomial), so `inf_{Nt} m_gap > 0`.
* **Coupled quantifier essential**: the `Ns·a = Ls` hypothesis inside the
  `∀` is what the removed FALSE predecessors (`spectral_gap_uniform`,
  `spectral_gap_lower_bound`, PR #60 — fixed-`Ns` shrinking-volume regime)
  lacked. Regime (ii): no coupling-strength hypothesis needed.
* **Expert story**: `T_a → e^{−aH(Ls)}` in compact-resolvent (norm-resolvent)
  sense; `H(Ls)` = spatially cut-off `P(φ)₂` Hamiltonian on the circle of
  circumference `Ls`, with strictly positive gap `m(Ls)` (Glimm–Jaffe;
  Simon Ch. VI). See
  `reflection-positivity/docs/B2_UNIFORMITY_QUESTION.md` for the full
  uniformity discussion.

**Citation.** Glimm–Jaffe, *Quantum Physics*, Ch. 6, 19; Simon, *The P(φ)₂
Euclidean (Quantum) Field Theory*, Ch. VI (semigroup convergence and the
positive Hamiltonian mass gap in finite spatial volume).

**Consumer (same commit).**
`asymSliceFamily_pathMeasure_second_moment_le_fixedLs`
(`Pphi2/AsymTorus/AsymSliceFamilySusceptibility.lean`): the
`γ := exp(−m₀·a)` specialization of the hole B-I slice-family susceptibility
bound, making the `2/(1−γ)` prefactor a-uniformly `≲ 2/(m₀·a)`-controlled at
fixed `Ls`. Also the future OS4/M4 brick.

**Discharge route.** Norm-resolvent convergence of the lattice transfer
generator to `H(Ls)` (fixed `Ls`, `a → 0`), plus continuity of the bottom of
the spectrum; the finite-`a` tail (`a ∈ [a₀', a₀]`) by compactness and the
per-lattice Jentzsch gap.
