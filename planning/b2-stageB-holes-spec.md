# B2 Stage B — statement designs for holes B-I and B-II

**Date**: 2026-07-12 (late). **Parent**: [`b2-route-a-statements.md`](b2-route-a-statements.md)
(Stage-B extraction section — verbatim brick signatures live there). Target shapes are FIXED
by the proved shell (`AsymB5bSingleSlice.lean:224/:273`): B-I proves its `hPiece3`
hypothesis, B-II replaces its `hFreeAssemble`/`hRem` hypothesis on the band.

## Hole B-I — `hPiece3` (slice-family susceptibility bound)

**Target (shape pinned by the shell):**
```lean
theorem asymSliceFamily_pathMeasure_second_moment_le
    (Nt Ns) [NeZero Nt] [NeZero Ns] (P) (a mass) (ha) (hmass)
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hnorm : ∀ v, ⟪asymGroundVector …, v⟫ = 0 → ‖asymTransferNormalized … v‖ ≤ γ * ‖v‖)
    (g : ZMod Nt → SpatialField Ns)
    (hInt : ∀ t, Integrable (fun ψ => (asymSliceObsLinear (g t) ψ)^2 * (Ω ψ)^2) ν) :
    ∫ ψ, (asymSliceFamilyLinear g ψ)^2 ∂(pathMeasure Nt) ≤
      (2 / (1 - γ)) * groundSliceVarianceSum … g
        + C_rem-form * (Nt : ℝ)^2 * γ ^ Nt * (…)      -- exact remainder shape: see step 7
```
(`asymSliceFamilyLinear g ψ = Σ_t asymSliceObsLinear (g t) (ψ t)`.)

**Proof design (7 sub-lemmas; each bounded):**

1. **Truncate**: work at `A_{K,t} := asymSliceObsTrunc (g t) K` (bounded, odd); target the
   K-uniform bound first; the landed K→∞ engine (`AsymBridgeKLimit.lean:296/:320`) transfers
   to the linear observables at the end. (Engine complete — final step is mechanical.)
2. **Square expansion** (finite sums, Fubini on the probability pathMeasure with bounded
   integrands): `∫(Σ_t A_{K,t}(ψ_t))² = Σ_{t,t'} ∫ A_{K,t}(ψ_t)·A_{K,t'}(ψ_{t'})`.
3. **Mean-zero by parity** (kills the disconnected part): `∫ A_{K,t}(ψ_t) dpath = 0`.
   Sub-design: the single-slice marginal of the pathMeasure is `Ω²·ν`-proportional (or use
   the dictionary at `B = 1`); `A_{K,t}` is odd (truncation of an odd linear functional with
   odd clamp); `Ω²ν` is parity-invariant. New small lemma needed:
   `asymGroundVector_comp_neg : Ω(−ψ) =ᵐ Ω(ψ)` — from ground-state simplicity + parity
   symmetry of the transfer operator (P even ⟹ transfer weight even ⟹ T commutes with the
   parity operator; ground simple + positive (`asymGroundStateRep_pos_ae`) ⟹ parity-fixed).
   ⚠ If the parity route fights the L² representative plumbing, fallback: keep the
   disconnected means and bound them into the remainder — but then the target constant
   changes; prefer parity. Flag to coordinator if fallback is needed.
4. **Cyclic invariance of the pathMeasure** (NEW, candidate for upstreaming to
   reflection-positivity): for the cyclic shift `σ_c : (ZMod Nt → S) → (ZMod Nt → S)`,
   `(pathMeasure Nt).map σ_c = pathMeasure Nt`. Proof: pathMeasure is the kernel-product
   measure with cyclic trace structure (`partition_eq_trace` layer); a Fubini/reindex over
   the product of kernels. Consequence: `∫A_t(ψ_t)A_{t'}(ψ_{t'}) = pathConnectedTwoPoint`-at-
   separation `d = t' − t` with observables `(A_t, A_{t'})`.
5. **Off-diagonal finite-K bridge** — generalize
   `asymSliceObsTrunc_pathMeasure_connected_two_point_bound` (`AsymBridgeInstance.lean:288`)
   from `(A, A)` to `(A_t, A_{t'})` (the underlying engine `connected_two_point_le` already
   takes `MA ≠ MB`; the pphi2 wrapper is what's diagonal). Same statement with two
   observables and RHS `‖P₁M_tΩ‖·‖P₁M_{t'}Ω‖·(γ^d + γ^{Nt−d}) + C_rem·γ^Nt`.
6. **AM-GM + averaged sum**: `‖P₁M_tΩ‖·‖P₁M_{t'}Ω‖ ≤ ½(‖P₁M_tΩ‖² + ‖P₁M_{t'}Ω‖²)`, then
   `averaged_susceptibility_bound` (verbatim shape match: `b_k := ‖P₁M_kΩ‖²`,
   `gam k := γ`) gives `Σ_{t,t'≠t} … ≤ (1+γ)/(1−γ)·Σ_t ‖P₁M_tΩ‖²`; the diagonal `t = t'`
   terms are `∫A_{K,t}² ≤ ∫⟨g_t,ψ⟩²Ω²dν` directly (clamp bound). Piece 1
   (`norm_sq_proj_obsTrunc_omega_le`) converts every `‖P₁M_tΩ‖²` to
   `groundSliceVariance (g t)`. Total constant: `1 + (1+γ)/(1−γ) = 2/(1−γ)` ✓ matches the
   shell's constant exactly.
7. **Remainder bookkeeping**: `Nt·(Nt−1)` off-diagonal pairs each contribute `C_rem·γ^Nt` ⟹
   remainder `≤ C_rem·Nt²·γ^Nt`. The shell's consumer must absorb an `Nt²` (not `Nt`) tail —
   check `piece3_pathMeasure_bound_to_freeCovariance_sum`'s remainder slot; if it hard-codes
   `Nt·γ^Nt`, generalize the shell's hypothesis (its proof is algebraic and indifferent).

**S2 lands in the same PR** (exactly the pinned `asymTransferGap_uniform_fixedLs` from
§S2 of `b2-route-a-statements.md`): its consumer is the specialization `γ := exp(−m₀a)` of
this theorem making `2/(1−γ) ≤ 2/(m₀a·(1−ε))`-controlled uniformly. Audit rows + vetting
record (cite the §S2 vet) in the same commit.

## Hole B-I — **LANDED (`1b2807a`) modulo two carried hypotheses; adjudication below**

**Outcome:** headline `asymSliceFamily_pathMeasure_second_moment_le` kernel-clean (bare trio);
S2 landed with consumer; counts 28 raw / 26 real; parity (step 3) proved OUTRIGHT via the
field-flip route (no L² representative issues); cyclic invariance proved generically over
`TransferSystem` (upstreaming candidate). Spec's step-6 diagonal claim was WRONG at finite
`Nt` (single-slice marginal = `Z⁻¹·kPow(Nt−1)(x,x)·ν`, not `Ω²ν`) — agent caught it; the
`O(γ^Nt)` correction is carried as `hDiag`. The K-uniformity gap of
`asymFinitePeriodicBridge_remainder_bound` is carried as `hRes`. Remainder shape:
`(C_diag·Nt + C_off·Nt²)·γ^Nt`; shell consumed it unchanged; constant exactly `2/(1−γ)`.

**Adjudication (coordinator, Gemini-vetted 2026-07-12): STRENGTHEN the bridge axiom to the
K-uniform form.** Mechanism confirmed: intrinsic ultracontractivity
(`T(x,y) ≤ C·Ω(x)Ω(y)`) reduces all residual/trace terms to Ω-weighted L¹/L² data
(`Tr(M_A Q^d M_B Q^{Nt−d}) ≤ C²γ^{Nt}·‖AΩ‖₁‖BΩ‖₁`), so the clamp domination
`|A_K| ≤ |⟨g,·⟩|` passes with NO `‖A‖_∞` penalty; the diagonal correction
(`|Q^{Nt}(x,x)| ≤ Cγ^{Nt}Ω(x)²`) discharges `hDiag` by the same mechanism. Strengthened
statement: same shape, `∃ C` depending on `(Nt-FREE: uniform in K, d, Nt; may depend on
a, Ns, P, mass)`, bound `C·‖M_{⟨g,·⟩}Ω‖·‖M_{⟨g',·⟩}Ω‖·γ^Nt`. Same rating (Standard) and
discharge plan (trace bridge / IUC); vetting-record update required.

**⚠ Stage-C design question #1 (from the vet's fine print):** the IUC constants depend on
`(a, Ls)`; at fixed `Lt`, `γ^Nt ≤ e^{−m₀Lt}` does NOT decay while `Nt² = (Lt/a)² → ∞` as
`a → 0` — the remainder's `a→0` corner is NOT automatically dominated. Stage C must either
(i) show the shell's `hRem` absorption works with the free sum's own `a`-powers in that
corner, or (ii) restate the remainder control with explicit `a`-dependence and check the
three-way stitching there. Do not hand-wave this corner — it is crux-2 class.

## Hole B-II — band-limited free-side comparison — **LANDED (`580205b`)**

**Outcome (2026-07-12): all theorems, 0 axioms/sorries, kernel-clean.** Final theorem
`freeSingleSliceCovarianceSum_le_freeVariance_of_band` with the HONEST constant
`C_band Ls mass κ = (κ² + mass²)·(4/mass² + 2·Ls/mass)`, uniform in `(a, Nt)` at fixed `Ls`.
Constant vs the vetted ledger (reported, not absorbed): per-instance coefficient is
`(κ²+m²)·(4/(Nt·m²) + 2a/m)` — the `2a/m` term confirms the predicted spare `a` (better than
the ledger); the `4/(Nt·m²)` term is the temporal ZERO MODE, not covered by the pure
`Ls(κ²+m²)/m` form at small `Nt` (the ledger implicitly assumed bounded `Lt`). T4 proved as
`Σ(λ+m²)⁻¹ ≤ 2/m² + a·Nt/m` (coarse split, no integral comparison). Note for B-I merge:
this file defines `sliceConstant` (pointwise) + the `sliceAvgProj` bridge lemma — reconcile
if B-I introduces its own.



**Design principle (avoids the eigenbasis-indexing trap a third time):** never touch the
abstract 2D eigenbasis. `sliceAvgProj` commutes with `massOperatorAsym` (Stage A), hence with
its inverse/covariance; on the slice-constant subspace the 2D GJ form REDUCES to the 1D
temporal form with an explicit `Ns` multiplicity. All statements below are about concrete
temporal profiles `c : ZMod Nt → ℝ` and the existing 1D DFT toolkit at size `Nt`.

**Target (replaces the shell's `hFreeAssemble` on the band):**
```lean
theorem freeSingleSliceCovarianceSum_le_freeVariance_of_band
    (Nt Ns) [NeZero Nt] [NeZero Ns] (a mass Ls : ℝ) (ha) (hmass) (hLs : (Ns:ℝ)*a = Ls)
    (κ : ℝ) (hκ : 0 < κ)
    (G : AsymLatticeField Nt Ns) (hsc : sliceConstant G)          -- Stage A predicate
    (hband : temporalBandLimited κ G)                              -- see T3 below
    : freeSingleSliceCovarianceSum … (fun t => asymSliceEquiv … G t) ≤
        C_band Ls mass κ * ∫ ω, (ω G)^2 ∂(latticeGaussianMeasureAsym …)
```
with `C_band Ls mass κ = Ls·(κ² + mass²)·c₀/(mass)`-shape — the exact constant to fall out
of T1–T4; the vetted ledger says it is `Ls(κ²+m²)/m` up to an absolute constant (the `m₀`
in the vetted `Ls(κ²+m²)/(m·m₀)` belongs to B-I's `1/(1−γ)`, NOT here — keep the two
factors in their own lemmas).

**Sub-lemmas:**

T1. **Slice-constant reduction of the free variance**: for slice-constant `G` with temporal
   profile `c` (`G(t,s) = c t`):
   `∫(ωG)² dμ_GFF = Ns · (a²)⁻¹ · Σ_{m₁ : Fin Nt} (latticeEigenvalue1d Nt a m₁ + mass²)⁻¹ ·
      (temporal DFT coefficient of c at m₁)² / latticeFourierNormSq Nt m₁`.
   Route: `asymFreeVariance` via the 2D product-DFT form
   (`abstract_spectral_eq_dft_spectral_2d_asym`, gaussian-field `AsymCovariance.lean:719`):
   for slice-constant `G`, the spatial DFT factor `Σ_s φ_{m₂}(s)` vanishes unless `m₂ = 0`
   (orthogonality of the 1D basis against constants) and equals `√Ns·c`-normalized at
   `m₂ = 0`; the spatial eigenvalue term drops (`latticeEigenvalue1d Ns a 0 = 0`). Pure
   computation with existing lemmas.
T2. **One-slice covariance at a slice profile**: `freeSingleSliceCovariance t (c_t • 𝟙) =
   c_t² · freeSingleSliceCovariance t 𝟙` (landed `_smul`), and the evaluation
   `freeSingleSliceCovariance t 𝟙 = Ns·(a²)⁻¹·Nt⁻¹·Σ_{m₁} (λ^{1d}_{m₁} + mass²)⁻¹`
   (same 2D-DFT computation with the one-hot temporal profile — its temporal DFT spreads
   flat, `|ĉ|² = 1/Nt` per mode against normSq bookkeeping). Then
   `freeSingleSliceCovarianceSum = (Σ_t c_t²)·(that constant)`.
T3. **Band predicate + temporal Parseval**: define `temporalBandLimited κ G` as: the temporal
   DFT coefficients of the profile `c` vanish for modes with `latticeEigenvalue1d Nt a m₁ >
   κ²`. Parseval (1D, size Nt): `Σ_t c_t² = Σ_{m₁} (coeff)²/normSq`. On the band each
   surviving mode has `(λ^{1d} + m²)⁻¹ ≥ (κ² + m²)⁻¹`, so T1 gives
   `Var_free(G) ≥ Ns·(a²)⁻¹·(κ²+m²)⁻¹·Σ_t c_t²`.
T4. **The slice-constant evaluation bound**: `Nt⁻¹·Σ_{m₁}(λ^{1d}_{m₁}+m²)⁻¹ ≤ c₀·a/mass`
   (the discrete temporal Green's function at coinciding times: Riemann-sum comparison of
   `Nt⁻¹Σ (4/a²·sin² + m²)⁻¹` against `∫dω/(ω²+m²) = π/m` — this is the ONE analytically
   careful estimate in B-II; the classical value is `a/(2m)·(1+o(1))`; any explicit
   `c₀·a/mass` upper bound with absolute `c₀` suffices. Prove by pairing each mode with the
   integral comparison, or crudely: split the sum at `|freq| ≤ mass·a·Nt`-scale. If this
   fights, an `Ls`-dependent constant is acceptable as fallback: `≤ c₀·a·(1/mass + a·Nt·…)`
   — flag to coordinator.)
   Combining T2+T4: `freeSingleSliceCovarianceSum ≤ Ns·(a²)⁻¹·(c₀·a/mass)·Σ_t c_t²`, and
   with T3: ratio `≤ (c₀·a/mass)·(κ²+m²)·… = c₀·Ls·(κ²+m²)/mass · (a-powers cancel:
   `Ns·(a²)⁻¹·a = Ns/a`… CHECK: LHS `Ns·a⁻¹·c₀/mass·Σc²`, RHS `Ns·a⁻²·(κ²+m²)⁻¹Σc²` ⟹
   ratio `= c₀·a·(κ²+m²)/mass` → **that VANISHES as a→0, even better than the vetted
   ledger** — re-derive carefully at implementation; if the ratio really carries a spare
   `a`, the vetted `Ls(κ²+m²)/m` is a safe over-estimate; either way uniform. Any
   discrepancy with the vetted ledger must be reported, not silently absorbed.)

**File plan**: B-II in a new `Pphi2/AsymTorus/AsymBandFreeComparison.lean` (imports
AsymSpatialConstant, AsymB5bSingleSlice, AsymFreeSpectral); B-I in a new
`Pphi2/AsymTorus/AsymSliceFamilySusceptibility.lean` (+ the S2 axiom either there or in
AsymSpectralGap.lean; + possible small addition to reflection-positivity? NO — keep the
cyclic-invariance lemma in pphi2 for now, upstream later). Disjoint from each other ⟹
parallel implementation.

## Item-1 upgrade (2026-07-12, latest): the τ-form — a-uniform bridge axioms (Gemini-vetted)

The explicit-factor sharpening (C independent of `g`, `√gSV` factors — landed) is necessary
but NOT sufficient: the per-step IUC constant `C(a)` **blows up as `a → 0`** (short-time
kernel → delta; rate `~ a^{−1/2}`-ish), so the instance-existential `C` in the current axioms
is implicitly a-divergent, and Stage C's corner would still fail. **Vetted fix (full proof
blueprint received)**: attach the kernel bound to a fixed physical reference time `τ > 0`
(require `Lt = Nt·a ≥ 2τ`; at least one arc is ≥ `Lt/2 ≥ τ`):
- HS Cauchy–Schwarz split `|Tr(Ã Q^d B̃ Q^{Nt−d})| ≤ ‖Q^{τ/(2a)}Ã‖_HS·‖Q^d‖op·‖B̃ Q^{Nt−d−τ/(2a)}‖_HS`;
- operator norm `γ^k` on the short arcs, IUC ONLY at the fixed physical time
  (`Q^{τ/a}(x,x) ≤ C_IUC(Ls,τ)·Ω(x)²`);
- total damping `γ^{Nt}·γ^{−τ/a}`; with the S2 gap `γ = e^{−m₀a}` this is `e^{m₀τ}` — constant.

**Axiom shapes to adopt (replace the current pair; keep names, add `(τ)` argument or fold
`γ^{−⌈τ/a⌉}` explicitly):**
  `residual ≤ C(Ls,τ,P,mass) · γ^(Nt − ⌈τ/a⌉) · √gSV(g t) · √gSV(g t')`   (for `Nt·a ≥ 2τ`)
  `∫A_K(ψ_t)² dpath ≤ (1 + C(Ls,τ,P,mass)·γ^(Nt − ⌈τ/a⌉)) · gSV(g t)`     (same proviso)
with `∃C` AFTER fixing only `(P, mass, Ls, τ)` — uniform over `(Nt, Ns, a, γ-data, g, K, d, t, t')`
with `Ns·a = Ls`. Small-`Lt` regime (`Nt·a < 2τ`): handled separately at Stage C (finite
physical volume — the B2 target there follows from the per-instance B1/Nelson bound, no gap
needed; OR keep the current per-instance axioms for that regime).
**Corner check with the τ-form**: remainder/main ≈ C·Nt·γ^{Nt−τ/a}·(1−γ)/2 =
C·(Lt/a)·e^{−m₀(Lt−τ)}·(m₀a)/2 = C·Lt·m₀·e^{−m₀(Lt−τ)}/2 — bounded in `a` AND decaying in
`Lt` ✓. Stage-C design question #1 is thereby RESOLVED at the design level.

Status: explicit-factor forms + rederived corollaries landed (compile in progress); the
τ-form revision is the next edit (same files; thread `τ` + the `Nt·a ≥ 2τ` proviso through
the corollaries; audit records updated to cite this section).

## Item 1 CLOSED (commit pending) → Stage C work plan (item 2)

τ-form landed and kernel-verified: `asymSliceFamily_pathMeasure_second_moment_le'` =
`[trio, diagonal_bound, remainder_bound_uniform]`; `…_fixedLs'` adds S2. Core theorems
R-generalized. Counts unchanged 30/28.

**Stage C tasks (mapped during the corner re-audit):**
- **C3 (REQUIRED for the corner, do first):** the main finite-K theorem still takes a SCALAR
  `C_off`, so the remainder carries `Nt²·γ^†·gSVSum` — ratio to main
  `~ m₀Lt²e^{−m₀(Lt−τ)}/(2a)`, STILL 1/a-divergent. Generalize `hRes` to a per-pair bound
  `r t t'` (conclusion `… + Nt·C_diag·R + Σ_{t≠t'} r t t'·R`), instantiate
  `r t t' := C·√gSV_t·√gSV_t'`, and Cauchy–Schwarz the double sum to `Nt·gSVSum`
  (`(Σ√gSV)² ≤ Nt·S`) — then remainder/main `≈ C·Lt·m₀·e^{−m₀(Lt−τ)}` ✓ bounded.
- **C1:** band-limitedness of the low projection: slice-constant eigenvector profiles are 1D
  temporal eigenvectors (via the Stage-A commutation), and the two-eigenvalue pairing trick
  kills temporal-DFT coefficients above `κ²` — gives B-II's `temporalBandLimited` for
  `asymModeProj S_low G`.
- **C2:** discharge `hInt` (`⟨g,ψ⟩²Ω² ∈ L¹`): from the transfer-kernel smoothing
  `Ω = λ₀⁻¹TΩ` (M_w Conv M_w structure gives explicit weight decay) — investigate existing
  bricks (AsymL2Operator/AsymNelson); else one new lemma. The B2 target has NO such
  hypothesis, so it must be discharged, not carried.
- **C4 (master assembly):** κ := min(mass, 4/Ls) (Stage-A `spatialGap_ge_sixteen_of_fixed_Ls`
  gives `κ² ≤ spatialGap` ⟹ low modes slice-constant); split G via `asymModeProj` (S4);
  `(x+y)² ≤ 2x²+2y²`; high branch = S1 consumer; low branch = B3 → B-I(τ,C3) → B5b → B-II;
  free-side reassembly exact (S4 additivity). Small-`Lt` (`Nt·a < 2τ`) regime: per-instance
  bound via B1 (`asymTorusIso_interacting_second_moment_density_transfer` per INDEX row-3
  notes) — finitely many... NO: (Nt,a) both continuous — handle via the per-instance
  τ-free bound with constant depending on `Lt ≤ 2τ` compactness — design at C4 time.
  Then Piece-5 converts `asymInteractingVariance_le_freeVariance_lattice_Lt_uniform` to a
  theorem; clustering axioms 14/15 follow per `cyl-2a-spectral-gap.md`.

## C4 design (2026-07-12, late) — thresholded target; C1 landed; regime analysis

**C1 LANDED** (`2083fe3`, `AsymLowModeBand.lean`): `asymModeProj_temporalBandLimited` — low-mode
projections are `temporalBandLimited κ` when `κ² ≤ spatialGap` (two-eigenvalue pairing; bare
trio; the 1D toolkit was size-generic, reused at `Nt` without cloning). C3 landed earlier
(`45937eb`, sharp `((2/(1−γ)) + C_rem·Nt·γ^†)·gSVSum` corollaries). C2 in flight.

**Regime analysis for C4 (the master assembly).** The B2 axiom as stated quantifies ALL
`(Lt, a)`; the proved chain covers `a ≤ a₀` (S2) and `Nt·a ≥ 2τ` (τ-axioms). The two
complements are analytically real but PHYSICALLY ARTIFICIAL:
- coarse `a > a₀` ⟺ finitely many `Ns` (since `a = Ls/Ns`), but `Nt`-uniformity at each
  fixed `(Ns, a)` is another S2-type input;
- short `Lt < 2τ`: no arc reaches the IUC window; B1's per-`(Lt, Ls)` constant has no
  proved sup over `Lt ∈ (0, 2τ]`.
Every downstream consumer needs the bound only EVENTUALLY (`Lt → ∞` IR limit, `a → 0` UV
limit). **Decision (flag for owner sign-off): C4's main theorem takes the thresholded form**
`∃ C L₀ a₀, 0 < C ∧ … ∀ Lt ≥ L₀, ∀ a ≤ a₀, (Nt·a = Lt, Ns·a = Ls) → ∀ G, Var_int ≤ C·Var_free`
(with `L₀ := 2τ`, `a₀` from S2) — pure assembly, no new axioms, no regime patches. Piece-5 /
Layer-C then migrate to eventual-form wiring (mechanical thread); the original all-`(Lt,a)`
axiom `asymInteractingVariance_le_freeVariance_lattice_Lt_uniform` is retained until the
migration, then deleted or restated (it is over-broad in the same spirit as the removed gap
axioms, though not false — the small-`Lt`/coarse-`a` cases are true but unproved).

**C4 assembly skeleton** (after C2): fix `τ := 1` (say), `κ := min mass (4/Ls)`
(`κ² ≤ 16/Ls² ≤ spatialGap`, Stage A A6); `S_low := {k : λ_k < mass² + κ²}`,
`S_high := S_lowᶜ` (`∀ k ∈ S_high, mass² + κ² ≤ λ_k`); split `G = P_low G + P_high G`
(S4 `asymModeProj_add_compl`); `(x+y)² ≤ 2x² + 2y²` inside `∫dμ_int`;
- high: S1 consumer `asymHighModes_variance_le_freeVariance` → `(1 + m²/κ²)·Var_free(P_high G)`;
- low: B3 (`interacting_second_moment_eq_pathMeasure`) + `asymSliceFamilyLinear_eq_slicePairing`
  → C3-sharp `…_le_fixedLs_sharp` (hInt by C2) → B5b (`groundVariance_sum_le_freeCovariance_sum`)
  → B-II (`freeSingleSliceCovarianceSum_le_freeVariance_of_band`; predicates by Stage A A5 +
  C1) → `C_low(Ls, m, κ, τ, m₀)·Var_free(P_low G)`;
- reassemble: `Var_free(P_low G) + Var_free(P_high G) = Var_free(G)` (S4 additivity);
  `C := 2·max(C_high, C_low)`. All constants depend only on `(P, mass, Ls, τ)`.
