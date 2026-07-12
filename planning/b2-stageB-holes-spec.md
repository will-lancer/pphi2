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

## Hole B-II — band-limited free-side comparison

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
