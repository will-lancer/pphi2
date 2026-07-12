# Layer B2 free-side assembly — design-pass verdict (Phase 2a.2)

**Date**: 2026-07-12. **Status**: design pass DONE (mandated by
[`layer-B2-scoping.md`] before formalizing the free-side assembly). Verdict verified by hand
computation + Gemini 3.1-pro same-day review. **Consequence: the Pieces 2–3 → B5b → assembly
chain as scoped CANNOT discharge the all-`G` axiom; a mode-aware repair is required.**

## The target and the chain

Axiom `asymInteractingVariance_le_freeVariance_lattice_Lt_uniform`
(`AsymExpMomentDischarge.lean:215`): `∃ C` (before `Lt, Nt, Ns, a, G`!) with
`Var_int(⟨ω,G⟩) ≤ C·Var_free(⟨ω,G⟩)` for **all** lattice vectors `G`, uniform in `(a, Lt)` at
fixed `Ls`. The scoped chain (Pieces 2–3 + B5b): slice decomposition + oscillation-blind
susceptibility (`|⟨v_t, T^d v_{t'}⟩| ≤ γ^d‖v_t‖‖v_{t'}‖`, AM-GM, geometric series) gives
`Var_int(G) ≤ (2C₁/(1−γ))·Σ_t VarSlice_int(g_t)`, then B5b per slice:
`… ≤ (2C₁C₂/(1−γ))·Σ_t C_free^slice(g_t)` — call this **(†)**.

## Finding 1 — (†) cannot reach `C·Var_free(G)` (verified, both reviewers concur)

Temporal Nyquist test `g_t = (−1)^t g`: the free side has the temporal symbol `4/a²`, so
`Var_free(G)` is suppressed by `~ a²`; but (†)'s RHS strips the signs
(`Σ_t C_free^slice(g_t) = Nt·C_free^slice(g)`) and carries `1/(1−γ) ~ 1/(m_gap·a)`, so
`RHS(†)/Var_free(G)` blows up like a negative power of `a` (and grows with `Lt`). The
interacting variance itself IS small at Nyquist (UV: interacting ≈ free), so **the axiom is
fine but the intermediate (†) is not** — the absolute values destroy the destructive
interference the free side relies on. No constant-`C` free-side assembly can follow (†).
This is the June "NORM MISMATCH" finding resurfacing concretely; the 2026-06-03 parking of
FSS ("the dangerous direction is time, owned by the proved gap") was incomplete — the gap
route as used is *lossy* at high temporal frequency, not merely unneeded there.

## Finding 2 — the repair is a temporal mode split (two viable designs)

`Var_int(G) = Σ_k |Ĝ(k)|²·S_int(k)` (needs a temporal/spatial DFT layer in pphi2 —
gaussian-field's DFT machinery per `docs/track2-upstream-dft-machinery.md` is the base):

- **High temporal frequency `|k_t| ≳ κ`** — **FSS infrared bound** from lattice reflection
  positivity: `S_int(k) ≤ c/D̂_Laplacian(k)` (massless symbol), valid a-/volume-uniformly, at
  all couplings, **robust to the Wick counterterm** (the double-well single-site measure is a
  Griffiths–Simon/Ising limit — same mechanism as Layer A; NOT the refuted Brascamp–Lieb
  route, which needed log-concavity). Then massless ≤ `(1 + m²/κ²)`·massive.
- **Low temporal frequency `|k_t| ≲ κ` with `κ ~ m_gap`** — the existing susceptibility/gap
  route: the oscillation-blind loss is only `O(1)` when the frequency is below the inverse
  correlation length (`k_t ≲ m_gap` ⟺ phases move by `O(1)` within the γ-correlation range).
  Pieces 1–5, B5b, and the GNS bridge axioms all remain valid as **this branch**.
- ⚠ **Refinement beyond the external review** (pin in the statement design): FSS alone does
  NOT cover small nonzero `k_t` — the massless/massive ratio `(k_t² + m²)/k_t²` diverges as
  `k_t → 0` (and `Lt → ∞` makes `k_t = 2π/Lt` arbitrarily small). Gemini's "gap for `k = 0`
  only" is too optimistic; the crossover at `κ ~ m_gap` is where the two branches must be
  stitched, and the low branch must handle a *band*, not a point. The band version of the
  susceptibility bound needs either (i) the AM-GM bound applied to the band-projected `G`
  (loss `O(1)` as above — quantify the constant `sup_{|k_t|≤κ} …` explicitly), or (ii) the
  exact **Poisson-kernel resummation** below.
- **Alternative (single-mechanism, no FSS dependency): operator Poisson kernel.** Keep
  `e^{ik_t d}` inside the temporal sum *before* any absolute value:
  `Σ_d e^{ik_t a d}⟨v, T^{|d|}v⟩` resums (spectral theorem for the compact self-adjoint
  normalized transfer operator) to Poisson-kernel factors
  `(1−λ²)/(1−2λcos(k_t a)+λ²)` per eigenvalue `λ ≤ γ`, which reproduce a massive temporal
  symbol with mass `m_gap` at ALL `k_t` — including the `a²`-suppression at Nyquist. Then
  only the slice/spatial matching (B5b) remains. Risk: this heads toward the interacting
  Källén–Lehmann territory that the 2026-06-02 vetting said not to axiomatize; it is viable
  ONLY as a proved spectral-theorem computation, never as a representation axiom.

## Decision needed (owner): FSS + gap band-split vs Poisson kernel

- **FSS + band-split**: canonical in the literature (both reviewers), reuses Layer A's
  Griffiths–Simon investment, but *unparks the FSS bound as a genuine new formalization
  target for B2* (`docs/fss-infrared-bound-spec.md` — its "not for B2" banner is now known
  to be wrong) and needs the DFT layer + the band-stitching constant.
- **Poisson kernel**: stays inside the already-proved transfer-operator framework (no new
  RP/chessboard input), needs the DFT layer + a careful spectral-resummation lemma; avoids
  FSS entirely but the spatial matching after resummation must be checked against the
  norm-mismatch trap (B5b covers the slice side; verify the eigenvector-dependence of the
  Poisson factors doesn't reintroduce it).
- Either way: **Pieces 1–5 as landed are NOT wasted** — they are the low-frequency/zero-mode
  branch (FSS route) or the `k_t`-independent skeleton (Poisson route). The 6 GNS bridge
  axioms and B5b stay on the critical path.

## Immediate doc actions (this commit)
- Banner added here; `layer-B2-scoping.md` and `INDEX.md` row 3 should point at this verdict
  before any Piece-2/3 free-side code is written (Piece 2/3 statements are fine; it is the
  *assembly* target that changes).
- `docs/fss-infrared-bound-spec.md`'s parking note is superseded for the FSS-route option.
