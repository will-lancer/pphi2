/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.AsymTorus.AsymSliceFamilySusceptibility
import Pphi2.AsymTorus.AsymGroundIntegrability

/-!
# Item 3a: asym exponential clustering in physical distance (fixed `Ls`)

The CYL-2a clustering payoff of the landed Layer-B2 machinery
(`planning/cyl-2a-volume-scaling-addendum.md` §"2026-07-13 — post-B2 clustering design"):
at fixed spatial circumference `Ls` and reference time `τ`, the periodic path-measure
connected two-point function of two truncated slice observables decays exponentially in
**physical** separation, at an `a`-uniform rate `m₀`, in the two-arc periodic form, plus a
`τ`-residual tail — with constants uniform in `(Nt, Ns, a, g, g', K, t, t')` under
`Ns·a = Ls`, `a ≤ a₀`, `2τ ≤ Nt·a`.

## Statement form

The headline `asymSliceObsTrunc_exponential_clustering_fixedLs` is stated in the full
connected form `|∫ A·A' − (∫A)·(∫A')|`.  Since the truncated slice observables are odd
and the path measure is parity-invariant, the one-point functions vanish
(`asymSliceObsTrunc_pathMeasure_mean_zero`), so inside the proof the connected two-point
reduces to the plain pair correlation; the subtracted product is kept in the statement so
the theorem is self-contained (the standard connected/Ursell form).

## Proof route (no new axioms)

1. **Cyclic reduction.**  `pathMeasure_pair_eq_pathTwoPoint` (the landed cyclic-shift
   change of variables) moves the pair `(t, t')` to `(0, t' − t)`; with the mean-zero
   identity the LHS is `|pathConnectedTwoPoint Ts A B Nt (t'−t)|`.
2. **Definitional envelope/residual split.**  `finitePeriodicBridgeResidual` is *defined*
   as `|pathConnectedTwoPoint| − finitePeriodicPerpEnvelope`, so
   `|conn| = envelope + residual` exactly — no GNS bridge packaging
   (`RemainderHypothesis` / per-contract remainder axiom) is consumed.
3. **Envelope.**  Piece 1 (`norm_sq_proj_obsTrunc_omega_le`) with C2's integrability
   discharge (`asymGroundVector_sliceObs_sq_integrable`) bounds each perpendicular leg by
   `√gSV`, `K`-uniformly; S2 (`asymTransferGap_uniform_fixedLs`) supplies
   `γ = exp(−m₀·a)`, and `γ^d = exp(−m₀·(d·a))` converts sites to physical distance.
4. **Residual.**  The τ-form `K`-uniform axiom
   (`asymFinitePeriodicBridge_remainder_bound_uniform`) bounds the residual by
   `C₂·√gSV·√gSV'·γ^(Nt−⌈τ/a⌉)`; since `⌈τ/a⌉·a ≤ τ + a` and `m₀·a ≤ 1` (shrinking
   `a₀ ≤ min(a₁, 1/m₀)`), the tail is `≤ e·exp(−m₀·(Nt·a − τ))`, and the factor
   `C₂·e` is absorbed into the headline constant `C := 1 + C₂·e`.

## Axiom footprint

Beyond the Lean kernel trio (`propext`, `Classical.choice`, `Quot.sound`), exactly two
project axioms: `asymTransferGap_uniform_fixedLs` (S2) and
`asymFinitePeriodicBridge_remainder_bound_uniform` (τ-residual) — verified with
`#print axioms asymSliceObsTrunc_exponential_clustering_fixedLs` (2026-07-13).

## References

* Glimm–Jaffe, *Quantum Physics*, Ch. 6, 19 (transfer matrix, mass gap, clustering).
* Simon, *The P(φ)₂ Euclidean (Quantum) Field Theory*, Ch. VI.
-/

noncomputable section

open MeasureTheory GaussianField ReflectionPositivity
open scoped BigOperators

namespace Pphi2

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- **Asym exponential clustering in physical distance (fixed `Ls`, a-uniform rate).**

At fixed spatial circumference `Ls` and reference time `τ` there are a physical mass
`m₀ > 0`, a constant `C ≥ 0`, and a spacing threshold `a₀ > 0` such that for every
admissible lattice (`Ns·a = Ls`, `a ≤ a₀`, `2τ ≤ Nt·a`), all spatial profiles `g, g'`,
every truncation `K > 0`, and every pair of slices at separation `0 < (t'−t).val < Nt`,
the path-measure connected two-point function of the truncated slice observables
`A_{g,K} = asymSliceObsTrunc g K` obeys the two-arc physical-distance bound

`|⟨A_{g,K}(ψ_t); A_{g',K}(ψ_{t'})⟩_conn|
   ≤ C·√gSV(g)·√gSV(g')·(e^{−m₀·d·a} + e^{−m₀·(Nt·a − d·a)} + e^{−m₀·(Nt·a − τ)})`

with `d = (t'−t).val` and `gSV = groundSliceVariance`.  The rate `m₀` and the constant
`C` are uniform in `(Nt, Ns, a, g, g', K, t, t')`. -/
theorem asymSliceObsTrunc_exponential_clustering_fixedLs
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (Ls : ℝ) (hLs : 0 < Ls) (τ : ℝ) (hτ : 0 < τ) :
    ∃ m₀ C a₀ : ℝ, 0 < m₀ ∧ 0 ≤ C ∧ 0 < a₀ ∧
    ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (ha : 0 < a),
      (Ns : ℝ) * a = Ls → a ≤ a₀ → 2 * τ ≤ (Nt : ℝ) * a →
      ∀ (g g' : SpatialField Ns) (K : ℝ) (_hK : 0 < K) (t t' : ZMod Nt),
        0 < (t' - t).val → (t' - t).val < Nt →
        |(∫ ψ : ZMod Nt → SpatialField Ns,
            asymSliceObsTrunc g K (ψ t) * asymSliceObsTrunc g' K (ψ t')
            ∂((asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).pathMeasure Nt))
          - (∫ ψ : ZMod Nt → SpatialField Ns, asymSliceObsTrunc g K (ψ t)
              ∂((asymTransferSystem (Nt := Nt) (Ns := Ns)
                  P a mass ha hmass).pathMeasure Nt)) *
            (∫ ψ : ZMod Nt → SpatialField Ns, asymSliceObsTrunc g' K (ψ t')
              ∂((asymTransferSystem (Nt := Nt) (Ns := Ns)
                  P a mass ha hmass).pathMeasure Nt))|
          ≤ C * Real.sqrt (groundSliceVariance (Nt := Nt) (Ns := Ns) P a mass ha hmass g)
              * Real.sqrt (groundSliceVariance (Nt := Nt) (Ns := Ns) P a mass ha hmass g')
              * (Real.exp (-(m₀ * (((t' - t).val : ℝ) * a)))
                + Real.exp (-(m₀ * ((Nt : ℝ) * a - ((t' - t).val : ℝ) * a)))
                + Real.exp (-(m₀ * ((Nt : ℝ) * a - τ)))) := by
  classical
  obtain ⟨m₀, hm₀, a₁, ha₁, hgap⟩ := asymTransferGap_uniform_fixedLs P mass hmass Ls hLs
  obtain ⟨C₂, hC₂, hResAx⟩ :=
    asymFinitePeriodicBridge_remainder_bound_uniform P mass hmass Ls hLs τ hτ
  have hCe : (0 : ℝ) ≤ C₂ * Real.exp 1 := mul_nonneg hC₂ (Real.exp_pos 1).le
  refine ⟨m₀, 1 + C₂ * Real.exp 1, min a₁ (1 / m₀), hm₀, by linarith,
    lt_min ha₁ (by positivity), ?_⟩
  intro Nt Ns _ _ a ha hLsa haa hLta g g' K hK t t' hd0 hdlt
  set d : ZMod Nt := t' - t with hd_def
  -- The S2 gap data at `γ = exp(−m₀·a)`, valid since `a ≤ a₀ ≤ a₁`.
  have haa₁ : a ≤ a₁ := haa.trans (min_le_left _ _)
  have ham : m₀ * a ≤ 1 := by
    have h2 : a ≤ 1 / m₀ := haa.trans (min_le_right _ _)
    rw [le_div_iff₀ hm₀] at h2
    linarith
  set γ : ℝ := Real.exp (-(m₀ * a)) with hγ_def
  have hγ0 : (0 : ℝ) ≤ γ := (Real.exp_pos _).le
  have hγ1 : γ < 1 := by
    have h1 : Real.exp (-(m₀ * a)) < Real.exp 0 :=
      Real.exp_lt_exp.mpr (by nlinarith)
    simpa [hγ_def] using h1
  have hnorm := hgap Nt Ns a ha hLsa haa₁
  -- Site-count powers of `γ` are physical-distance exponentials.
  have hpow_exp : ∀ k : ℕ, γ ^ k = Real.exp (-(m₀ * ((k : ℝ) * a))) := by
    intro k
    rw [hγ_def, ← Real.exp_nat_mul]
    congr 1
    ring
  have hE2 : γ ^ (Nt - d.val) =
      Real.exp (-(m₀ * ((Nt : ℝ) * a - (d.val : ℝ) * a))) := by
    rw [hpow_exp]
    congr 1
    rw [Nat.cast_sub hdlt.le]
    ring
  -- τ-tail bookkeeping: `γ^(Nt−⌈τ/a⌉) ≤ e·exp(−m₀·(Nt·a − τ))` using
  -- `⌈τ/a⌉·a ≤ τ + a` and `m₀·a ≤ 1`.
  have hceil_le : Nat.ceil (τ / a) ≤ Nt := by
    refine Nat.ceil_le.mpr ?_
    rw [div_le_iff₀ ha]
    nlinarith
  have hceil_mul : (Nat.ceil (τ / a) : ℝ) * a ≤ τ + a := by
    have h1 : (Nat.ceil (τ / a) : ℝ) < τ / a + 1 :=
      Nat.ceil_lt_add_one (div_nonneg hτ.le ha.le)
    have h2 : (Nat.ceil (τ / a) : ℝ) * a < (τ / a + 1) * a :=
      mul_lt_mul_of_pos_right h1 ha
    have h3 : (τ / a + 1) * a = τ + a := by field_simp
    linarith
  have hE3 : γ ^ (Nt - Nat.ceil (τ / a)) ≤
      Real.exp 1 * Real.exp (-(m₀ * ((Nt : ℝ) * a - τ))) := by
    rw [hpow_exp, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    rw [Nat.cast_sub hceil_le]
    nlinarith [mul_le_mul_of_nonneg_left hceil_mul hm₀.le]
  -- The one-point functions vanish (parity), so the LHS is the connected two-point
  -- at separation `d` after the cyclic shift.
  have hzero_g : ∫ ψ : ZMod Nt → SpatialField Ns, asymSliceObsTrunc g K (ψ t)
      ∂((asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).pathMeasure Nt) = 0 :=
    asymSliceObsTrunc_pathMeasure_mean_zero (Nt := Nt) (Ns := Ns)
      P a mass ha hmass g hK.le t
  have hzero_g' : ∫ ψ : ZMod Nt → SpatialField Ns, asymSliceObsTrunc g' K (ψ t')
      ∂((asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).pathMeasure Nt) = 0 :=
    asymSliceObsTrunc_pathMeasure_mean_zero (Nt := Nt) (Ns := Ns)
      P a mass ha hmass g' hK.le t'
  have hmeanA : finiteVolumeMean
      (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass)
      (asymSliceObsTruncContract (Ns := Ns) g hK) Nt 0 = 0 :=
    asymSliceObsTrunc_pathMeasure_mean_zero (Nt := Nt) (Ns := Ns)
      P a mass ha hmass g hK.le 0
  have hpair : ∫ ψ : ZMod Nt → SpatialField Ns,
      asymSliceObsTrunc g K (ψ t) * asymSliceObsTrunc g' K (ψ t')
      ∂((asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).pathMeasure Nt) =
      pathConnectedTwoPoint
        (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass)
        (asymSliceObsTruncContract (Ns := Ns) g hK)
        (asymSliceObsTruncContract (Ns := Ns) g' hK) Nt d := by
    unfold pathConnectedTwoPoint
    rw [hmeanA, zero_mul, sub_zero]
    exact pathMeasure_pair_eq_pathTwoPoint
      (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass)
      Nt (asymSliceObsTruncContract (Ns := Ns) g hK)
      (asymSliceObsTruncContract (Ns := Ns) g' hK) t t'
  rw [hzero_g, hzero_g', zero_mul, sub_zero, hpair]
  -- Definitional split: |conn| = envelope + residual.
  have hsplit : |pathConnectedTwoPoint
      (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass)
      (asymSliceObsTruncContract (Ns := Ns) g hK)
      (asymSliceObsTruncContract (Ns := Ns) g' hK) Nt d| =
      finitePeriodicPerpEnvelope
        (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass)
        (asymSliceObsTruncContract (Ns := Ns) g hK)
        (asymSliceObsTruncContract (Ns := Ns) g' hK)
        (asymGappedTransfer Nt Ns P a mass ha hmass γ hγ0 hγ1 hnorm) γ Nt d
      + finitePeriodicBridgeResidual
        (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass)
        (asymSliceObsTruncContract (Ns := Ns) g hK)
        (asymSliceObsTruncContract (Ns := Ns) g' hK)
        (asymGappedTransfer Nt Ns P a mass ha hmass γ hγ0 hγ1 hnorm) γ Nt d := by
    unfold finitePeriodicBridgeResidual
    ring
  rw [hsplit]
  -- Envelope bound: Piece 1 + C2 give the K-uniform `√gSV` legs.
  have hperpA : ‖(asymGappedTransfer Nt Ns P a mass ha hmass γ hγ0 hγ1 hnorm).vacuumPerp
      ((asymSliceObsTruncContract (Ns := Ns) g hK).M
        (asymGappedTransfer Nt Ns P a mass ha hmass γ hγ0 hγ1 hnorm).vacuum)‖ ≤
      Real.sqrt (groundSliceVariance (Nt := Nt) (Ns := Ns) P a mass ha hmass g) := by
    have hsq : ‖(asymGappedTransfer Nt Ns P a mass ha hmass γ hγ0 hγ1 hnorm).vacuumPerp
        ((asymSliceObsTruncContract (Ns := Ns) g hK).M
          (asymGappedTransfer Nt Ns P a mass ha hmass γ hγ0 hγ1 hnorm).vacuum)‖ ^ 2 ≤
        groundSliceVariance (Nt := Nt) (Ns := Ns) P a mass ha hmass g :=
      norm_sq_proj_obsTrunc_omega_le (Nt := Nt) (Ns := Ns) P a mass ha hmass g hK
        (asymGroundVector_sliceObs_sq_integrable Nt Ns P a mass ha hmass g)
    rw [← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt hsq
  have hperpB : ‖(asymGappedTransfer Nt Ns P a mass ha hmass γ hγ0 hγ1 hnorm).vacuumPerp
      ((asymSliceObsTruncContract (Ns := Ns) g' hK).M
        (asymGappedTransfer Nt Ns P a mass ha hmass γ hγ0 hγ1 hnorm).vacuum)‖ ≤
      Real.sqrt (groundSliceVariance (Nt := Nt) (Ns := Ns) P a mass ha hmass g') := by
    have hsq : ‖(asymGappedTransfer Nt Ns P a mass ha hmass γ hγ0 hγ1 hnorm).vacuumPerp
        ((asymSliceObsTruncContract (Ns := Ns) g' hK).M
          (asymGappedTransfer Nt Ns P a mass ha hmass γ hγ0 hγ1 hnorm).vacuum)‖ ^ 2 ≤
        groundSliceVariance (Nt := Nt) (Ns := Ns) P a mass ha hmass g' :=
      norm_sq_proj_obsTrunc_omega_le (Nt := Nt) (Ns := Ns) P a mass ha hmass g' hK
        (asymGroundVector_sliceObs_sq_integrable Nt Ns P a mass ha hmass g')
    rw [← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt hsq
  have hw_nonneg : (0 : ℝ) ≤ γ ^ d.val + γ ^ (Nt - d.val) :=
    add_nonneg (pow_nonneg hγ0 _) (pow_nonneg hγ0 _)
  have henv : finitePeriodicPerpEnvelope
      (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass)
      (asymSliceObsTruncContract (Ns := Ns) g hK)
      (asymSliceObsTruncContract (Ns := Ns) g' hK)
      (asymGappedTransfer Nt Ns P a mass ha hmass γ hγ0 hγ1 hnorm) γ Nt d ≤
      Real.sqrt (groundSliceVariance (Nt := Nt) (Ns := Ns) P a mass ha hmass g) *
        Real.sqrt (groundSliceVariance (Nt := Nt) (Ns := Ns) P a mass ha hmass g') *
        (Real.exp (-(m₀ * ((d.val : ℝ) * a))) +
          Real.exp (-(m₀ * ((Nt : ℝ) * a - (d.val : ℝ) * a)))) := by
    rw [← hpow_exp d.val, ← hE2]
    unfold finitePeriodicPerpEnvelope
    exact mul_le_mul
      (mul_le_mul hperpA hperpB (norm_nonneg _) (Real.sqrt_nonneg _))
      le_rfl hw_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  -- Residual bound via the τ-form K-uniform axiom, instantiated at the two-profile
  -- slice family `fam := (if · = d then g' else g)`.
  have hdne : d ≠ 0 := fun hcon => absurd hd0 (by simp [hcon])
  have hres : finitePeriodicBridgeResidual
      (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass)
      (asymSliceObsTruncContract (Ns := Ns) g hK)
      (asymSliceObsTruncContract (Ns := Ns) g' hK)
      (asymGappedTransfer Nt Ns P a mass ha hmass γ hγ0 hγ1 hnorm) γ Nt d ≤
      C₂ * Real.sqrt (groundSliceVariance (Nt := Nt) (Ns := Ns) P a mass ha hmass g) *
        Real.sqrt (groundSliceVariance (Nt := Nt) (Ns := Ns) P a mass ha hmass g') *
        γ ^ (Nt - Nat.ceil (τ / a)) := by
    have h := hResAx Nt Ns a ha hLsa hLta hγ0 hγ1 hnorm
      (fun s : ZMod Nt => if s = d then g' else g) K hK 0 d d hd0 hdlt
    have hfam0 : (fun s : ZMod Nt => if s = d then g' else g) 0 = g := by
      simp only [if_neg (fun hcon : (0 : ZMod Nt) = d => hdne hcon.symm)]
    have hfamd : (fun s : ZMod Nt => if s = d then g' else g) d = g' := by
      simp
    rwa [hfam0, hfamd] at h
  -- Combine, absorbing `C₂·e` into `C = 1 + C₂·e`.
  have hres' : finitePeriodicBridgeResidual
      (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass)
      (asymSliceObsTruncContract (Ns := Ns) g hK)
      (asymSliceObsTruncContract (Ns := Ns) g' hK)
      (asymGappedTransfer Nt Ns P a mass ha hmass γ hγ0 hγ1 hnorm) γ Nt d ≤
      C₂ * Real.sqrt (groundSliceVariance (Nt := Nt) (Ns := Ns) P a mass ha hmass g) *
        Real.sqrt (groundSliceVariance (Nt := Nt) (Ns := Ns) P a mass ha hmass g') *
        (Real.exp 1 * Real.exp (-(m₀ * ((Nt : ℝ) * a - τ)))) :=
    hres.trans (mul_le_mul_of_nonneg_left hE3
      (mul_nonneg (mul_nonneg hC₂ (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)))
  have hsA : (0 : ℝ) ≤
      Real.sqrt (groundSliceVariance (Nt := Nt) (Ns := Ns) P a mass ha hmass g) :=
    Real.sqrt_nonneg _
  have hsB : (0 : ℝ) ≤
      Real.sqrt (groundSliceVariance (Nt := Nt) (Ns := Ns) P a mass ha hmass g') :=
    Real.sqrt_nonneg _
  have hE1n : (0 : ℝ) ≤ Real.exp (-(m₀ * ((d.val : ℝ) * a))) := (Real.exp_pos _).le
  have hE2n : (0 : ℝ) ≤ Real.exp (-(m₀ * ((Nt : ℝ) * a - (d.val : ℝ) * a))) :=
    (Real.exp_pos _).le
  have hE3n : (0 : ℝ) ≤ Real.exp (-(m₀ * ((Nt : ℝ) * a - τ))) := (Real.exp_pos _).le
  have hint1 : (0 : ℝ) ≤ C₂ * Real.exp 1 *
      (Real.sqrt (groundSliceVariance (Nt := Nt) (Ns := Ns) P a mass ha hmass g) *
        (Real.sqrt (groundSliceVariance (Nt := Nt) (Ns := Ns) P a mass ha hmass g') *
          Real.exp (-(m₀ * ((d.val : ℝ) * a))))) :=
    mul_nonneg hCe (mul_nonneg hsA (mul_nonneg hsB hE1n))
  have hint2 : (0 : ℝ) ≤ C₂ * Real.exp 1 *
      (Real.sqrt (groundSliceVariance (Nt := Nt) (Ns := Ns) P a mass ha hmass g) *
        (Real.sqrt (groundSliceVariance (Nt := Nt) (Ns := Ns) P a mass ha hmass g') *
          Real.exp (-(m₀ * ((Nt : ℝ) * a - (d.val : ℝ) * a))))) :=
    mul_nonneg hCe (mul_nonneg hsA (mul_nonneg hsB hE2n))
  have hint3 : (0 : ℝ) ≤
      Real.sqrt (groundSliceVariance (Nt := Nt) (Ns := Ns) P a mass ha hmass g) *
        (Real.sqrt (groundSliceVariance (Nt := Nt) (Ns := Ns) P a mass ha hmass g') *
          Real.exp (-(m₀ * ((Nt : ℝ) * a - τ)))) :=
    mul_nonneg hsA (mul_nonneg hsB hE3n)
  linarith [henv, hres']

end Pphi2

end
