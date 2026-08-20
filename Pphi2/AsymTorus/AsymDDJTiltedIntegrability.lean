/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Polynomial moments under a source tilt

The weighted source estimate at exponent `P.n / (P.n - 1)` gives an
exponential bound for the doubled source.  This file records the elementary
consequence that the `P.n`-th source moment is integrable under the normalized
tilt by the original source exponent.
-/

import Pphi2.AsymTorus.AsymDDJSource
import Pphi2.GeneralResults.TiltPressureMoment

noncomputable section

open GaussianField MeasureTheory

namespace Pphi2

/-! ## Scaling of the cell-weighted source power -/

theorem asymWeightedLpPow_smul
    {Nt Ns : ℕ} [NeZero Nt] [NeZero Ns]
    (p a c : ℝ) (h : AsymLatticeField Nt Ns) :
    asymWeightedLpPow p a (c • h) =
      Real.rpow |c| p * asymWeightedLpPow p a h := by
  unfold asymWeightedLpPow
  calc
    a ^ 2 * ∑ x : AsymLatticeSites Nt Ns,
        Real.rpow |(c • h) x| p =
      a ^ 2 * ∑ x : AsymLatticeSites Nt Ns,
        Real.rpow |c| p * Real.rpow |h x| p := by
      apply congrArg (fun s : ℝ => a ^ 2 * s)
      apply Finset.sum_congr rfl
      intro x hx
      rw [Pi.smul_apply, smul_eq_mul, abs_mul]
      change (|c| * |h x|) ^ p = |c| ^ p * |h x| ^ p
      exact Real.mul_rpow (abs_nonneg c) (abs_nonneg (h x))
    _ = Real.rpow |c| p *
        (a ^ 2 * ∑ x : AsymLatticeSites Nt Ns,
          Real.rpow |h x| p) := by
      calc
        a ^ 2 * ∑ x : AsymLatticeSites Nt Ns,
            Real.rpow |c| p * Real.rpow |h x| p =
          ∑ x : AsymLatticeSites Nt Ns,
            a ^ 2 * (Real.rpow |c| p * Real.rpow |h x| p) := by
          rw [Finset.mul_sum]
        _ = ∑ x : AsymLatticeSites Nt Ns,
            Real.rpow |c| p * (a ^ 2 * Real.rpow |h x| p) := by
          apply Finset.sum_congr rfl
          intro x hx
          ring
        _ = Real.rpow |c| p *
            ∑ x : AsymLatticeSites Nt Ns,
              a ^ 2 * Real.rpow |h x| p := by
          rw [← Finset.mul_sum]
        _ = Real.rpow |c| p *
            (a ^ 2 * ∑ x : AsymLatticeSites Nt Ns,
              Real.rpow |h x| p) := by
          rw [Finset.mul_sum]

/-! ## The finite tilted-moment consumer -/

/-- A stronger weighted source ball gives integrability of the source power
under the normalized exponential tilt by that same source power.

The proof obtains integrability of the doubled source exponential from the
finite weighted-source theorem.  Since `P.n` is even, the source exponent is
nonnegative.  The elementary bound
`x^n exp (x^n/n) ≤ n exp (2^n x^n/n)` then transfers integrability through
`integrable_tilted_iff`.
-/
theorem interactingLatticeMeasureAsym_tilted_integrable_pow_of_weightedLpPow
    (Lt Ls : ℝ) [Fact (0 < Lt)] [Fact (0 < Ls)]
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (f : AsymTorusTestFunction Lt Ls)
    (hLp :
      asymWeightedLpPow
          ((P.n : ℝ) / ((P.n : ℝ) - 1)) a
          (asymRawSource a
            (asymLatticeTestFnIso Lt Ls Nt Ns a f)) ≤
        (1 / 4 : ℝ) ^ ((P.n : ℝ) / ((P.n : ℝ) - 1))) :
    Integrable
      (fun ω : Configuration (AsymLatticeField Nt Ns) =>
        (ω (asymLatticeTestFnIso Lt Ls Nt Ns a f)) ^ P.n)
      ((interactingLatticeMeasureAsym Nt Ns P a mass ha hmass).tilted
        (fun ω : Configuration (AsymLatticeField Nt Ns) =>
          (ω (asymLatticeTestFnIso Lt Ls Nt Ns a f)) ^ P.n /
            (P.n : ℝ))) := by
  let μ := interactingLatticeMeasureAsym Nt Ns P a mass ha hmass
  let g : AsymLatticeField Nt Ns :=
    asymLatticeTestFnIso Lt Ls Nt Ns a f
  let p : ℝ := (P.n : ℝ) / ((P.n : ℝ) - 1)
  have hn_nat : 1 < P.n := by
    have h := P.hn_ge
    omega
  have hn_pos : 0 < (P.n : ℝ) := by
    have : 0 < P.n := by omega
    exact_mod_cast this
  have hn_real : 1 < (P.n : ℝ) := by
    exact_mod_cast hn_nat
  have hp_pos : 0 < p := by
    dsimp [p]
    exact div_pos hn_pos (sub_pos.mpr hn_real)
  have hLp2 :
      asymWeightedLpPow p a
          (asymRawSource a
            (asymLatticeTestFnIso Lt Ls Nt Ns a ((2 : ℝ) • f))) ≤
        (1 / 2 : ℝ) ^ p := by
    have hmap :
        asymLatticeTestFnIso Lt Ls Nt Ns a ((2 : ℝ) • f) = (2 : ℝ) • g := by
      funext x
      simp [g, asymLatticeTestFnIso, evalAsymTorusAtSiteGJ_apply,
        map_smul, Pi.smul_apply, smul_eq_mul] <;> ring
    have hraw :
        asymRawSource a
            (asymLatticeTestFnIso Lt Ls Nt Ns a ((2 : ℝ) • f)) =
          (2 : ℝ) • asymRawSource a g := by
      rw [hmap]
      unfold asymRawSource
      simp only [smul_smul]
      congr 1
      ring
    rw [hraw, asymWeightedLpPow_smul]
    simp only [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hbase :
        Real.rpow (2 : ℝ) p * asymWeightedLpPow p a
            (asymRawSource a g) ≤
          Real.rpow (2 : ℝ) p * (1 / 4 : ℝ) ^ p := by
      exact mul_le_mul_of_nonneg_left
        (by simpa [p, g] using hLp) (Real.rpow_nonneg (by norm_num) _)
    calc
      Real.rpow (2 : ℝ) p * asymWeightedLpPow p a
          (asymRawSource a g) ≤
          Real.rpow (2 : ℝ) p * (1 / 4 : ℝ) ^ p := hbase
      _ = (1 / 2 : ℝ) ^ p := by
        rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
          (by norm_num : (0 : ℝ) ≤ 1 / 4)]
        norm_num

  have hLp_half :
      asymWeightedLpPow p a
          (asymRawSource a g) ≤ (1 / 2 : ℝ) ^ p := by
    calc
      asymWeightedLpPow p a (asymRawSource a g) ≤
          (1 / 4 : ℝ) ^ p := by simpa [p, g] using hLp
      _ ≤ (1 / 2 : ℝ) ^ p := by
        exact Real.rpow_le_rpow (by norm_num) (by norm_num) hp_pos.le

  have h_exp2_raw :=
    interactingLatticeMeasureAsym_integrable_exp_of_weightedLpPow
      Lt Ls Nt Ns P a mass ha hmass ((2 : ℝ) • f) hLp2
  have h_exp2 :
      Integrable
        (fun ω : Configuration (AsymLatticeField Nt Ns) =>
          Real.exp (((2 : ℝ) ^ P.n) *
            ((ω g) ^ P.n / (P.n : ℝ)))) μ := by
    have h_eq :
        (fun ω : Configuration (AsymLatticeField Nt Ns) =>
            Real.exp (((2 : ℝ) ^ P.n) *
              ((ω g) ^ P.n / (P.n : ℝ)))) =
        (fun ω : Configuration (AsymLatticeField Nt Ns) =>
            Real.exp ((ω (asymLatticeTestFnIso Lt Ls Nt Ns a
                ((2 : ℝ) • f))) ^ P.n / (P.n : ℝ))) := by
      funext ω
      congr 1
      have hmap :
          asymLatticeTestFnIso Lt Ls Nt Ns a ((2 : ℝ) • f) = (2 : ℝ) • g := by
        funext x
        simp [g, asymLatticeTestFnIso, evalAsymTorusAtSiteGJ_apply,
          map_smul, Pi.smul_apply, smul_eq_mul] <;> ring
      rw [hmap, map_smul, smul_eq_mul, mul_pow]
      dsimp [g]
      ring
    rw [h_eq]
    simpa [μ] using h_exp2_raw

  have h_exp_raw :=
    interactingLatticeMeasureAsym_integrable_exp_of_weightedLpPow
      Lt Ls Nt Ns P a mass ha hmass f hLp_half
  have h_exp :
      Integrable
        (fun ω : Configuration (AsymLatticeField Nt Ns) =>
          Real.exp ((ω g) ^ P.n / (P.n : ℝ))) μ := by
    simpa [μ, g] using h_exp_raw

  let X : Configuration (AsymLatticeField Nt Ns) → ℝ :=
    fun ω => (ω g) ^ P.n
  let F : Configuration (AsymLatticeField Nt Ns) → ℝ :=
    fun ω => X ω / (P.n : ℝ)
  have h_exp_F : Integrable (fun ω => Real.exp (F ω)) μ := by
    simpa [X, F] using h_exp
  have htilt :=
    (integrable_tilted_iff (μ := μ) (f := F) h_exp_F X)
  apply htilt.mpr
  have hX_meas : Measurable X := by
    dsimp [X]
    exact (configuration_eval_measurable g).pow_const P.n
  have hF_meas : Measurable F := by
    dsimp [F]
    exact hX_meas.div measurable_const
  have htarget_meas :
      AEStronglyMeasurable (fun ω => Real.exp (F ω) • X ω) μ := by
    simpa only [smul_eq_mul] using
      (hF_meas.exp.mul hX_meas).aestronglyMeasurable
  have h_exp2_scaled : Integrable
      (fun ω => (P.n : ℝ) *
        Real.exp (((2 : ℝ) ^ P.n) * F ω)) μ :=
    h_exp2.const_mul (P.n : ℝ)
  refine Integrable.mono'
    (g := fun ω => (P.n : ℝ) *
      Real.exp (((2 : ℝ) ^ P.n) * F ω)) h_exp2_scaled ?_ ?_
  · simpa [smul_eq_mul] using htarget_meas
  · filter_upwards [] with ω
    have hX_nonneg : 0 ≤ X ω := by
      dsimp [X]
      exact P.hn_even.pow_nonneg _
    have hF_nonneg : 0 ≤ F ω := by
      dsimp [F]
      exact div_nonneg hX_nonneg hn_pos.le
    have hF_le_exp : F ω ≤ Real.exp (F ω) := by
      have h := Real.add_one_le_exp (F ω)
      linarith
    have hX_le : X ω ≤ (P.n : ℝ) * Real.exp (F ω) := by
      have hmul := mul_le_mul_of_nonneg_left hF_le_exp hn_pos.le
      have hXF : (P.n : ℝ) * F ω = X ω := by
        dsimp [F]
        field_simp [hn_pos.ne'] <;> ring
      rw [hXF] at hmul
      exact hmul
    have h2n : (2 : ℝ) ≤ (2 : ℝ) ^ P.n := by
      have hpow := pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num)
        (show 1 ≤ P.n by omega)
      simpa using hpow
    have h2F : 2 * F ω ≤ (2 : ℝ) ^ P.n * F ω := by
      exact mul_le_mul_of_nonneg_right h2n hF_nonneg
    have hexp : Real.exp (2 * F ω) ≤
        Real.exp (((2 : ℝ) ^ P.n) * F ω) :=
      Real.exp_le_exp.mpr h2F
    calc
      ‖Real.exp (F ω) • X ω‖ =
          Real.exp (F ω) * X ω := by
        rw [smul_eq_mul, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hX_nonneg)]
      _ ≤ Real.exp (F ω) * ((P.n : ℝ) * Real.exp (F ω)) :=
        mul_le_mul_of_nonneg_left hX_le (Real.exp_pos _).le
      _ = (P.n : ℝ) * Real.exp (F ω + F ω) := by
        calc
          Real.exp (F ω) * ((P.n : ℝ) * Real.exp (F ω)) =
              (P.n : ℝ) * (Real.exp (F ω) * Real.exp (F ω)) := by ring
          _ = (P.n : ℝ) * Real.exp (F ω + F ω) := by
            rw [← Real.exp_add]
      _ = (P.n : ℝ) * Real.exp (2 * F ω) := by
        congr 2
        ring
      _ ≤ (P.n : ℝ) *
          Real.exp (((2 : ℝ) ^ P.n) * F ω) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)

end Pphi2
