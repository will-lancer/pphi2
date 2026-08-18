/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Uniform Exponential Moment Bound for Cylinder Pullback

Provides the uniform-in-Lt exponential moment bound
`E_{ν_Lt}[exp(|ω(f)|)] ≤ K · exp(C · q(f)²)` needed for OS0 analyticity.

This is pulled through from the AsymTorus Nelson/Fröhlich bound via
the cylinder-to-torus embedding.

## Mathematical background

The torus interacting measure satisfies (from `asymTorusInteracting_exponentialMomentBound`):
  `E_{μ_Lt}[exp(|ω(g)|)] ≤ K · exp(σ²_Lt(g))`

For `g = embed(f)` where `f` is a cylinder test function:
  `σ²_Lt(embed f) ≤ C · q(f)²`  (from the method of images bound)

Combined: `E_{ν_Lt}[exp(|ω(f)|)] ≤ K · exp(C · q(f)²)` uniformly in Lt.

Together with bounded-continuous convergence of the extracted limit, this is
sufficient for the dominated integral proof of OS0 analyticity.
-/

import Pphi2.AsymTorus.MomentBoundOS1

noncomputable section

namespace Pphi2

open GaussianField MeasureTheory Filter

variable (Ls : ℝ) [hLs : Fact (0 < Ls)]

/-- Uniform exponential moment bound for the cylinder pullback measures.

For any cylinder test function `f`, the exponential moment under the
pulled-back torus interacting measure is bounded uniformly in Lt:

  `∫ exp(|ω(f)|) dν_Lt ≤ K · exp(C · q(f)²)`

where `q` is a continuous seminorm on `CylinderTestFunction Ls` and
`K, C > 0` are constants independent of `f` and `Lt`.

This theorem deliberately keeps the needed analytic input explicit. The
abstract `AsymSatisfiesTorusOS.os1` clause has a bound by an unspecified
continuous seminorm, which is too weak to imply uniformity as `Lt → ∞`.
Assuming instead the Green-controlled bound `MeasureHasGreenMomentBound` with
constants uniform in `Lt`, `cylinderPullback_expMoment_uniform_bound` composes
that input with the method-of-images estimate. -/
theorem cylinderIR_uniform_exponential_moment
    (mass : ℝ) (hmass : 0 < mass)
    (KG CG : ℝ) (hKG_pos : 0 < KG) (hCG_pos : 0 < CG) :
    ∃ (K C : ℝ) (q : Seminorm ℝ (CylinderTestFunction Ls)),
    0 < K ∧ 0 < C ∧ Continuous q ∧
    ∀ (Lt : ℝ) [Fact (0 < Lt)] (_ : 1 ≤ Lt)
      (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
      [IsProbabilityMeasure μ]
      (_ : MeasureHasGreenMomentBound Ls mass hmass KG CG μ)
      (f : CylinderTestFunction Ls),
    Integrable (fun ω : Configuration (CylinderTestFunction Ls) =>
      Real.exp (|ω f|)) (cylinderPullbackMeasure Lt Ls μ) ∧
    ∫ ω : Configuration (CylinderTestFunction Ls),
      Real.exp (|ω f|) ∂(cylinderPullbackMeasure Lt Ls μ) ≤
    K * Real.exp (C * q f ^ 2) := by
  obtain ⟨K, C, q, hK, hC, hq_cont, hbound⟩ :=
    cylinderPullback_expMoment_uniform_bound Ls mass hmass KG CG hKG_pos hCG_pos
  refine ⟨K, C, q, hK, hC, hq_cont, ?_⟩
  intro Lt _ hLt μ _ hμ_green f
  exact hbound Lt hLt μ hμ_green f

/-- A direct exponential-moment bound on a torus measure after pullback to the
cylinder.  This is the source-independent interface used by the IR limit:
the constants and continuous seminorm can be supplied by a Green comparison,
by a finite-lattice estimate, or by another honest analytic input. -/
def MeasureHasCylinderExpMomentBound
    {Lt : ℝ} [Fact (0 < Lt)]
    (K C : ℝ) (q : Seminorm ℝ (CylinderTestFunction Ls))
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls))) : Prop :=
  ∀ f : CylinderTestFunction Ls,
    Integrable (fun ω : Configuration (CylinderTestFunction Ls) =>
      Real.exp (|ω f|)) (cylinderPullbackMeasure Lt Ls μ) ∧
    ∫ ω : Configuration (CylinderTestFunction Ls),
      Real.exp (|ω f|) ∂(cylinderPullbackMeasure Lt Ls μ) ≤
    K * Real.exp (C * q f ^ 2)

/-- A local exponential moment bound for an even polynomial degree.

The local bound is stated on the cylinder configuration space itself.  It is
the form supplied by a local `P(Φ)₂` estimate: on the seminorm ball
`q f ≤ r`, the normalized degree-`n` exponential has moment at most `2`.
The parity and lower-bound hypotheses on `n`, together with positivity of
`r`, are kept as hypotheses of the adapter below so that this predicate can
also be used by source-specific producers without carrying redundant proof
fields in every instance. -/
def MeasureHasLocalCylinderNthExpMomentBound
    (n : ℕ) (r : ℝ) (q : Seminorm ℝ (CylinderTestFunction Ls))
    (ν : Measure (Configuration (CylinderTestFunction Ls))) : Prop :=
  ∀ f : CylinderTestFunction Ls, q f ≤ r →
    Integrable (fun ω : Configuration (CylinderTestFunction Ls) =>
      Real.exp ((ω f) ^ n / (n : ℝ))) ν ∧
    ∫ ω : Configuration (CylinderTestFunction Ls),
      Real.exp ((ω f) ^ n / (n : ℝ)) ∂ν ≤ 2

/-- Elementary polynomial Young bound used by the local-to-global adapter.

For `t ≥ 1` and `y ≥ 0`, the degree-`n` term absorbs the linear term.  The
extra `1 / n` makes the estimate uniform across the small-`y` region. -/
private lemma local_nth_young
    (n : ℕ) (hn_even : Even n) (hn4 : 4 ≤ n)
    {t y : ℝ} (ht : 1 ≤ t) (hy : 0 ≤ y) :
    t * y ≤ y ^ n / (n : ℝ) + (n : ℝ) / 4 * t ^ 2 + 1 / (n : ℝ) := by
  have hn_pos : 0 < n := by omega
  have hnR_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  obtain ⟨k, hk⟩ := hn_even
  have hk2 : 2 ≤ k := by omega
  have ht0 : 0 ≤ t := by linarith
  by_cases hy1 : y ≤ 1
  · have hty : t * y ≤ t := by
      have h := mul_le_mul_of_nonneg_left hy1 ht0
      simpa using h
    have ht_sq : t ≤ t ^ 2 := by
      have hprod : 0 ≤ (t - 1) * t :=
        mul_nonneg (sub_nonneg.mpr ht) ht0
      nlinarith
    have hn4R : (1 : ℝ) ≤ (n : ℝ) / 4 := by
      have hn4R' : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
      nlinarith
    have ht_bound : t ≤ (n : ℝ) / 4 * t ^ 2 := by
      have hprod : 0 ≤ ((n : ℝ) / 4 - 1) * t ^ 2 :=
        mul_nonneg (sub_nonneg.mpr hn4R) (sq_nonneg t)
      nlinarith
    calc
      t * y ≤ t := hty
      _ ≤ (n : ℝ) / 4 * t ^ 2 := ht_bound
      _ ≤ y ^ n / (n : ℝ) + (n : ℝ) / 4 * t ^ 2 + 1 / (n : ℝ) := by
        have hy_pow : 0 ≤ y ^ n / (n : ℝ) :=
          div_nonneg (pow_nonneg hy n) hnR_pos.le
        have hn_inv : 0 ≤ 1 / (n : ℝ) := by positivity
        linarith
  · have hy1' : 1 ≤ y := le_of_lt (lt_of_not_ge hy1)
    have hyk : y ≤ y ^ k := by
      have hpow : y ^ (1 : ℕ) ≤ y ^ k :=
        pow_le_pow_right₀ hy1' (by omega)
      simpa using hpow
    let b : ℝ := y ^ k
    have htb : t * y ≤ t * b :=
      mul_le_mul_of_nonneg_left hyk ht0
    have hsq : 0 ≤ (2 * b - (n : ℝ) * t) ^ 2 := sq_nonneg _
    have hyoung : t * b ≤ b ^ 2 / (n : ℝ) + (n : ℝ) / 4 * t ^ 2 := by
      calc
        t * b ≤
            (b ^ 2 + (n : ℝ) ^ 2 / 4 * t ^ 2) / (n : ℝ) := by
          apply (le_div_iff₀ hnR_pos).2
          nlinarith [hsq]
        _ = b ^ 2 / (n : ℝ) + (n : ℝ) / 4 * t ^ 2 := by
          have hnR_ne : (n : ℝ) ≠ 0 := ne_of_gt hnR_pos
          field_simp [hnR_ne] <;> ring
    have hb_sq : b ^ 2 = y ^ n := by
      dsimp [b]
      rw [← pow_mul]
      congr 1
      omega
    calc
      t * y ≤ t * b := htb
      _ ≤ b ^ 2 / (n : ℝ) + (n : ℝ) / 4 * t ^ 2 := hyoung
      _ = y ^ n / (n : ℝ) + (n : ℝ) / 4 * t ^ 2 := by rw [hb_sq]
      _ ≤ y ^ n / (n : ℝ) + (n : ℝ) / 4 * t ^ 2 + 1 / (n : ℝ) := by
        have hn_inv : 0 ≤ 1 / (n : ℝ) := by positivity
        linarith

/-- Convert a local even-degree cylinder estimate into the quadratic
exponential-moment interface consumed by the existing IR and OS adapters.

For an arbitrary `f`, put `t = max 1 (q f / r)` and `λ = 1 / t`.  Then
`λ • f` lies in the local ball and
`|ω f| = t |ω (λ • f)|`.  Applying `local_nth_young` and integrating gives
the safe constants
`K = 2 exp(n / 4 + 1 / n)` and `C = n / (4 r²)`.
-/
theorem measureHasCylinderExpMomentBound_of_localNth
    (n : ℕ) (hn_even : Even n) (hn4 : 4 ≤ n)
    (r : ℝ) (hr : 0 < r)
    (q : Seminorm ℝ (CylinderTestFunction Ls))
    {Lt : ℝ} [Fact (0 < Lt)]
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    (hlocal : MeasureHasLocalCylinderNthExpMomentBound Ls n r q
      (cylinderPullbackMeasure Lt Ls μ)) :
    MeasureHasCylinderExpMomentBound Ls
      (2 * Real.exp ((n : ℝ) / 4 + 1 / (n : ℝ)))
      ((n : ℝ) / (4 * r ^ 2)) q μ := by
  unfold MeasureHasCylinderExpMomentBound
  intro f
  let s : ℝ := q f
  have hs : 0 ≤ s := by
    dsimp [s]
    exact apply_nonneg q f
  let t : ℝ := max 1 (s / r)
  have ht1 : 1 ≤ t := by
    dsimp [t]
    exact le_max_left _ _
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  let lam : ℝ := 1 / t
  have hlam_pos : 0 < lam := by
    dsimp [lam]
    exact one_div_pos.mpr ht_pos
  have hsr : s / r ≤ t := by
    dsimp [t]
    exact le_max_right _ _
  have hs_le : s ≤ r * t := by
    have h := (div_le_iff₀ hr).1 hsr
    nlinarith
  have hq_lam : q (lam • f) ≤ r := by
    have hq_eq : q (lam • f) = s / t := by
      rw [map_smul_eq_mul q lam f, Real.norm_eq_abs, abs_of_pos hlam_pos]
      dsimp [lam, s]
      rw [one_div]
      ring
    rw [hq_eq]
    exact (div_le_iff₀ ht_pos).2 (by nlinarith [hs_le])
  unfold MeasureHasLocalCylinderNthExpMomentBound at hlocal
  obtain ⟨hlocal_int, hlocal_bound⟩ := hlocal (lam • f) hq_lam
  have h_eval : ∀ ω : Configuration (CylinderTestFunction Ls),
      ω (lam • f) = lam * ω f := by
    intro ω
    simp [map_smul]
  have h_recover : ∀ ω : Configuration (CylinderTestFunction Ls),
      t * ω (lam • f) = ω f := by
    intro ω
    calc
      t * ω (lam • f) = t * (lam * ω f) := by rw [h_eval ω]
      _ = (t * (1 / t)) * ω f := by
        dsimp [lam]
        ring
      _ = ω f := by
        rw [one_div, mul_inv_cancel₀ (ne_of_gt ht_pos), one_mul]
  let A : ℝ := Real.exp ((n : ℝ) / 4 * t ^ 2 + 1 / (n : ℝ))
  have h_point : ∀ ω : Configuration (CylinderTestFunction Ls),
      Real.exp (|ω f|) ≤
        A * Real.exp ((ω (lam • f)) ^ n / (n : ℝ)) := by
    intro ω
    have hyoung := local_nth_young n hn_even hn4 ht1 (abs_nonneg (ω (lam • f)))
    have harg : |ω f| ≤
        ((n : ℝ) / 4 * t ^ 2 + 1 / (n : ℝ)) +
          (ω (lam • f)) ^ n / (n : ℝ) := by
      calc
        |ω f| = t * |ω (lam • f)| := by
          calc
            |ω f| = |t * ω (lam • f)| :=
              congrArg abs (h_recover ω).symm
            _ = |t| * |ω (lam • f)| := by rw [abs_mul]
            _ = t * |ω (lam • f)| := by rw [abs_of_nonneg ht1.le]
        _ ≤ |ω (lam • f)| ^ n / (n : ℝ) +
              (n : ℝ) / 4 * t ^ 2 + 1 / (n : ℝ) := hyoung
        _ = ((n : ℝ) / 4 * t ^ 2 + 1 / (n : ℝ)) +
              (ω (lam • f)) ^ n / (n : ℝ) := by
          rw [hn_even.pow_abs]
          ring
    dsimp [A]
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr harg
  have h_dom_int : Integrable
      (fun ω : Configuration (CylinderTestFunction Ls) =>
        A * Real.exp ((ω (lam • f)) ^ n / (n : ℝ)))
      (cylinderPullbackMeasure Lt Ls μ) := hlocal_int.const_mul A
  have h_target_meas : AEStronglyMeasurable
      (fun ω : Configuration (CylinderTestFunction Ls) => Real.exp (|ω f|))
      (cylinderPullbackMeasure Lt Ls μ) :=
    ((configuration_eval_measurable f).abs.exp).aestronglyMeasurable
  have h_target_int : Integrable
      (fun ω : Configuration (CylinderTestFunction Ls) => Real.exp (|ω f|))
      (cylinderPullbackMeasure Lt Ls μ) := by
    refine h_dom_int.mono' h_target_meas (ae_of_all _ fun ω => ?_)
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)]
    exact h_point ω
  have h_integral_le :
      ∫ ω : Configuration (CylinderTestFunction Ls), Real.exp (|ω f|)
          ∂(cylinderPullbackMeasure Lt Ls μ) ≤
        ∫ ω : Configuration (CylinderTestFunction Ls),
          A * Real.exp ((ω (lam • f)) ^ n / (n : ℝ))
            ∂(cylinderPullbackMeasure Lt Ls μ) := by
    apply integral_mono_of_nonneg
    · exact ae_of_all _ (fun ω => (Real.exp_pos _).le)
    · exact h_dom_int
    · exact ae_of_all _ h_point
  have h_integral_bound :
      ∫ ω : Configuration (CylinderTestFunction Ls), Real.exp (|ω f|)
          ∂(cylinderPullbackMeasure Lt Ls μ) ≤ 2 * A := by
    calc
      ∫ ω : Configuration (CylinderTestFunction Ls), Real.exp (|ω f|)
          ∂(cylinderPullbackMeasure Lt Ls μ) ≤
          ∫ ω : Configuration (CylinderTestFunction Ls),
            A * Real.exp ((ω (lam • f)) ^ n / (n : ℝ))
              ∂(cylinderPullbackMeasure Lt Ls μ) := h_integral_le
      _ = A * (∫ ω : Configuration (CylinderTestFunction Ls),
            Real.exp ((ω (lam • f)) ^ n / (n : ℝ))
              ∂(cylinderPullbackMeasure Lt Ls μ)) := by
        rw [integral_const_mul]
      _ ≤ A * 2 :=
        mul_le_mul_of_nonneg_left hlocal_bound (Real.exp_pos _).le
      _ = 2 * A := by ring
  have ht_sq_le : t ^ 2 ≤ 1 + (s / r) ^ 2 := by
    by_cases h : 1 ≤ s / r
    · dsimp [t]
      rw [max_eq_right h]
      nlinarith [sq_nonneg (s / r)]
    · have h' : s / r ≤ 1 := le_of_not_ge h
      dsimp [t]
      rw [max_eq_left h']
      nlinarith [sq_nonneg (s / r)]
  have h_arg_bound :
      (n : ℝ) / 4 * t ^ 2 + 1 / (n : ℝ) ≤
        ((n : ℝ) / 4 + 1 / (n : ℝ)) +
          ((n : ℝ) / (4 * r ^ 2)) * s ^ 2 := by
    calc
      (n : ℝ) / 4 * t ^ 2 + 1 / (n : ℝ) ≤
          (n : ℝ) / 4 * (1 + (s / r) ^ 2) + 1 / (n : ℝ) := by
            exact add_le_add_right
              (mul_le_mul_of_nonneg_left ht_sq_le (by positivity)) _
      _ = ((n : ℝ) / 4 + 1 / (n : ℝ)) +
          ((n : ℝ) / (4 * r ^ 2)) * s ^ 2 := by
            have hnR_pos : (0 : ℝ) < (n : ℝ) := by
              exact_mod_cast (show 0 < n by omega)
            have hnR_ne : (n : ℝ) ≠ 0 := ne_of_gt hnR_pos
            have hr_ne : r ≠ 0 := ne_of_gt hr
            have hr2_ne : r ^ 2 ≠ 0 := pow_ne_zero 2 hr_ne
            field_simp [hnR_ne, hr_ne, hr2_ne] <;> ring
  have hA_bound : A ≤
      Real.exp (((n : ℝ) / 4 + 1 / (n : ℝ)) +
        ((n : ℝ) / (4 * r ^ 2)) * s ^ 2) := by
    dsimp [A]
    exact Real.exp_le_exp.mpr h_arg_bound
  have h_final : 2 * A ≤
      (2 * Real.exp ((n : ℝ) / 4 + 1 / (n : ℝ))) *
        Real.exp (((n : ℝ) / (4 * r ^ 2)) * s ^ 2) := by
    calc
      2 * A ≤ 2 * Real.exp (((n : ℝ) / 4 + 1 / (n : ℝ)) +
          ((n : ℝ) / (4 * r ^ 2)) * s ^ 2) :=
        mul_le_mul_of_nonneg_left hA_bound (by norm_num)
      _ = (2 * Real.exp ((n : ℝ) / 4 + 1 / (n : ℝ))) *
          Real.exp (((n : ℝ) / (4 * r ^ 2)) * s ^ 2) := by
        rw [Real.exp_add]
        ring
  refine ⟨h_target_int, ?_⟩
  simpa [s] using h_integral_bound.trans h_final

/-- Elementary inequality `x² ≤ 2 e^|x|`, used to extract a polynomial
    moment from the exponential moment. -/
private lemma sq_le_two_mul_exp_abs (x : ℝ) : x ^ 2 ≤ 2 * Real.exp |x| := by
  have h := Real.quadratic_le_exp_of_nonneg (abs_nonneg x)
  have hx_nn : 0 ≤ |x| := abs_nonneg x
  have h_sq : |x| ^ 2 ≤ 2 * Real.exp |x| := by linarith [h, hx_nn]
  rwa [sq_abs] at h_sq

/-- **Uniform second moment bound** for cylinder pullback measures.

For each fixed cylinder test function `f`, the second moment under the
pulled-back torus interacting measure is finite, and is bounded
**uniformly in `Lt ≥ 1`** by the additive expression
  `∫ (ω f)² dν_{Lt} ≤ C₁ · q(f)² + C₂`,
where `C₁, C₂ > 0` and the seminorm `q` are independent of `Lt` and `f`.

The bound is **per-f** (not a uniform Hilbertian-seminorm bound in the
Mitoma sense) and the additive `C₂` is **essential** to the scaling
argument used here — the strict multiplicative form `C · q(f)²` would
require a separate a.s.-vanishing argument for the `q(f) = 0` corner.
The IR-tightness consumer (`IRTightness.lean`) only needs an
`f`-dependent bound uniform in `Lt`, so this additive form suffices.

The conclusion bundles `Integrable (fun ω => (ω f)²) ν` so the consumer
gets integrability without a separate derivation; both come from the
same exp-moment input (`cylinderIR_uniform_exponential_moment`) without
circularity (integrability uses `Real.exp |ω f|` as dominator;
the bound uses the rescaled `Real.exp |ω(λ•f)|`).

**Proof of the bound.** Apply `cylinderIR_uniform_exponential_moment` to
the scaled test function `λ • f` (any `λ > 0`):
  `∫ exp(|ω(λf)|) dν ≤ K · exp(C λ² q(f)²)`.
The pointwise inequality `(λx)² ≤ 2 exp(λ|x|)` (from
`Real.quadratic_le_exp_of_nonneg`) gives
  `λ² ∫ (ω f)² dν ≤ 2K · exp(C λ² q(f)²)`.
Choose `λ² = 1 / (C (q(f)² + 1))`, so `Cλ²q(f)² ≤ 1`:
  `∫ (ω f)² dν ≤ 2K · C · (q(f)² + 1) · e = (2KCe) q(f)² + (2KCe)`.

Hence `C₁ = C₂ = 2KCe`.

**Proof of integrability.** Apply the exp-moment at `λ = 1` (i.e. the
test function `f` itself) to get `Integrable (Real.exp ∘ |· f|) ν`. By
the pointwise bound `(ω f)² ≤ 2 · Real.exp |ω f|` (the `λ = 1` case of
the same helper) and `Integrable.mono'` against the AE-strong
measurability of `(· f) ^ 2` (composition of `configuration_eval_measurable`
with `pow_const 2`), `(ω f)²` is integrable. -/
theorem cylinder_uniform_second_moment_of_expMoment
    (K C : ℝ) (hK : 0 < K) (hC : 0 < C)
    (q : Seminorm ℝ (CylinderTestFunction Ls))
    (ν : Measure (Configuration (CylinderTestFunction Ls)))
    (hbound : ∀ f : CylinderTestFunction Ls,
      Integrable (fun ω : Configuration (CylinderTestFunction Ls) =>
        Real.exp (|ω f|)) ν ∧
      ∫ ω : Configuration (CylinderTestFunction Ls),
        Real.exp (|ω f|) ∂ν ≤ K * Real.exp (C * q f ^ 2)) :
    ∀ f : CylinderTestFunction Ls,
    Integrable (fun ω : Configuration (CylinderTestFunction Ls) =>
      (ω f) ^ 2) ν ∧
    ∫ ω : Configuration (CylinderTestFunction Ls),
      (ω f) ^ 2 ∂ν ≤
    (2 * K * C * Real.exp 1) * q f ^ 2 +
      (2 * K * C * Real.exp 1) := by
  intro f
  set s : ℝ := q f with hs_def
  have hs_nn : 0 ≤ s := apply_nonneg q f
  -- Choose scaling: λ² = 1 / (C (s² + 1))
  set α : ℝ := C * (s ^ 2 + 1) with hα_def
  have hα_pos : 0 < α := by rw [hα_def]; positivity
  set lam : ℝ := Real.sqrt (1 / α) with hlam_def
  have hlam_pos : 0 < lam :=
    Real.sqrt_pos.mpr (one_div_pos.mpr hα_pos)
  have hlam_sq : lam ^ 2 = 1 / α :=
    Real.sq_sqrt (one_div_pos.mpr hα_pos).le
  have hlam2_pos : (0:ℝ) < lam ^ 2 := by positivity
  -- Apply exp moment at λ = 1 (for integrability of (ωf)²)
  obtain ⟨h_int_one, _⟩ := hbound f
  -- Apply exp moment to (lam • f) (for the moment bound)
  obtain ⟨h_int_lam, h_bd_lam⟩ := hbound (lam • f)
  -- AE-strong measurability of (ω f)² via configuration_eval_measurable
  have h_meas_sq : AEStronglyMeasurable
      (fun ω : Configuration (CylinderTestFunction Ls) => (ω f) ^ 2) ν :=
    ((configuration_eval_measurable f).pow_const 2).aestronglyMeasurable
  -- Integrability of (ω f)² via domination by 2 * Real.exp |ω f|
  have h_int_sq : Integrable (fun ω : Configuration (CylinderTestFunction Ls) =>
      (ω f) ^ 2) ν := by
    refine (h_int_one.const_mul 2).mono' h_meas_sq (ae_of_all _ fun ω => ?_)
    have h := sq_le_two_mul_exp_abs (ω f)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact h
  refine ⟨h_int_sq, ?_⟩
  -- Linearity of ω: ω(λ•f) = λ * ω f
  have h_eval : ∀ ω : Configuration (CylinderTestFunction Ls),
      ω (lam • f) = lam * ω f := by
    intro ω; simp [map_smul]
  -- Seminorm scaling: q(λ•f)² = λ² * s²
  have h_q : q (lam • f) ^ 2 = lam ^ 2 * s ^ 2 := by
    rw [map_smul_eq_mul q lam f, mul_pow, Real.norm_eq_abs, sq_abs, hs_def]
  -- Pointwise: λ² (ω f)² ≤ 2 * exp(|ω(λ•f)|)
  have h_pt : ∀ ω : Configuration (CylinderTestFunction Ls),
      lam ^ 2 * (ω f) ^ 2 ≤ 2 * Real.exp |ω (lam • f)| := by
    intro ω
    have h := sq_le_two_mul_exp_abs (lam * ω f)
    have h_pow : (lam * ω f) ^ 2 = lam ^ 2 * (ω f) ^ 2 := by ring
    have h_abs : |lam * ω f| = |ω (lam • f)| := by rw [h_eval ω]
    rw [h_pow, h_abs] at h
    exact h
  -- Integrate the pointwise inequality
  have h_2exp_int :
      Integrable (fun ω => 2 * Real.exp |ω (lam • f)|) ν := h_int_lam.const_mul 2
  have h_lhs_nn :
      0 ≤ᵐ[ν] fun ω : Configuration (CylinderTestFunction Ls) =>
        lam ^ 2 * (ω f) ^ 2 :=
    Filter.Eventually.of_forall fun ω => by positivity
  have h_pt_ae :
      (fun ω : Configuration (CylinderTestFunction Ls) =>
        lam ^ 2 * (ω f) ^ 2) ≤ᵐ[ν]
      (fun ω => 2 * Real.exp |ω (lam • f)|) :=
    Filter.Eventually.of_forall h_pt
  have h_int_le :
      ∫ ω, lam ^ 2 * (ω f) ^ 2 ∂ν ≤
      ∫ ω, 2 * Real.exp |ω (lam • f)| ∂ν :=
    integral_mono_of_nonneg h_lhs_nn h_2exp_int h_pt_ae
  rw [integral_const_mul, integral_const_mul] at h_int_le
  -- Combine with exponential moment bound
  have h_chain :
      lam ^ 2 * ∫ ω, (ω f) ^ 2 ∂ν ≤
      2 * (K * Real.exp (C * q (lam • f) ^ 2)) :=
    h_int_le.trans (by gcongr)
  rw [h_q] at h_chain
  -- Now: lam² * A ≤ 2K * exp(C * lam² * s²) where A = ∫(ωf)²
  -- Bound exp(C lam² s²) ≤ exp(1) since C lam² s² ≤ 1
  have hCls_le_1 : C * lam ^ 2 * s ^ 2 ≤ 1 := by
    rw [hlam_sq]
    have hs2_le : C * s ^ 2 ≤ α := by
      change C * s ^ 2 ≤ C * (s ^ 2 + 1)
      have : s ^ 2 ≤ s ^ 2 + 1 := by linarith
      exact mul_le_mul_of_nonneg_left this hC.le
    rw [show C * (1 / α) * s ^ 2 = C * s ^ 2 / α by ring,
        div_le_one hα_pos]
    exact hs2_le
  have h_exp_le : Real.exp (C * lam ^ 2 * s ^ 2) ≤ Real.exp 1 :=
    Real.exp_le_exp.mpr hCls_le_1
  -- A ≤ (2K/lam²) exp(C lam² s²) ≤ (2K/lam²) e = 2K * α * e = 2KC(s²+1) e
  --   = 2KCe s² + 2KCe = C₁ s² + C₂
  have h_A_le_div :
      ∫ ω, (ω f) ^ 2 ∂ν ≤
      (2 * K / lam ^ 2) * Real.exp (C * lam ^ 2 * s ^ 2) := by
    have h_arg_eq : C * (lam ^ 2 * s ^ 2) = C * lam ^ 2 * s ^ 2 := by ring
    have h_chain' : lam ^ 2 * ∫ ω, (ω f) ^ 2 ∂ν ≤
        2 * K * Real.exp (C * lam ^ 2 * s ^ 2) := by
      calc lam ^ 2 * ∫ ω, (ω f) ^ 2 ∂ν
          ≤ 2 * (K * Real.exp (C * (lam ^ 2 * s ^ 2))) := h_chain
        _ = 2 * K * Real.exp (C * lam ^ 2 * s ^ 2) := by rw [h_arg_eq]; ring
    rw [div_mul_eq_mul_div, le_div_iff₀ hlam2_pos, mul_comm _ (lam ^ 2)]
    exact h_chain'
  calc ∫ ω, (ω f) ^ 2 ∂ν
      ≤ (2 * K / lam ^ 2) * Real.exp (C * lam ^ 2 * s ^ 2) := h_A_le_div
    _ ≤ (2 * K / lam ^ 2) * Real.exp 1 := by
        have : 0 ≤ 2 * K / lam ^ 2 := by positivity
        exact mul_le_mul_of_nonneg_left h_exp_le this
    _ = 2 * K * α * Real.exp 1 := by
        rw [hlam_sq]
        field_simp [ne_of_gt hα_pos]
    _ = 2 * K * C * (s ^ 2 + 1) * Real.exp 1 := by
        rw [hα_def]; ring
    _ = 2 * K * C * Real.exp 1 * s ^ 2 + 2 * K * C * Real.exp 1 := by ring

/-- The Green-controlled route supplies the generic cylinder exponential
moment interface, hence the same additive uniform second-moment estimate as
before. -/
theorem cylinderIR_uniform_second_moment
    (mass : ℝ) (hmass : 0 < mass)
    (KG CG : ℝ) (hKG_pos : 0 < KG) (hCG_pos : 0 < CG) :
    ∃ (C₁ C₂ : ℝ) (q : Seminorm ℝ (CylinderTestFunction Ls)),
    0 < C₁ ∧ 0 < C₂ ∧ Continuous q ∧
    ∀ (Lt : ℝ) [Fact (0 < Lt)] (_ : 1 ≤ Lt)
      (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
      [IsProbabilityMeasure μ]
      (_ : MeasureHasGreenMomentBound Ls mass hmass KG CG μ)
      (f : CylinderTestFunction Ls),
    Integrable (fun ω : Configuration (CylinderTestFunction Ls) =>
      (ω f) ^ 2) (cylinderPullbackMeasure Lt Ls μ) ∧
    ∫ ω : Configuration (CylinderTestFunction Ls),
      (ω f) ^ 2 ∂(cylinderPullbackMeasure Lt Ls μ) ≤
    C₁ * q f ^ 2 + C₂ := by
  obtain ⟨K, C, q, hK, hC, hq_cont, hbound⟩ :=
    cylinderIR_uniform_exponential_moment Ls mass hmass KG CG hKG_pos hCG_pos
  refine ⟨2 * K * C * Real.exp 1, 2 * K * C * Real.exp 1, q,
    by positivity, by positivity, hq_cont, ?_⟩
  intro Lt _ hLt μ _ hμ_green f
  exact cylinder_uniform_second_moment_of_expMoment Ls K C hK hC q
    (cylinderPullbackMeasure Lt Ls μ) (hbound Lt hLt μ hμ_green) f

end Pphi2
