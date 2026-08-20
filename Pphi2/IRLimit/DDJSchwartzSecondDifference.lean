/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A centered second-difference bound for Schwartz functions

This file isolates the unperiodized estimate used by the centered lattice
periodization bound.  The seminorm is a finite supremum of the usual Schwartz
seminorms through derivative order two.
-/

import Pphi2.IRLimit.DDJPeriodizationBound
import Mathlib.Analysis.Calculus.Taylor

noncomputable section

namespace Pphi2

open GaussianField Set

/-- A finite Schwartz seminorm controlling the weighted second derivative. -/
def centeredSecondDiffSeminorm : Seminorm ℝ (SchwartzMap ℝ ℝ) :=
  (Finset.Iic ((2 : ℕ), (2 : ℕ))).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2)

theorem centeredSecondDiffSeminorm_continuous :
    Continuous centeredSecondDiffSeminorm := by
  refine Seminorm.continuous_of_le
    (p := centeredSecondDiffSeminorm)
    (q := ∑ m ∈ Finset.Iic ((2 : ℕ), (2 : ℕ)),
      SchwartzMap.seminorm ℝ m.1 m.2) ?_ ?_
  · change Continuous fun h : SchwartzMap ℝ ℝ =>
      (∑ m ∈ Finset.Iic ((2 : ℕ), (2 : ℕ)),
        SchwartzMap.seminorm ℝ m.1 m.2) h
    exact continuous_finsetSum _ fun m _ =>
      (schwartz_withSeminorms (𝕜 := ℝ) (E := ℝ) (F := ℝ)).continuous_seminorm m
  · simpa only [centeredSecondDiffSeminorm] using
      (Seminorm.finset_sup_le_sum
        (𝕜 := ℝ) (E := SchwartzMap ℝ ℝ)
        (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2)
        (Finset.Iic ((2 : ℕ), (2 : ℕ))))

private lemma centeredSecondDiffSeminorm_second_deriv_bound
    (h : SchwartzMap ℝ ℝ) (x a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    ∀ y ∈ Set.Icc (x - a) (x + a),
      |iteratedDeriv 2 (h : ℝ → ℝ) y| ≤
        16 * centeredSecondDiffSeminorm h / (1 + |x|) ^ 2 := by
  intro y hy
  have hbd := SchwartzMap.one_add_le_sup_seminorm_apply
    (𝕜 := ℝ) (m := ((2 : ℕ), (2 : ℕ)))
    (le_refl _) (le_refl _) h y
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hbd
  rw [Real.norm_eq_abs] at hbd
  norm_num at hbd
  have hbd' :
      |iteratedDeriv 2 (h : ℝ → ℝ) y| ≤
        4 * centeredSecondDiffSeminorm h / (1 + |y|) ^ 2 := by
    rw [le_div_iff₀ (sq_pos_of_pos (by positivity : (0 : ℝ) < 1 + |y|))]
    simpa [centeredSecondDiffSeminorm, mul_comm] using hbd
  have hxy : |x - y| ≤ a := by
    rw [abs_le]
    constructor <;> linarith [hy.1, hy.2]
  have htri : |x| ≤ |y| + |x - y| := by
    calc
      |x| = |(x - y) + y| := by ring_nf
      _ ≤ |x - y| + |y| := abs_add_le _ _
      _ = |y| + |x - y| := by ring
  have hweight : 1 + |x| ≤ 2 * (1 + |y|) := by
    nlinarith [htri, hxy, abs_nonneg y]
  have hpow : (1 + |x|) ^ 2 ≤ 4 * (1 + |y|) ^ 2 := by
    have hpow' := pow_le_pow_left₀
      (by positivity : (0 : ℝ) ≤ 1 + |x|) hweight 2
    nlinarith
  have hq : 0 ≤ centeredSecondDiffSeminorm h :=
    apply_nonneg _ _
  calc
    |iteratedDeriv 2 (h : ℝ → ℝ) y| ≤
        4 * centeredSecondDiffSeminorm h / (1 + |y|) ^ 2 := hbd'
    _ ≤ 16 * centeredSecondDiffSeminorm h / (1 + |x|) ^ 2 := by
      rw [div_le_div_iff₀
        (sq_pos_of_pos (by positivity : (0 : ℝ) < 1 + |y|))
        (sq_pos_of_pos (by positivity : (0 : ℝ) < 1 + |x|))]
      have hmul := mul_le_mul_of_nonneg_left hpow (by positivity :
        (0 : ℝ) ≤ 4 * centeredSecondDiffSeminorm h)
      nlinarith

private lemma centered_second_diff_of_second_deriv_bound
    (h : SchwartzMap ℝ ℝ) (x a M : ℝ) (ha : 0 < a)
    (hsecond : ∀ y ∈ Set.Icc (x - a) (x + a),
      |iteratedDeriv 2 (h : ℝ → ℝ) y| ≤ M) :
    |h (x + a) + h (x - a) - 2 * h x| ≤ M * a ^ 2 := by
  have hplus_base :
      derivWithin (h : ℝ → ℝ) (Set.Icc x (x + a)) x =
        deriv (h : ℝ → ℝ) x := by
    exact ((h.smooth' : ContDiff ℝ (⊤ : ℕ∞) (h : ℝ → ℝ)).of_le
      (mod_cast le_top)).contDiffAt.differentiableAt_one.derivWithin
      (uniqueDiffOn_Icc (by linarith) x (by simp [ha.le]))
  have hminus_base :
      derivWithin (h : ℝ → ℝ) (Set.Icc (x - a) x) x =
        deriv (h : ℝ → ℝ) x := by
    exact ((h.smooth' : ContDiff ℝ (⊤ : ℕ∞) (h : ℝ → ℝ)).of_le
      (mod_cast le_top)).contDiffAt.differentiableAt_one.derivWithin
      (uniqueDiffOn_Icc (by linarith) x (by simp [ha.le]))
  obtain ⟨yplus, hyplus, hplus⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (f := (h : ℝ → ℝ)) (x₀ := x) (x := x + a) (n := 1)
      (by linarith)
      (((h.smooth' : ContDiff ℝ (⊤ : ℕ∞) (h : ℝ → ℝ)).of_le
        (mod_cast le_top)).contDiffOn)
  obtain ⟨yminus, hyminus, hminus⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (f := (h : ℝ → ℝ)) (x₀ := x) (x := x - a) (n := 1)
      (by linarith)
      (((h.smooth' : ContDiff ℝ (⊤ : ℕ∞) (h : ℝ → ℝ)).of_le
        (mod_cast le_top)).contDiffOn)
  have hyplus' : yplus ∈ Set.Icc (x - a) (x + a) := by
    rw [uIoo_of_lt (by linarith)] at hyplus
    constructor <;> linarith [hyplus.1, hyplus.2]
  have hyminus' : yminus ∈ Set.Icc (x - a) (x + a) := by
    rw [uIoo_of_gt (by linarith)] at hyminus
    constructor <;> linarith [hyminus.1, hyminus.2]
  have hplus_taylor :
      taylorWithinEval (h : ℝ → ℝ) 1 (Set.uIcc x (x + a)) x (x + a) =
        h x + a * deriv (h : ℝ → ℝ) x := by
    rw [uIcc_of_le (a := x) (b := x + a) (by linarith), taylor_within_apply]
    simp [Finset.sum_range_succ, iteratedDerivWithin_zero, iteratedDerivWithin_one,
      hplus_base, sub_eq_add_neg, smul_eq_mul]
  have hminus_taylor :
      taylorWithinEval (h : ℝ → ℝ) 1 (Set.uIcc x (x - a)) x (x - a) =
        h x - a * deriv (h : ℝ → ℝ) x := by
    have hminus_base' :
        derivWithin (h : ℝ → ℝ) (Set.Icc (x + -a) x) x =
          deriv (h : ℝ → ℝ) x := by
      simpa only [sub_eq_add_neg] using hminus_base
    rw [uIcc_of_ge (a := x) (b := x - a) (by linarith), taylor_within_apply]
    simp [Finset.sum_range_succ, iteratedDerivWithin_zero, iteratedDerivWithin_one,
      hminus_base', sub_eq_add_neg, smul_eq_mul]
  have hplus' :
      h (x + a) - (h x + a * deriv (h : ℝ → ℝ) x) =
        iteratedDeriv 2 (h : ℝ → ℝ) yplus * a ^ 2 / 2 := by
    calc
      h (x + a) - (h x + a * deriv (h : ℝ → ℝ) x) =
          h (x + a) -
            taylorWithinEval (h : ℝ → ℝ) 1 (Set.uIcc x (x + a)) x (x + a) := by
              rw [hplus_taylor]
      _ = iteratedDeriv 2 (h : ℝ → ℝ) yplus *
          ((x + a - x) ^ 2) / (2 : ℝ) := by
            simpa [Nat.factorial] using hplus
      _ = iteratedDeriv 2 (h : ℝ → ℝ) yplus * a ^ 2 / 2 := by
        ring
  have hminus' :
      h (x - a) - (h x - a * deriv (h : ℝ → ℝ) x) =
        iteratedDeriv 2 (h : ℝ → ℝ) yminus * a ^ 2 / 2 := by
    calc
      h (x - a) - (h x - a * deriv (h : ℝ → ℝ) x) =
          h (x - a) -
            taylorWithinEval (h : ℝ → ℝ) 1 (Set.uIcc x (x - a)) x (x - a) := by
              rw [hminus_taylor]
      _ = iteratedDeriv 2 (h : ℝ → ℝ) yminus *
          ((x - a - x) ^ 2) / (2 : ℝ) := by
            simpa [Nat.factorial] using hminus
      _ = iteratedDeriv 2 (h : ℝ → ℝ) yminus * a ^ 2 / 2 := by
        ring
  have hplus_bound :
      |iteratedDeriv 2 (h : ℝ → ℝ) yplus * a ^ 2 / 2| ≤ M * a ^ 2 / 2 := by
    have hmul := mul_le_mul_of_nonneg_right
      (hsecond yplus hyplus') (sq_nonneg a)
    calc
      |iteratedDeriv 2 (h : ℝ → ℝ) yplus * a ^ 2 / 2| =
          |iteratedDeriv 2 (h : ℝ → ℝ) yplus| * a ^ 2 / 2 := by
            rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg a)]
            norm_num
      _ ≤ M * a ^ 2 / 2 := by
        exact div_le_div_of_nonneg_right hmul (by norm_num)
  have hminus_bound :
      |iteratedDeriv 2 (h : ℝ → ℝ) yminus * a ^ 2 / 2| ≤ M * a ^ 2 / 2 := by
    have hmul := mul_le_mul_of_nonneg_right
      (hsecond yminus hyminus') (sq_nonneg a)
    calc
      |iteratedDeriv 2 (h : ℝ → ℝ) yminus * a ^ 2 / 2| =
          |iteratedDeriv 2 (h : ℝ → ℝ) yminus| * a ^ 2 / 2 := by
            rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg a)]
            norm_num
      _ ≤ M * a ^ 2 / 2 := by
        exact div_le_div_of_nonneg_right hmul (by norm_num)
  have hsum :
      h (x + a) + h (x - a) - 2 * h x =
        (iteratedDeriv 2 (h : ℝ → ℝ) yplus * a ^ 2 / 2) +
          (iteratedDeriv 2 (h : ℝ → ℝ) yminus * a ^ 2 / 2) := by
    linarith [hplus', hminus']
  rw [hsum]
  calc
    |iteratedDeriv 2 (h : ℝ → ℝ) yplus * a ^ 2 / 2 +
          iteratedDeriv 2 (h : ℝ → ℝ) yminus * a ^ 2 / 2| ≤
        |iteratedDeriv 2 (h : ℝ → ℝ) yplus * a ^ 2 / 2| +
          |iteratedDeriv 2 (h : ℝ → ℝ) yminus * a ^ 2 / 2| := abs_add_le _ _
    _ ≤ M * a ^ 2 / 2 + M * a ^ 2 / 2 :=
      add_le_add hplus_bound hminus_bound
    _ = M * a ^ 2 := by ring

theorem centeredSecondDiffSeminorm_second_diff_decay
    (h : SchwartzMap ℝ ℝ) (a x : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    |h (x + a) + h (x - a) - 2 * h x| ≤
      16 * a ^ 2 * centeredSecondDiffSeminorm h / (1 + |x|) ^ 2 := by
  have hsecond := centeredSecondDiffSeminorm_second_deriv_bound h x a ha ha1
  exact (centered_second_diff_of_second_deriv_bound h x a
    (16 * centeredSecondDiffSeminorm h / (1 + |x|) ^ 2) ha hsecond).trans_eq
    (by ring)

theorem schwartz_centered_second_diff_decay :
    ∃ q : Seminorm ℝ (SchwartzMap ℝ ℝ), Continuous q ∧
      ∀ (h : SchwartzMap ℝ ℝ) (a x : ℝ),
        0 < a → a ≤ 1 →
        |h (x + a) + h (x - a) - 2 * h x| ≤
          16 * a ^ 2 * q h / (1 + |x|) ^ 2 := by
  exact ⟨centeredSecondDiffSeminorm,
    centeredSecondDiffSeminorm_continuous,
    centeredSecondDiffSeminorm_second_diff_decay⟩

end Pphi2
