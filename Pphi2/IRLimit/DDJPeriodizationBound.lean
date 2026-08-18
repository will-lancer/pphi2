/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Uniform centered bounds for periodized Schwartz functions

The periodization map is defined in the GaussianField dependency by
`periodizeCLM_apply`.  This file records the elementary estimate needed when a
periodized temporal Schwartz function is sampled on a finite circle.  The
bound is uniform for periods `L ≥ 1`; the decay variable is the centered
physical coordinate, rather than the uncentered representative `val z`.
-/

import Pphi2.IRLimit.Periodization
import Pphi2.ContinuumLimit.Embedding

noncomputable section

namespace Pphi2

open GaussianField

/-! ## The universal inverse-square series -/

private def invIntSq (k : ℤ) : ℝ :=
  if k = 0 then 0 else 1 / ((k.natAbs : ℝ) ^ 2)

private def intZeroIndicator (k : ℤ) : ℝ :=
  if k = 0 then 1 else 0

private lemma summable_invIntSq : Summable invIntSq := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · have h := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    refine h.congr ?_
    intro n
    simp [invIntSq]
  · have h := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    refine h.congr ?_
    intro n
    simp [invIntSq]

private lemma invIntSq_even : Function.Even invIntSq := by
  intro k
  simp [invIntSq]

private lemma tsum_invIntSq :
    (∑' k : ℤ, invIntSq k) =
      2 * (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2) := by
  have hs := summable_invIntSq
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat invIntSq_even hs]
  have hzero : invIntSq 0 = 0 := by simp [invIntSq]
  rw [hzero, zero_add]
  rw [tsum_pnat_eq_tsum_succ]
  congr 1
  funext n
  simp [invIntSq]

private lemma summable_intZeroIndicator :
    Summable intZeroIndicator := by
  apply summable_of_hasFiniteSupport
  refine (Set.finite_singleton (0 : ℤ)).subset ?_
  intro k hk
  simp only [Set.mem_setOf_eq] at hk
  by_contra hk0
  simp [intZeroIndicator, hk0] at hk

private lemma schwartz_zero_decay (h : SchwartzMap ℝ ℝ) :
    ∀ x : ℝ, |h x| ≤
      4 * ((Finset.Iic ((2 : ℕ), (0 : ℕ))).sup
        (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) h /
        (1 + |x|) ^ 2 := by
  intro x
  have hbd := SchwartzMap.one_add_le_sup_seminorm_apply
    (𝕜 := ℝ) (m := ((2 : ℕ), (0 : ℕ))) (le_refl _) (le_refl _) h x
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hbd
  have hbd' : (1 + |x|) ^ 2 * |h x| ≤
      4 * ((Finset.Iic ((2 : ℕ), (0 : ℕ))).sup
        (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) h := by
    simpa [iteratedDeriv_zero, Real.norm_eq_abs] using hbd
  rw [le_div_iff₀ (sq_pos_of_pos (by positivity : (0 : ℝ) < 1 + |x|))]
  simpa [mul_comm] using hbd'

/-! ## A centered periodization estimate -/

private lemma periodizeCLM_centered_decay_of_pointwise
    (h : SchwartzMap ℝ ℝ) (S : ℝ) (hS : 0 ≤ S)
    (hdecay : ∀ x : ℝ, |h x| ≤ 4 * S / (1 + |x|) ^ 2)
    (L : ℝ) [hL : Fact (0 < L)] (hL1 : 1 ≤ L)
    (t : ℝ) (ht : |t| ≤ L / 2) :
    |(periodizeCLM L h).toFun t| ≤
      (4 + 72 * (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2)) * S /
        (1 + |t|) ^ 2 := by
  let A : ℝ := 4 * S / (1 + |t|) ^ 2
  let B : ℝ := 36 * S / (1 + |t|) ^ 2
  let u : ℤ → ℝ := fun k => A * intZeroIndicator k + B * invIntSq k
  have hden_pos : 0 < (1 + |t|) ^ 2 := by positivity
  have hLt_pos : 0 < L := hL.out
  have hsum_u : Summable u := by
    dsimp [u]
    exact (summable_intZeroIndicator.mul_left A).add
      (summable_invIntSq.mul_left B)
  have hpoint : ∀ k : ℤ, ‖h (t + (k : ℝ) * L)‖ ≤ u k := by
    intro k
    rw [Real.norm_eq_abs]
    by_cases hk : k = 0
    · subst hk
      simp only [u, intZeroIndicator, if_pos, invIntSq, A, B]
      rw [zero_mul, add_zero]
      exact hdecay t
    · have hk_ne : k ≠ 0 := hk
      have hk_abs_pos : 0 < (k.natAbs : ℝ) := by
        exact_mod_cast (Int.natAbs_pos.mpr hk_ne)
      have hk_abs_ge : (1 : ℝ) ≤ (k.natAbs : ℝ) := by
        have hk_nat_pos : 0 < k.natAbs := Int.natAbs_pos.mpr hk_ne
        exact_mod_cast (show 1 ≤ k.natAbs by omega)
      have hdist : (k.natAbs : ℝ) * L / 2 ≤ |t + (k : ℝ) * L| := by
        have hk_cast_abs : |(k : ℝ)| = (k.natAbs : ℝ) := by
          simpa only [Int.cast_abs] using
            (Nat.cast_natAbs (α := ℝ) k).symm
        have htriangle : |(k : ℝ) * L| ≤
            |t + (k : ℝ) * L| + |t| := by
          calc
            |(k : ℝ) * L| = |(t + (k : ℝ) * L) + (-t)| := by ring_nf
            _ ≤ |t + (k : ℝ) * L| + |-t| := abs_add_le _ _
            _ = |t + (k : ℝ) * L| + |t| := by rw [abs_neg]
        have hkl : |(k : ℝ) * L| = (k.natAbs : ℝ) * L := by
          rw [abs_mul, hk_cast_abs, abs_of_pos hLt_pos]
        rw [hkl] at htriangle
        have hNL : L ≤ (k.natAbs : ℝ) * L := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hk_abs_ge) (le_of_lt hLt_pos)]
        have hkL : (k.natAbs : ℝ) * L / 2 ≤
            (k.natAbs : ℝ) * L - |t| := by
          nlinarith [ht, hNL]
        linarith
      have hbase : (k.natAbs : ℝ) * L / 2 ≤
          1 + |t + (k : ℝ) * L| := by
        linarith [hdist, abs_nonneg (t + (k : ℝ) * L)]
      have hsource := hdecay (t + (k : ℝ) * L)
      have hbound : |h (t + (k : ℝ) * L)| ≤
          16 * S / ((k.natAbs : ℝ) ^ 2 * L ^ 2) := by
        have hden : 0 < ((k.natAbs : ℝ) * L / 2) ^ 2 := by positivity
        have hpow :
            ((k.natAbs : ℝ) * L / 2) ^ 2 ≤
              (1 + |t + (k : ℝ) * L|) ^ 2 := by
          exact pow_le_pow_left₀ (by positivity) hbase 2
        rw [le_div_iff₀ (sq_pos_of_pos (by positivity :
          (0 : ℝ) < 1 + |t + (k : ℝ) * L|))] at hsource
        have hsource' : |h (t + (k : ℝ) * L)| *
            (1 + |t + (k : ℝ) * L|) ^ 2 ≤ 4 * S := by
          simpa [mul_comm] using hsource
        rw [le_div_iff₀ (mul_pos (sq_pos_of_pos hk_abs_pos)
          (sq_pos_of_pos hLt_pos))]
        calc
          |h (t + (k : ℝ) * L)| *
              ((k.natAbs : ℝ) ^ 2 * L ^ 2)
              = 4 * (|h (t + (k : ℝ) * L)| *
                ((k.natAbs : ℝ) * L / 2) ^ 2) := by ring
          _ ≤ 4 * (|h (t + (k : ℝ) * L)| *
                (1 + |t + (k : ℝ) * L|) ^ 2) := by
                gcongr
          _ ≤ 16 * S := by nlinarith [hsource']
      have hL_ratio : (1 + |t|) ^ 2 ≤ (9 / 4 : ℝ) * L ^ 2 := by
        have ht1 : 1 + |t| ≤ (3 / 2 : ℝ) * L := by
          nlinarith [ht, hL1]
        nlinarith [sq_nonneg ((3 / 2 : ℝ) * L - (1 + |t|))]
      have htail : |h (t + (k : ℝ) * L)| ≤
          B * invIntSq k := by
        dsimp [B, invIntSq]
        rw [if_neg hk]
        have hk2 : 0 < (k.natAbs : ℝ) ^ 2 := sq_pos_of_pos hk_abs_pos
        have htail_rhs :
            36 * S / (1 + |t|) ^ 2 * (1 / (k.natAbs : ℝ) ^ 2) =
              36 * S / ((k.natAbs : ℝ) ^ 2 * (1 + |t|) ^ 2) := by
          field_simp [hk2, hden_pos.ne']
          ring
        rw [htail_rhs]
        rw [le_div_iff₀ (mul_pos hk2 hden_pos)]
        calc
          |h (t + (k : ℝ) * L)| *
              ((k.natAbs : ℝ) ^ 2 * (1 + |t|) ^ 2)
              ≤ 16 * S / ((k.natAbs : ℝ) ^ 2 * L ^ 2) *
                ((k.natAbs : ℝ) ^ 2 * (1 + |t|) ^ 2) := by
                  exact mul_le_mul_of_nonneg_right hbound
                    (mul_nonneg (sq_nonneg _) (sq_nonneg _))
          _ ≤ 36 * S := by
            have hS16 : 0 ≤ 16 * S := by positivity
            have hscaled := mul_le_mul_of_nonneg_left hL_ratio hS16
            calc
              16 * S / ((k.natAbs : ℝ) ^ 2 * L ^ 2) *
                  ((k.natAbs : ℝ) ^ 2 * (1 + |t|) ^ 2) =
                (16 * S * (1 + |t|) ^ 2) / L ^ 2 := by
                  field_simp [hk2, sq_pos_of_pos hLt_pos]
                  ring
              _ ≤ (16 * S * ((9 / 4 : ℝ) * L ^ 2)) / L ^ 2 := by
                exact div_le_div_of_nonneg_right hscaled
                  (le_of_lt (sq_pos_of_pos hLt_pos))
              _ = 36 * S := by
                field_simp [sq_pos_of_pos hLt_pos]
                ring
      simpa [u, intZeroIndicator, invIntSq, hk] using htail
  have hnorm : ‖(∑' k : ℤ, h (t + (k : ℝ) * L))‖ ≤
      ∑' k : ℤ, ‖h (t + (k : ℝ) * L)‖ :=
    norm_tsum_le_tsum_norm (periodize_summable L h t).norm
  have hsum_bound : (∑' k : ℤ, u k) =
      (4 + 72 * (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2)) * S /
        (1 + |t|) ^ 2 := by
    have hA0 : Summable (fun k : ℤ => A * intZeroIndicator k) :=
      summable_intZeroIndicator.mul_left A
    have hB0 : Summable (fun k : ℤ => B * invIntSq k) :=
      summable_invIntSq.mul_left B
    dsimp [u]
    rw [hA0.tsum_add hB0, tsum_mul_left, tsum_invIntSq]
    have hzero : (∑' k : ℤ, intZeroIndicator k) = 1 := by
      simp [intZeroIndicator]
    rw [hzero]
    dsimp [A, B]
    ring
  rw [periodizeCLM_apply]
  rw [← hsum_bound]
  have hle := le_trans hnorm ((periodize_summable L h t).norm.tsum_le_tsum
    hpoint hsum_u)
  simpa only [Real.norm_eq_abs] using hle

/-! ## Grid corollary -/

theorem periodizeCLM_circlePoint_centered_decay
    (h : SchwartzMap ℝ ℝ)
    (L : ℝ) [hL : Fact (0 < L)] (hL1 : 1 ≤ L)
    (N : ℕ) [NeZero N] (z : ZMod N) :
    |(periodizeCLM L h).toFun (circlePoint L N z)| ≤
      (4 + 72 * (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2)) *
        ((Finset.Iic ((2 : ℕ), (0 : ℕ))).sup
          (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) h /
        (1 + |((signedVal N z : ℤ) : ℝ) * L / N|) ^ 2 := by
  let s : ℤ := signedVal N z
  let t : ℝ := (s : ℝ) * L / N
  let S : ℝ := ((Finset.Iic ((2 : ℕ), (0 : ℕ))).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) h
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hzval : (ZMod.val z : ℤ) < (N : ℤ) := by
    exact_mod_cast ZMod.val_lt z
  have hs2 : -(N : ℤ) ≤ 2 * s ∧ 2 * s ≤ (N : ℤ) := by
    dsimp [s, signedVal]
    split_ifs <;> omega
  have hs2r : -(N : ℝ) ≤ 2 * (s : ℝ) ∧
      2 * (s : ℝ) ≤ (N : ℝ) := by
    constructor
    · exact_mod_cast hs2.1
    · exact_mod_cast hs2.2
  have hst : |t| ≤ L / 2 := by
    have ht_nonneg : 0 ≤ L / (N : ℝ) := le_of_lt (div_pos hL.out hN_pos)
    have hs_abs : |(s : ℝ)| ≤ (N : ℝ) / 2 := by
      rw [abs_le]
      constructor <;> linarith [hs2r.1, hs2r.2]
    dsimp [t]
    rw [abs_div, abs_mul, abs_of_pos hL.out, abs_of_pos hN_pos]
    nlinarith
  have hcenter := periodizeCLM_centered_decay_of_pointwise h S
    (apply_nonneg _ _)
    (schwartz_zero_decay h) L hL1 t hst
  have hcenter_eq :
      (periodizeCLM L h).toFun (circlePoint L N z) =
        (periodizeCLM L h).toFun t := by
    by_cases hz : (ZMod.val z : ℤ) ≤ (N : ℤ) / 2
    · have hs : s = (ZMod.val z : ℤ) := by simp [s, signedVal, hz]
      dsimp only [t, circlePoint]
      simp [hs]
    · have hs : s = (ZMod.val z : ℤ) - (N : ℤ) := by
        simp [s, signedVal, hz]
      have hdiff : circlePoint L N z = t + L := by
        dsimp only [t, circlePoint]
        rw [hs]
        push_cast
        field_simp [hN_pos.ne']
        ring
      rw [hdiff]
      exact (periodizeCLM L h).periodic' t
  rw [hcenter_eq]
  simpa [S, t, s] using hcenter

end Pphi2
