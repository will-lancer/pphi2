/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/

import Pphi2.IRLimit.Periodization
import Pphi2.ContinuumLimit.Embedding

/-!
# Uniform centered bounds for periodized Schwartz functions

The periodization map is defined in the GaussianField dependency by
`periodizeCLM_apply`.  This file records the elementary estimate needed when a
periodized temporal Schwartz function is sampled on a finite circle.  The
bound is uniform for periods `L ≥ 1`; the decay variable is the centered
physical coordinate, rather than the uncentered representative `val z`.
-/

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
  simp only [nsmul_eq_mul]
  rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => invIntSq (n : ℤ))]
  congr 1
  simp [invIntSq]

private lemma summable_intZeroIndicator :
    Summable intZeroIndicator := by
  apply summable_of_hasFiniteSupport
  refine (Set.finite_singleton (0 : ℤ)).subset ?_
  intro k hk
  change intZeroIndicator k ≠ 0 at hk
  have hk0 : k = 0 := by
    by_contra hne
    apply hk
    simp [intZeroIndicator, hne]
  simpa [hk0]

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
    convert hbd using 1 <;> norm_num [iteratedDeriv_zero, Real.norm_eq_abs]
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
      simpa [u, intZeroIndicator, invIntSq, A, B] using hdecay t
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
        calc
          (1 + |t|) ^ 2 ≤ ((3 / 2 : ℝ) * L) ^ 2 :=
            pow_le_pow_left₀ (by positivity) ht1 2
          _ = (9 / 4 : ℝ) * L ^ 2 := by ring
      have htail : |h (t + (k : ℝ) * L)| ≤
          B * invIntSq k := by
        dsimp [B, invIntSq]
        rw [if_neg hk]
        have hk2 : 0 < (k.natAbs : ℝ) ^ 2 := sq_pos_of_pos hk_abs_pos
        have htail_rhs :
            36 * S / (1 + |t|) ^ 2 * (1 / (k.natAbs : ℝ) ^ 2) =
              36 * S / ((k.natAbs : ℝ) ^ 2 * (1 + |t|) ^ 2) := by
          field_simp [hk2, hden_pos.ne'] <;> ring
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
                  field_simp [hk2, sq_pos_of_pos hLt_pos] <;> ring
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
    rw [hA0.tsum_add hB0, tsum_mul_left, tsum_mul_left, tsum_invIntSq]
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
    have hmul := mul_le_mul_of_nonneg_right hs_abs (le_of_lt hL.out)
    calc
      |(s : ℝ)| * L / (N : ℝ) ≤
          (((N : ℝ) / 2) * L) / (N : ℝ) :=
        div_le_div_of_nonneg_right hmul (le_of_lt hN_pos)
      _ = L / 2 := by field_simp [hN_pos.ne'] <;> ring
  have hcenter := periodizeCLM_centered_decay_of_pointwise h S
    (apply_nonneg _ _)
    (schwartz_zero_decay h) L hL1 t hst
  have hcenter_eq :
      (periodizeCLM L h).toFun (circlePoint L N z) =
        (periodizeCLM L h).toFun t := by
    by_cases hz : (ZMod.val z : ℤ) ≤ (N : ℤ) / 2
    · have hs : s = (ZMod.val z : ℤ) := by
        dsimp [s, signedVal]
        rw [if_pos hz]
      dsimp only [t, circlePoint]
      simp [hs]
    · have hs : s = (ZMod.val z : ℤ) - (N : ℤ) := by
        dsimp [s, signedVal]
        rw [if_neg hz]
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

/-! ## Normalized second differences

The source Laplacian uses a centered second difference.  The estimate below
keeps the finite-difference input explicit.  This is useful at the interface
where a Sobolev or source-specific estimate supplies the bound on the
unperiodized Schwartz function.  The periodization and the lattice scaling are
handled here, including the wrap at the centred representative of `z`.
-/

private lemma periodizeCLM_centered_second_diff_normalized_of_pointwise
    (h : SchwartzMap ℝ ℝ) (S : ℝ) (hS : 0 ≤ S)
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hdd : ∀ x : ℝ,
      |h (x + a) + h (x - a) - 2 * h x| ≤
        16 * a ^ 2 * S / (1 + |x|) ^ 2)
    (L : ℝ) [hL : Fact (0 < L)] (hL4 : 4 ≤ L)
    (t : ℝ) (ht : |t| ≤ L / 2) :
    |(a ^ 2 : ℝ)⁻¹ *
        ((periodizeCLM L h).toFun (t + a) +
          (periodizeCLM L h).toFun (t - a) -
          2 * (periodizeCLM L h).toFun t)| ≤
      (16 + 288 * (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2)) * S /
        (1 + |t|) ^ 2 := by
  let A : ℝ := 16 * a ^ 2 * S / (1 + |t|) ^ 2
  let B : ℝ := 144 * a ^ 2 * S / (1 + |t|) ^ 2
  let u : ℤ → ℝ := fun k => A * intZeroIndicator k + B * invIntSq k
  let d : ℤ → ℝ := fun k =>
    h (t + a + (k : ℝ) * L) +
      h (t - a + (k : ℝ) * L) -
      2 * h (t + (k : ℝ) * L)
  have hden_pos : 0 < (1 + |t|) ^ 2 := by positivity
  have hLt_pos : 0 < L := hL.out
  have hsumPlus : Summable (fun k : ℤ => h (t + a + (k : ℝ) * L)) :=
    periodize_summable L h (t + a)
  have hsumMinus : Summable (fun k : ℤ => h (t - a + (k : ℝ) * L)) :=
    periodize_summable L h (t - a)
  have hsumZero : Summable (fun k : ℤ => h (t + (k : ℝ) * L)) :=
    periodize_summable L h t
  have hsum_d : Summable d := by
    exact (hsumPlus.add hsumMinus).sub (hsumZero.mul_left 2)
  have hsum_u : Summable u := by
    dsimp [u]
    exact (summable_intZeroIndicator.mul_left A).add
      (summable_invIntSq.mul_left B)
  have hdist : ∀ k : ℤ, k ≠ 0 →
      (k.natAbs : ℝ) * L / 2 ≤ |t + (k : ℝ) * L| := by
    intro k hk
    have hk_abs_pos : 0 < (k.natAbs : ℝ) := by
      exact_mod_cast (Int.natAbs_pos.mpr hk)
    have hk_abs_ge : (1 : ℝ) ≤ (k.natAbs : ℝ) := by
      have hk_nat_pos : 0 < k.natAbs := Int.natAbs_pos.mpr hk
      exact_mod_cast (show 1 ≤ k.natAbs by omega)
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
  have hpoint : ∀ k : ℤ, ‖d k‖ ≤ u k := by
    intro k
    rw [Real.norm_eq_abs]
    by_cases hk : k = 0
    · subst hk
      simpa [d, u, intZeroIndicator, invIntSq, A, B, sub_eq_add_neg,
        add_comm, add_left_comm, add_assoc] using hdd t
    · have hk_abs_pos : 0 < (k.natAbs : ℝ) := by
        exact_mod_cast (Int.natAbs_pos.mpr hk)
      have hdist' := hdist k hk
      have hbase : (k.natAbs : ℝ) * L / 2 ≤
          1 + |t + (k : ℝ) * L| := by
        linarith [abs_nonneg (t + (k : ℝ) * L)]
      have hsource := hdd (t + (k : ℝ) * L)
      have hbound : |d k| ≤
          64 * a ^ 2 * S / ((k.natAbs : ℝ) ^ 2 * L ^ 2) := by
        have hden : 0 < ((k.natAbs : ℝ) * L / 2) ^ 2 := by positivity
        have hpow : ((k.natAbs : ℝ) * L / 2) ^ 2 ≤
            (1 + |t + (k : ℝ) * L|) ^ 2 := by
          exact pow_le_pow_left₀ (by positivity) hbase 2
        rw [le_div_iff₀ (sq_pos_of_pos (by positivity :
          (0 : ℝ) < 1 + |t + (k : ℝ) * L|))] at hsource
        have hsource' : |d k| *
            (1 + |t + (k : ℝ) * L|) ^ 2 ≤ 16 * a ^ 2 * S := by
          simpa [d, sub_eq_add_neg, mul_comm, add_comm, add_left_comm, add_assoc] using hsource
        rw [le_div_iff₀ (mul_pos (sq_pos_of_pos hk_abs_pos)
          (sq_pos_of_pos hLt_pos))]
        calc
          |d k| * ((k.natAbs : ℝ) ^ 2 * L ^ 2) =
              4 * (|d k| * ((k.natAbs : ℝ) * L / 2) ^ 2) := by ring
          _ ≤ 4 * (|d k| *
              (1 + |t + (k : ℝ) * L|) ^ 2) := by
            gcongr
          _ ≤ 64 * a ^ 2 * S := by nlinarith [hsource']
      have hL_ratio : (1 + |t|) ^ 2 ≤ (9 / 4 : ℝ) * L ^ 2 := by
        have ht1 : 1 + |t| ≤ (3 / 2 : ℝ) * L := by
          nlinarith [ht, hL4]
        calc
          (1 + |t|) ^ 2 ≤ ((3 / 2 : ℝ) * L) ^ 2 :=
            pow_le_pow_left₀ (by positivity) ht1 2
          _ = (9 / 4 : ℝ) * L ^ 2 := by ring
      have htail : |d k| ≤ B * invIntSq k := by
        dsimp [B, invIntSq]
        rw [if_neg hk]
        have hk2 : 0 < (k.natAbs : ℝ) ^ 2 := sq_pos_of_pos hk_abs_pos
        have htail_rhs :
            144 * a ^ 2 * S / (1 + |t|) ^ 2 *
                (1 / (k.natAbs : ℝ) ^ 2) =
              144 * a ^ 2 * S /
                ((k.natAbs : ℝ) ^ 2 * (1 + |t|) ^ 2) := by
          field_simp [hk2, hden_pos.ne'] <;> ring
        rw [htail_rhs]
        rw [le_div_iff₀ (mul_pos hk2 hden_pos)]
        calc
          |d k| * ((k.natAbs : ℝ) ^ 2 * (1 + |t|) ^ 2) ≤
              64 * a ^ 2 * S / ((k.natAbs : ℝ) ^ 2 * L ^ 2) *
                ((k.natAbs : ℝ) ^ 2 * (1 + |t|) ^ 2) := by
            exact mul_le_mul_of_nonneg_right hbound
              (mul_nonneg (sq_nonneg _) (sq_nonneg _))
          _ ≤ 144 * a ^ 2 * S := by
            have hS64 : 0 ≤ 64 * a ^ 2 * S := by positivity
            have hscaled := mul_le_mul_of_nonneg_left hL_ratio hS64
            calc
              64 * a ^ 2 * S / ((k.natAbs : ℝ) ^ 2 * L ^ 2) *
                  ((k.natAbs : ℝ) ^ 2 * (1 + |t|) ^ 2) =
                (64 * a ^ 2 * S * (1 + |t|) ^ 2) / L ^ 2 := by
                  field_simp [hk2, sq_pos_of_pos hLt_pos] <;> ring
              _ ≤ (64 * a ^ 2 * S * ((9 / 4 : ℝ) * L ^ 2)) / L ^ 2 := by
                exact div_le_div_of_nonneg_right hscaled
                  (le_of_lt (sq_pos_of_pos hLt_pos))
              _ = 144 * a ^ 2 * S := by
                field_simp [sq_pos_of_pos hLt_pos]
                ring
      simpa [u, intZeroIndicator, invIntSq, hk] using htail
  have hnorm : ‖(∑' k : ℤ, d k)‖ ≤ ∑' k : ℤ, ‖d k‖ :=
    norm_tsum_le_tsum_norm hsum_d.norm
  have hsum_bound : (∑' k : ℤ, u k) =
      (16 + 288 * (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2)) *
        a ^ 2 * S / (1 + |t|) ^ 2 := by
    have hA0 : Summable (fun k : ℤ => A * intZeroIndicator k) :=
      summable_intZeroIndicator.mul_left A
    have hB0 : Summable (fun k : ℤ => B * invIntSq k) :=
      summable_invIntSq.mul_left B
    dsimp [u]
    rw [hA0.tsum_add hB0, tsum_mul_left, tsum_mul_left, tsum_invIntSq]
    have hzero : (∑' k : ℤ, intZeroIndicator k) = 1 := by
      simp [intZeroIndicator]
    rw [hzero]
    dsimp [A, B]
    ring
  have hrewrite :
      (periodizeCLM L h).toFun (t + a) +
          (periodizeCLM L h).toFun (t - a) -
      2 * (periodizeCLM L h).toFun t = ∑' k : ℤ, d k := by
    rw [periodizeCLM_apply, periodizeCLM_apply, periodizeCLM_apply]
    rw [← hsumPlus.tsum_add hsumMinus, ← tsum_mul_left,
      ← (hsumPlus.add hsumMinus).tsum_sub (hsumZero.mul_left 2)]
  rw [hrewrite]
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg a))]
  have hle := le_trans hnorm ((hsum_d.norm.tsum_le_tsum hpoint hsum_u))
  rw [hsum_bound] at hle
  calc
    (a ^ 2)⁻¹ * ‖∑' k : ℤ, d k‖ ≤
        (a ^ 2)⁻¹ *
          ((16 + 288 * (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2)) *
            a ^ 2 * S / (1 + |t|) ^ 2) := by
      exact mul_le_mul_of_nonneg_left hle
        (inv_nonneg.mpr (sq_nonneg a))
    _ = (16 + 288 * (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2)) * S /
          (1 + |t|) ^ 2 := by
      field_simp [ne_of_gt ha, hden_pos.ne'] <;> ring

theorem periodizeCLM_circlePoint_centered_second_diff_decay
    (h : SchwartzMap ℝ ℝ)
    (q : Seminorm ℝ (SchwartzMap ℝ ℝ)) (hq : Continuous q)
    (L : ℝ) [hL : Fact (0 < L)] (hL4 : 4 ≤ L)
    (N : ℕ) [NeZero N] (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hphys : (N : ℝ) * a = L) (z : ZMod N)
    (hdd : ∀ x : ℝ,
      |h (x + a) + h (x - a) - 2 * h x| ≤
        16 * a ^ 2 * q h / (1 + |x|) ^ 2) :
    |(a ^ 2 : ℝ)⁻¹ *
        (2 * circleRestriction L N (periodizeCLM L h) z -
          circleRestriction L N (periodizeCLM L h) (z + 1) -
          circleRestriction L N (periodizeCLM L h) (z - 1))| ≤
      Real.sqrt a *
        (16 + 288 * (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2)) * q h /
          (1 + |((signedVal N z : ℤ) : ℝ) * L / N|) ^ 2 := by
  have hq_nonneg : 0 ≤ q h := apply_nonneg q h
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_pos
  have ha_eq : L / (N : ℝ) = a := by
    field_simp [hN_ne]
    nlinarith [hphys]
  let s : ℤ := signedVal N z
  let t : ℝ := (s : ℝ) * L / N
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
  have ht : |t| ≤ L / 2 := by
    have ht_nonneg : 0 ≤ L / (N : ℝ) := le_of_lt (div_pos hL.out hN_pos)
    have hs_abs : |(s : ℝ)| ≤ (N : ℝ) / 2 := by
      rw [abs_le]
      constructor <;> linarith [hs2r.1, hs2r.2]
    dsimp [t]
    rw [abs_div, abs_mul, abs_of_pos hL.out, abs_of_pos hN_pos]
    have hmul := mul_le_mul_of_nonneg_right hs_abs (le_of_lt hL.out)
    calc
      |(s : ℝ)| * L / (N : ℝ) ≤
          (((N : ℝ) / 2) * L) / (N : ℝ) :=
        div_le_div_of_nonneg_right hmul (le_of_lt hN_pos)
      _ = L / 2 := by field_simp [hN_pos.ne'] <;> ring
  have hraw := periodizeCLM_centered_second_diff_normalized_of_pointwise h
    (q h) hq_nonneg a ha ha1 hdd L hL4 t ht
  have hcenter_eq :
      (periodizeCLM L h) (circlePoint L N z) =
        (periodizeCLM L h) t := by
    by_cases hz : (ZMod.val z : ℤ) ≤ (N : ℤ) / 2
    · have hs' : s = (ZMod.val z : ℤ) := by
        dsimp [s, signedVal]
        rw [if_pos hz]
      dsimp only [t, circlePoint]
      simp [hs']
    · have hs' : s = (ZMod.val z : ℤ) - (N : ℤ) := by
        dsimp [s, signedVal]
        rw [if_neg hz]
      have hdiff : circlePoint L N z = t + L := by
        dsimp only [t, circlePoint]
        rw [hs']
        push_cast
        field_simp [hN_ne]
        ring
      rw [hdiff]
      exact (periodizeCLM L h).periodic' t
  have hsucc :
      (periodizeCLM L h) (circlePoint L N (z + 1)) =
        (periodizeCLM L h) (circlePoint L N z + a) := by
    have hdvd : (N : ℤ) ∣ ((z.val : ℤ) + 1 - ((z + 1 : ZMod N).val : ℤ)) := by
      rw [← Int.modEq_iff_dvd, ← ZMod.intCast_eq_intCast_iff]
      simp
    obtain ⟨r, hr⟩ := hdvd
    have hval : ((z + 1 : ZMod N).val : ℝ) =
        (z.val : ℝ) + 1 - (N : ℝ) * (r : ℝ) := by
      have := congr_arg (Int.cast (R := ℝ)) hr
      push_cast at this ⊢
      linarith
    have harg : circlePoint L N (z + 1) =
        circlePoint L N z + a - (r : ℝ) * L := by
      dsimp [circlePoint]
      rw [hval]
      field_simp [hN_ne]
      nlinarith [hphys]
    rw [harg]
    exact (periodizeCLM L h).periodic'.sub_int_mul_eq r
  have hpred :
      (periodizeCLM L h) (circlePoint L N (z - 1)) =
        (periodizeCLM L h) (circlePoint L N z - a) := by
    have hdvd : (N : ℤ) ∣ ((z.val : ℤ) - 1 - ((z - 1 : ZMod N).val : ℤ)) := by
      rw [← Int.modEq_iff_dvd, ← ZMod.intCast_eq_intCast_iff]
      simp
    obtain ⟨r, hr⟩ := hdvd
    have hval : ((z - 1 : ZMod N).val : ℝ) =
        (z.val : ℝ) - 1 - (N : ℝ) * (r : ℝ) := by
      have := congr_arg (Int.cast (R := ℝ)) hr
      push_cast at this ⊢
      linarith
    have harg : circlePoint L N (z - 1) =
        circlePoint L N z - a - (r : ℝ) * L := by
      dsimp [circlePoint]
      rw [hval]
      field_simp [hN_ne]
      nlinarith [hphys]
    rw [harg]
    exact (periodizeCLM L h).periodic'.sub_int_mul_eq r
  have hcenter_shift :
      (periodizeCLM L h) (circlePoint L N z + a) =
        (periodizeCLM L h) (t + a) := by
    by_cases hz : (ZMod.val z : ℤ) ≤ (N : ℤ) / 2
    · have hs' : s = (ZMod.val z : ℤ) := by
        dsimp [s, signedVal]
        rw [if_pos hz]
      dsimp only [t, circlePoint]
      simp [hs', ha_eq]
    · have hs' : s = (ZMod.val z : ℤ) - (N : ℤ) := by
        dsimp [s, signedVal]
        rw [if_neg hz]
      have hdiff : circlePoint L N z = t + L := by
        dsimp only [t, circlePoint]
        rw [hs']
        push_cast
        field_simp [hN_ne]
        ring
      rw [hdiff]
      simpa [add_assoc, add_comm, add_left_comm] using
        (periodizeCLM L h).periodic' (t + a)
  have hcenter_shift' :
      (periodizeCLM L h) (circlePoint L N z - a) =
        (periodizeCLM L h) (t - a) := by
    by_cases hz : (ZMod.val z : ℤ) ≤ (N : ℤ) / 2
    · have hs' : s = (ZMod.val z : ℤ) := by
        dsimp [s, signedVal]
        rw [if_pos hz]
      dsimp only [t, circlePoint]
      simp [hs', ha_eq]
    · have hs' : s = (ZMod.val z : ℤ) - (N : ℤ) := by
        dsimp [s, signedVal]
        rw [if_neg hz]
      have hdiff : circlePoint L N z = t + L := by
        dsimp only [t, circlePoint]
        rw [hs']
        push_cast
        field_simp [hN_ne]
        ring
      rw [hdiff]
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
        (periodizeCLM L h).periodic' (t - a)
  rw [circleRestriction_apply, circleRestriction_apply, circleRestriction_apply]
  rw [hcenter_eq, hsucc, hpred, hcenter_shift, hcenter_shift']
  have hsqrt : Real.sqrt (L / (N : ℝ)) = Real.sqrt a := by rw [ha_eq]
  rw [hsqrt]
  have hsq : 0 ≤ Real.sqrt a := Real.sqrt_nonneg _
  have hraw' := hraw
  rw [show 2 * (Real.sqrt a * (periodizeCLM L h).toFun t) -
      Real.sqrt a * (periodizeCLM L h).toFun (t + a) -
      Real.sqrt a * (periodizeCLM L h).toFun (t - a) =
      Real.sqrt a *
        (-( (periodizeCLM L h).toFun (t + a) +
            (periodizeCLM L h).toFun (t - a) -
            2 * (periodizeCLM L h).toFun t)) by ring]
  rw [abs_mul, abs_of_nonneg hsq, abs_neg]
  calc
    Real.sqrt a * |(a ^ 2 : ℝ)⁻¹ *
        ((periodizeCLM L h).toFun (t + a) +
          (periodizeCLM L h).toFun (t - a) -
          2 * (periodizeCLM L h).toFun t)| ≤
      Real.sqrt a *
        ((16 + 288 * (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2)) * q h /
          (1 + |t|) ^ 2) := by
      exact mul_le_mul_of_nonneg_left hraw (Real.sqrt_nonneg _)
    _ = Real.sqrt a *
        (16 + 288 * (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2)) * q h /
          (1 + |((signedVal N z : ℤ) : ℝ) * L / N|) ^ 2 := by
      dsimp [t, s]
      ring

end Pphi2
