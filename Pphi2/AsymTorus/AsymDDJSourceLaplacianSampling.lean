/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Centered finite-Laplacian bounds for the DDJ source

This file keeps the finite Laplacian at the source level.  The temporal
factor is handled by the centered periodization estimate, and the spatial
factor by the one-dimensional restriction estimate from GaussianField.
-/

import Pphi2.AsymTorus.AsymDDJSourceSampling
import Pphi2.IRLimit.DDJSchwartzSecondDifference

noncomputable section

namespace Pphi2

open GaussianField MeasureTheory

private def lapTemporalSeminorm : Seminorm ℝ (SchwartzMap ℝ ℝ) :=
  (Finset.Iic ((2 : ℕ), (0 : ℕ))).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) +
    centeredSecondDiffSeminorm

private theorem lapTemporalSeminorm_continuous :
    Continuous lapTemporalSeminorm := by
  apply Continuous.add
  · refine Seminorm.continuous_of_le
      (p := (Finset.Iic ((2 : ℕ), (0 : ℕ))).sup
        (fun m => SchwartzMap.seminorm ℝ m.1 m.2))
      (q := ∑ m ∈ Finset.Iic ((2 : ℕ), (0 : ℕ)),
        SchwartzMap.seminorm ℝ m.1 m.2) ?_ ?_
    · change Continuous fun h : SchwartzMap ℝ ℝ =>
        (∑ m ∈ Finset.Iic ((2 : ℕ), (0 : ℕ)),
          SchwartzMap.seminorm ℝ m.1 m.2) h
      simpa only [SchwartzMap.schwartzSeminormFamily_apply] using
        (continuous_finsetSum (Finset.Iic ((2 : ℕ), (0 : ℕ))) fun m _ =>
          (schwartz_withSeminorms (𝕜 := ℝ) (E := ℝ) (F := ℝ)).continuous_seminorm m)
    · simpa only using
        (Seminorm.finset_sup_le_sum
          (𝕜 := ℝ) (E := SchwartzMap ℝ ℝ)
          (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2)
          (Finset.Iic ((2 : ℕ), (0 : ℕ))))
  · exact centeredSecondDiffSeminorm_continuous

private theorem lapTemporalSeminorm_nonneg (h : SchwartzMap ℝ ℝ) :
    0 ≤ lapTemporalSeminorm h :=
  apply_nonneg _ _

private theorem lapTemporalSeminorm_basis_poly_bound :
    ∃ D : ℝ, 0 < D ∧ ∃ S : ℕ, ∀ m : ℕ,
      lapTemporalSeminorm
          (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) m) ≤
        D * (1 + (m : ℝ)) ^ S := by
  classical
  obtain ⟨t, Cnn, hCnn, hle⟩ := Seminorm.bound_of_continuous
    (schwartz_withSeminorms (𝕜 := ℝ) (E := ℝ) (F := ℝ))
    lapTemporalSeminorm lapTemporalSeminorm_continuous
  obtain ⟨D, hD, S, hb⟩ := GaussianField.finset_sup_poly_bound
    (DyninMityaginSpace.p (E := SchwartzMap ℝ ℝ)) t
    (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ))
    (fun i _ => DyninMityaginSpace.basis_growth
      (E := SchwartzMap ℝ ℝ) i)
  refine ⟨(Cnn : ℝ) * D, ?_, S, ?_⟩
  · have hCpos : (0 : ℝ) < Cnn :=
      NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hCnn)
    positivity
  · intro m
    calc
      lapTemporalSeminorm
          (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) m) ≤
          (Cnn : ℝ) *
            (t.sup (DyninMityaginSpace.p (E := SchwartzMap ℝ ℝ)))
              (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) m) := hle _
      _ ≤ (Cnn : ℝ) * (D * (1 + (m : ℝ)) ^ S) := by
        exact mul_le_mul_of_nonneg_left (hb m) (NNReal.coe_nonneg Cnn)
      _ = (Cnn : ℝ) * D * (1 + (m : ℝ)) ^ S := by ring

private theorem lapSpatialBasis_bounds
    (Ls : ℝ) [Fact (0 < Ls)] :
    ∃ C₀ C₂ : ℝ, 0 < C₀ ∧ 0 < C₂ ∧
      (∀ (Ns : ℕ) [NeZero Ns] (z : ZMod Ns) (m : ℕ),
        |circleRestriction Ls Ns
            (DyninMityaginSpace.basis
              (E := SmoothMap_Circle Ls ℝ) m) z| ≤
          Real.sqrt (Ls / Ns) * C₀) ∧
      (∀ (Ns : ℕ) [NeZero Ns] (m : ℕ) (z : ZMod Ns),
        |(circleSpacing Ls Ns)⁻¹ ^ 2 *
            (2 * circleRestriction Ls Ns
              (DyninMityaginSpace.basis
                (E := SmoothMap_Circle Ls ℝ) m) z -
             circleRestriction Ls Ns
              (DyninMityaginSpace.basis
                (E := SmoothMap_Circle Ls ℝ) m) (z + 1) -
             circleRestriction Ls Ns
              (DyninMityaginSpace.basis
                (E := SmoothMap_Circle Ls ℝ) m) (z - 1))| ≤
          Real.sqrt (circleSpacing Ls Ns) *
            (C₂ * (1 + (m : ℝ)) ^ 2)) := by
  obtain ⟨C₀, hC₀, hC₀b⟩ :=
    SmoothMap_Circle.sobolevSeminorm_fourierBasis_le (L := Ls) 0
  obtain ⟨C₂, hC₂, hC₂b⟩ :=
    SmoothMap_Circle.sobolevSeminorm_fourierBasis_le (L := Ls) 2
  refine ⟨C₀, C₂, hC₀, hC₂, ?_, ?_⟩
  · intro Ns _ z m
    rw [dm_basis_eq_fourierBasis (L := Ls) m, circleRestriction_apply,
      circleSpacing_eq, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    calc
      |(SmoothMap_Circle.fourierBasis (L := Ls) m : ℝ → ℝ)
          (circlePoint Ls Ns z)| =
          ‖iteratedDeriv 0
            ((SmoothMap_Circle.fourierBasis (L := Ls) m : ℝ → ℝ))
            (circlePoint Ls Ns z)‖ := by
        rw [iteratedDeriv_zero, Real.norm_eq_abs]
      _ ≤ SmoothMap_Circle.sobolevSeminorm 0
          (SmoothMap_Circle.fourierBasis m) :=
        SmoothMap_Circle.norm_iteratedDeriv_le_sobolevSeminorm' _ 0 _
      _ ≤ C₀ := by
        simpa only [pow_zero, mul_one] using hC₀b m
  · intro Ns _ m z
    rw [dm_basis_eq_fourierBasis (L := Ls) m]
    have hlap := negLaplacian_restriction_bound Ls Ns
      (DyninMityaginSpace.basis
        (E := SmoothMap_Circle Ls ℝ) m) z
    rw [dm_basis_eq_fourierBasis (L := Ls) m] at hlap
    calc
      |(circleSpacing Ls Ns)⁻¹ ^ 2 *
          (2 * circleRestriction Ls Ns
            (SmoothMap_Circle.fourierBasis (L := Ls) m) z -
           circleRestriction Ls Ns
            (SmoothMap_Circle.fourierBasis (L := Ls) m) (z + 1) -
           circleRestriction Ls Ns
            (SmoothMap_Circle.fourierBasis (L := Ls) m) (z - 1))| ≤
        Real.sqrt (circleSpacing Ls Ns) *
          SmoothMap_Circle.sobolevSeminorm 2
            (SmoothMap_Circle.fourierBasis m) := hlap
      _ ≤ Real.sqrt (circleSpacing Ls Ns) *
          (C₂ * (1 + (m : ℝ)) ^ 2) := by
        gcongr
        exact hC₂b m

private theorem lapTemporal_zero_bound
    (h : SchwartzMap ℝ ℝ) (Lt : ℝ) [Fact (0 < Lt)]
    (hLt1 : 1 ≤ Lt) (Nt : ℕ) [NeZero Nt] (a : ℝ) (ha : 0 < a)
    (hphys : (Nt : ℝ) * a = Lt) (z : ZMod Nt) :
    |circleRestriction Lt Nt (periodizeCLM Lt h) z| ≤
      Real.sqrt a *
        (4 + 72 * (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2)) *
        ((Finset.Iic ((2 : ℕ), (0 : ℕ))).sup
          (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) h /
        (1 + a * ((signedVal Nt z).natAbs : ℝ)) ^ 2 := by
  have hN_pos : (0 : ℝ) < Nt := Nat.cast_pos.mpr (NeZero.pos Nt)
  have hratio : Lt / (Nt : ℝ) = a := by
    rw [← hphys]
    field_simp [ne_of_gt hN_pos]
  have hperiod := periodizeCLM_circlePoint_centered_decay h Lt hLt1 Nt z
  rw [circleRestriction_apply, circleSpacing_eq, hratio]
  have hsqrt : Real.sqrt (Lt / (Nt : ℝ)) = Real.sqrt a := by rw [hratio]
  rw [hsqrt]
  have hden :
      1 + |((signedVal Nt z : ℤ) : ℝ) * Lt / Nt| =
        1 + a * ((signedVal Nt z).natAbs : ℝ) := by
    have hs_abs : ((signedVal Nt z).natAbs : ℝ) =
        |(signedVal Nt z : ℤ) : ℝ| := by
      simpa using (Nat.cast_natAbs (α := ℝ) (signedVal Nt z))
    rw [show ((signedVal Nt z : ℤ) : ℝ) * Lt / Nt =
        ((signedVal Nt z : ℤ) : ℝ) * (Lt / Nt) by ring,
      hratio, abs_mul, abs_of_pos ha, hs_abs]
    ring
  rw [hden] at hperiod
  calc
    Real.sqrt a *
        |(periodizeCLM Lt h).toFun (circlePoint Lt Nt z)| ≤
        Real.sqrt a *
          ((4 + 72 * (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2)) *
            ((Finset.Iic ((2 : ℕ), (0 : ℕ))).sup
              (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) h /
            (1 + a * ((signedVal Nt z).natAbs : ℝ)) ^ 2) := by
      exact mul_le_mul_of_nonneg_left hperiod (Real.sqrt_nonneg _)
    _ = Real.sqrt a *
          (4 + 72 * (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2)) *
          ((Finset.Iic ((2 : ℕ), (0 : ℕ))).sup
            (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) h /
          (1 + a * ((signedVal Nt z).natAbs : ℝ)) ^ 2 := by ring

theorem asymFiniteLaplacianRawSource_pointwise_centered_decay
    (Ls : ℝ) [Fact (0 < Ls)] :
    ∃ (A : ℝ) (q : Seminorm ℝ (CylinderTestFunction Ls)),
      0 < A ∧ Continuous q ∧
      ∀ (Lt : ℝ) [Fact (0 < Lt)], 4 ≤ Lt →
        ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
          (a : ℝ) (ha : 0 < a),
          (Nt : ℝ) * a = Lt → (Ns : ℝ) * a = Ls → a ≤ 1 →
          ∀ (f : CylinderTestFunction Ls)
            (x : AsymLatticeSites Nt Ns),
            |finiteLaplacianAsymFun Nt Ns a
                (asymRawSource a
                  (asymLatticeTestFnIso Lt Ls Nt Ns a
                    (cylinderToTorusEmbed Lt Ls f))) x| ≤
              A * q f /
                (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2 := by
  obtain ⟨D, hD, S, hDb⟩ := lapTemporalSeminorm_basis_poly_bound
  obtain ⟨C₀, C₂, hC₀, hC₂, hC₀b, hC₂b⟩ :=
    lapSpatialBasis_bounds Ls
  let K₀ : ℝ := 4 + 72 * (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2)
  let K₂ : ℝ := 16 + 288 * (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2)
  let A : ℝ := D * (K₂ * C₀ + K₀ * C₂)
  let q : Seminorm ℝ (CylinderTestFunction Ls) :=
    RapidDecaySeq.rapidDecaySeminorm (S + 2)
  refine ⟨A, q, ?_, ?_, ?_⟩
  · dsimp [A, K₀, K₂]
    positivity
  · exact RapidDecaySeq.rapidDecay_withSeminorms.continuous_seminorm (S + 2)
  · intro Lt hLt hLt4 Nt Ns _ _ a ha hLtphys hLsphys ha1 f x
    have hLt1 : 1 ≤ Lt := by linarith
    let R : AsymLatticeSites Nt Ns →
        CylinderTestFunction Ls →L[ℝ] ℝ := fun y =>
      (a⁻¹ : ℝ) •
        (evalAsymTorusAtSite Lt Ls Nt Ns y).comp
          (cylinderToTorusEmbed Lt Ls)
    let T : CylinderTestFunction Ls →L[ℝ] ℝ :=
      (a⁻¹ ^ 2 : ℝ) •
        (R (x.1 + 1, x.2) + R (x.1 - 1, x.2) +
          R (x.1, x.2 + 1) + R (x.1, x.2 - 1) - (4 : ℝ) • R x)
    have hTf : T f = finiteLaplacianAsymFun Nt Ns a
        (asymRawSource a
          (asymLatticeTestFnIso Lt Ls Nt Ns a
            (cylinderToTorusEmbed Lt Ls f))) x := by
      dsimp [T, R]
      simp [finiteLaplacianAsymFun,
        asymRawSource_asymLatticeTestFnIso_apply, smul_eq_mul,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
      ring
    have hN_pos : (0 : ℝ) < Nt := Nat.cast_pos.mpr (NeZero.pos Nt)
    have hNs_pos : (0 : ℝ) < Ns := Nat.cast_pos.mpr (NeZero.pos Ns)
    have hLt_ratio : Lt / (Nt : ℝ) = a := by
      rw [← hLtphys]
      field_simp [ne_of_gt hN_pos]
    have hLs_ratio : Ls / (Ns : ℝ) = a := by
      rw [← hLsphys]
      field_simp [ne_of_gt hNs_pos]
    have hden :
        1 + |((signedVal Nt x.1 : ℤ) : ℝ) * Lt / Nt| =
          1 + a * ((signedVal Nt x.1).natAbs : ℝ) := by
      have hs_abs : ((signedVal Nt x.1).natAbs : ℝ) =
          |(signedVal Nt x.1 : ℤ) : ℝ| := by
        simpa using (Nat.cast_natAbs (α := ℝ) (signedVal Nt x.1))
      rw [show ((signedVal Nt x.1 : ℤ) : ℝ) * Lt / Nt =
          ((signedVal Nt x.1 : ℤ) : ℝ) * (Lt / Nt) by ring,
        hLt_ratio, abs_mul, abs_of_pos ha, hs_abs]
      ring
    have hroot : |a⁻¹| * Real.sqrt a * Real.sqrt a = 1 := by
      rw [abs_of_pos (inv_pos.mpr ha)]
      have hsqrt : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha.le
      field_simp [ne_of_gt ha]
      nlinarith
    have hbasis : ∀ m : ℕ,
        |T (RapidDecaySeq.basisVec m)| ≤
          A * (1 + (m : ℝ)) ^ (S + 2) /
            (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2 := by
      intro m
      let i := (Nat.unpair m).1
      let j := (Nat.unpair m).2
      have him : i ≤ m := by exact Nat.unpair_left_le m
      have hjm : j ≤ m := by exact Nat.unpair_right_le m
      have him_real : (1 + (i : ℝ)) ≤ 1 + (m : ℝ) := by
        have him_cast : (i : ℝ) ≤ (m : ℝ) := by
          exact_mod_cast him
        linarith
      have hjm_real : (1 + (j : ℝ)) ≤ 1 + (m : ℝ) := by
        have hjm_cast : (j : ℝ) ≤ (m : ℝ) := by
          exact_mod_cast hjm
        linarith
      have hpow2 : (1 + (i : ℝ)) ^ 2 ≤ (1 + (m : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) him_real 2
      have hpow : (1 + (j : ℝ)) ^ S ≤ (1 + (m : ℝ)) ^ S :=
        pow_le_pow_left₀ (by positivity) hjm_real S
      have hpow_extra : (1 + (m : ℝ)) ^ S ≤
          (1 + (m : ℝ)) ^ (S + 2) := by
        rw [pow_add]
        calc
          (1 + (m : ℝ)) ^ S =
              (1 + (m : ℝ)) ^ S * 1 := by ring
          _ ≤ (1 + (m : ℝ)) ^ S * (1 + (m : ℝ)) ^ 2 := by
            gcongr
            have hm_nonneg : (0 : ℝ) ≤ (m : ℝ) := by positivity
            nlinarith [sq_nonneg (m : ℝ)]
      have hsem : lapTemporalSeminorm
          (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) j) ≤
          D * (1 + (m : ℝ)) ^ S := by
        exact (hDb j).trans
          (mul_le_mul_of_nonneg_left hpow (le_of_lt hD))
      have hq0 :
          ((Finset.Iic ((2 : ℕ), (0 : ℕ))).sup
            (fun r => SchwartzMap.seminorm ℝ r.1 r.2))
            (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) j) ≤
          lapTemporalSeminorm
            (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) j) := by
        exact le_add_of_nonneg_right
          (apply_nonneg centeredSecondDiffSeminorm _)
      have hq2 : centeredSecondDiffSeminorm
          (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) j) ≤
          lapTemporalSeminorm
            (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) j) := by
        exact le_add_of_nonneg_left
          (apply_nonneg _ _)
      let bt : SchwartzMap ℝ ℝ :=
        DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) j
      let bs : SmoothMap_Circle Ls ℝ :=
        DyninMityaginSpace.basis (E := SmoothMap_Circle Ls ℝ) i
      let ct : ZMod Nt → ℝ := fun z =>
        circleRestriction Lt Nt (periodizeCLM Lt bt) z
      let cs : ZMod Ns → ℝ := fun z => circleRestriction Ls Ns bs z
      have htem0 := lapTemporal_zero_bound bt Lt hLt1 Nt a ha hLtphys x.1
      have htem0' :
          |ct x.1| ≤ Real.sqrt a * K₀ * (D * (1 + (m : ℝ)) ^ S) /
            (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2 := by
        dsimp [ct] at ⊢
        dsimp [K₀] at htem0 ⊢
        calc
          |circleRestriction Lt Nt (periodizeCLM Lt bt) x.1| ≤
              Real.sqrt a *
                  (4 + 72 * (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2)) *
                ((Finset.Iic ((2 : ℕ), (0 : ℕ))).sup
                  (fun r => SchwartzMap.seminorm ℝ r.1 r.2)) bt /
                (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2 := htem0
          _ ≤ Real.sqrt a *
                  (4 + 72 * (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2)) *
                (D * (1 + (m : ℝ)) ^ S) /
                (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2 := by
            apply div_le_div_of_nonneg_right
            · simpa only [mul_assoc] using
                (mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left
                    (by simpa [bt] using hq0.trans hsem) (by positivity))
                  (by positivity))
            · positivity
      have htem2 := periodizeCLM_circlePoint_centered_second_diff_decay
        bt centeredSecondDiffSeminorm centeredSecondDiffSeminorm_continuous
        Lt hLt4 Nt a ha ha1 hLtphys x.1
        (fun y => centeredSecondDiffSeminorm_second_diff_decay bt a y ha ha1)
      have htem2' :
          |(a ^ 2 : ℝ)⁻¹ *
              (ct (x.1 + 1) + ct (x.1 - 1) - 2 * ct x.1)| ≤
            Real.sqrt a * K₂ * (D * (1 + (m : ℝ)) ^ S) /
              (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2 := by
        have hsign :
            (a ^ 2 : ℝ)⁻¹ *
                (ct (x.1 + 1) + ct (x.1 - 1) - 2 * ct x.1) =
              -((a ^ 2 : ℝ)⁻¹ *
                (2 * ct x.1 - ct (x.1 + 1) - ct (x.1 - 1))) := by
          ring
        rw [hsign, abs_neg]
        rw [hden] at htem2
        dsimp [ct, K₂] at htem2 ⊢
        calc
          |(a ^ 2 : ℝ)⁻¹ *
              (2 * ct x.1 - ct (x.1 + 1) - ct (x.1 - 1))| ≤
              Real.sqrt a *
                  (16 + 288 * (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2)) *
                centeredSecondDiffSeminorm bt /
                (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2 := htem2
          _ ≤ Real.sqrt a *
                  (16 + 288 * (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2)) *
                (D * (1 + (m : ℝ)) ^ S) /
                (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2 := by
            apply div_le_div_of_nonneg_right
            · simpa only [mul_assoc] using
                (mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left
                    (by simpa [bt] using hq2.trans hsem) (by positivity))
                  (by positivity))
            · positivity
      have htem2_bound_nonneg :
          0 ≤ Real.sqrt a * K₂ * (D * (1 + (m : ℝ)) ^ S) /
            (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2 :=
        (abs_nonneg _).trans htem2'
      have hsp0 : |cs x.2| ≤ Real.sqrt a * C₀ := by
        dsimp [cs, bs]
        simpa [hLs_ratio] using hC₀b Ns x.2 i
      have hsp2 := hC₂b Ns i x.2
      have hsp2' :
          |(a ^ 2 : ℝ)⁻¹ *
              (cs (x.2 + 1) + cs (x.2 - 1) - 2 * cs x.2)| ≤
            Real.sqrt a * C₂ * (1 + (m : ℝ)) ^ 2 := by
        have hsign :
            (a ^ 2 : ℝ)⁻¹ *
                (cs (x.2 + 1) + cs (x.2 - 1) - 2 * cs x.2) =
              -((a ^ 2 : ℝ)⁻¹ *
                (2 * cs x.2 - cs (x.2 + 1) - cs (x.2 - 1))) := by
          ring
        have hsp2_i :
            |(a ^ 2 : ℝ)⁻¹ *
                (cs (x.2 + 1) + cs (x.2 - 1) - 2 * cs x.2)| ≤
              Real.sqrt a * C₂ * (1 + (i : ℝ)) ^ 2 := by
          rw [hsign, abs_neg]
          dsimp [cs, bs]
          rw [show circleSpacing Ls Ns = a by
            simp [circleSpacing_eq, hLs_ratio]] at hsp2
          simpa [inv_pow, mul_assoc] using hsp2
        calc
          |(a ^ 2 : ℝ)⁻¹ *
                (cs (x.2 + 1) + cs (x.2 - 1) - 2 * cs x.2)| ≤
              Real.sqrt a * C₂ * (1 + (i : ℝ)) ^ 2 := hsp2_i
          _ ≤ Real.sqrt a * C₂ * (1 + (m : ℝ)) ^ 2 := by
            exact mul_le_mul_of_nonneg_left hpow2 (by positivity)
      have hEval : ∀ (y : AsymLatticeSites Nt Ns),
          evalAsymTorusAtSite Lt Ls Nt Ns y
              (cylinderToTorusEmbed Lt Ls
                (RapidDecaySeq.basisVec m)) =
            ct y.1 * cs y.2 := by
        intro y
        rw [show RapidDecaySeq.basisVec m =
            NuclearTensorProduct.pure
              (DyninMityaginSpace.basis
                (E := SmoothMap_Circle Ls ℝ) i)
              (DyninMityaginSpace.basis
                (E := SchwartzMap ℝ ℝ) j) by
          rw [NuclearTensorProduct.basisVec_eq_pure
            (DyninMityaginSpace.HasBiorthogonalBasis.coeff_basis
              (E := SmoothMap_Circle Ls ℝ))
            (DyninMityaginSpace.HasBiorthogonalBasis.coeff_basis
              (E := SchwartzMap ℝ ℝ)) m]]
        simp [cylinderToTorusEmbed_pure, evalAsymTorusAtSite,
          NuclearTensorProduct.evalCLM_pure,
          ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
          ct, cs, bt, bs]
      have hTbasis : T (RapidDecaySeq.basisVec m) =
          (a⁻¹) * ((a ^ 2 : ℝ)⁻¹ *
            (ct (x.1 + 1) + ct (x.1 - 1) - 2 * ct x.1)) * cs x.2 +
          (a⁻¹) * ct x.1 *
            ((a ^ 2 : ℝ)⁻¹ *
              (cs (x.2 + 1) + cs (x.2 - 1) - 2 * cs x.2)) := by
        dsimp [T, R]
        simp only [ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
          ContinuousLinearMap.comp_apply, smul_eq_mul]
        rw [hEval, hEval, hEval, hEval, hEval]
        ring
      have hterm₀ :
          |a⁻¹| *
              |(a ^ 2 : ℝ)⁻¹ *
                (ct (x.1 + 1) + ct (x.1 - 1) - 2 * ct x.1)| *
              |cs x.2| ≤
            K₂ * D * C₀ * (1 + (m : ℝ)) ^ (S + 2) /
              (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2 := by
        calc
          |a⁻¹| *
                |(a ^ 2 : ℝ)⁻¹ *
                  (ct (x.1 + 1) + ct (x.1 - 1) - 2 * ct x.1)| *
                |cs x.2| ≤
              |a⁻¹| *
                (Real.sqrt a * K₂ * (D * (1 + (m : ℝ)) ^ S) /
                  (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2) *
                |cs x.2| := by
            apply mul_le_mul_of_nonneg_right
            · exact mul_le_mul_of_nonneg_left htem2' (abs_nonneg _)
            · exact abs_nonneg _
          _ ≤ |a⁻¹| *
                (Real.sqrt a * K₂ * (D * (1 + (m : ℝ)) ^ S) /
                  (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2) *
                (Real.sqrt a * C₀) := by
            apply mul_le_mul_of_nonneg_left hsp0
            exact mul_nonneg (abs_nonneg _) htem2_bound_nonneg
          _ = (|a⁻¹| * Real.sqrt a * Real.sqrt a) *
                (K₂ * D * C₀ * (1 + (m : ℝ)) ^ S /
                  (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2) := by
            ring
          _ ≤ K₂ * D * C₀ * (1 + (m : ℝ)) ^ (S + 2) /
                (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2 := by
            rw [hroot, one_mul]
            apply div_le_div_of_nonneg_right
            · exact mul_le_mul_of_nonneg_left hpow_extra (by positivity)
            · positivity
      have htem0_bound_nonneg :
          0 ≤ Real.sqrt a * K₀ * (D * (1 + (m : ℝ)) ^ S) /
            (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2 :=
        (abs_nonneg _).trans htem0'
      have hterm₂ :
          |a⁻¹| * |ct x.1| *
              |(a ^ 2 : ℝ)⁻¹ *
                (cs (x.2 + 1) + cs (x.2 - 1) - 2 * cs x.2)| ≤
            K₀ * D * C₂ * (1 + (m : ℝ)) ^ (S + 2) /
              (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2 := by
        calc
          |a⁻¹| * |ct x.1| *
                |(a ^ 2 : ℝ)⁻¹ *
                  (cs (x.2 + 1) + cs (x.2 - 1) - 2 * cs x.2)| ≤
              |a⁻¹| *
                (Real.sqrt a * K₀ * (D * (1 + (m : ℝ)) ^ S) /
                  (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2) *
                |(a ^ 2 : ℝ)⁻¹ *
                  (cs (x.2 + 1) + cs (x.2 - 1) - 2 * cs x.2)| := by
            apply mul_le_mul_of_nonneg_right
            · exact mul_le_mul_of_nonneg_left htem0' (abs_nonneg _)
            · exact abs_nonneg _
          _ ≤ |a⁻¹| *
                (Real.sqrt a * K₀ * (D * (1 + (m : ℝ)) ^ S) /
                  (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2) *
                (Real.sqrt a * C₂ * (1 + (m : ℝ)) ^ 2) := by
            apply mul_le_mul_of_nonneg_left hsp2'
            exact mul_nonneg (abs_nonneg _) htem0_bound_nonneg
          _ = (|a⁻¹| * Real.sqrt a * Real.sqrt a) *
                (K₀ * D * C₂ * (1 + (m : ℝ)) ^ S *
                  (1 + (m : ℝ)) ^ 2 /
                  (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2) := by
            ring
          _ = K₀ * D * C₂ * (1 + (m : ℝ)) ^ (S + 2) /
                (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2 := by
            rw [hroot, pow_add]
            ring
      calc
        |T (RapidDecaySeq.basisVec m)| ≤
            |a⁻¹| *
                |(a ^ 2 : ℝ)⁻¹ *
                  (ct (x.1 + 1) + ct (x.1 - 1) - 2 * ct x.1)| *
                |cs x.2| +
              |a⁻¹| * |ct x.1| *
                |(a ^ 2 : ℝ)⁻¹ *
                  (cs (x.2 + 1) + cs (x.2 - 1) - 2 * cs x.2)| := by
          rw [hTbasis]
          exact abs_add_le _ _
        _ ≤ (K₂ * D * C₀ + K₀ * D * C₂) *
              (1 + (m : ℝ)) ^ (S + 2) /
              (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2 :=
          add_le_add hterm₀ hterm₂
        _ = A * (1 + (m : ℝ)) ^ (S + 2) /
              (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2 := by
          dsimp [A]
          ring
    rw [← hTf, DyninMityaginSpace.expansion T f]
    have hf_sum : Summable (fun m : ℕ =>
        |f.val m| * (1 + (m : ℝ)) ^ (S + 2)) := by
      simpa [q, RapidDecaySeq.rapidDecaySeminorm] using f.rapid_decay (S + 2)
    have hmajor : Summable (fun m : ℕ =>
        (A / (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2) *
          (|f.val m| * (1 + (m : ℝ)) ^ (S + 2))) :=
      hf_sum.mul_left _
    have hterm : ∀ m : ℕ, ‖f.val m * T
        (RapidDecaySeq.basisVec m)‖ ≤
        (A / (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2) *
          (|f.val m| * (1 + (m : ℝ)) ^ (S + 2)) := by
      intro m
      rw [Real.norm_eq_abs, abs_mul]
      have hTbasis := hbasis m
      calc
        |f.val m| * |T (RapidDecaySeq.basisVec m)| ≤
            |f.val m| *
              (A * (1 + (m : ℝ)) ^ (S + 2) /
                (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2) :=
          mul_le_mul_of_nonneg_left hTbasis (abs_nonneg _)
        _ = (A / (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2) *
            (|f.val m| * (1 + (m : ℝ)) ^ (S + 2)) := by ring
    have hsum : Summable (fun m : ℕ =>
        f.val m * T (RapidDecaySeq.basisVec m)) :=
      hmajor.of_norm_bounded hterm
    calc
      |∑' m, f.val m * T (RapidDecaySeq.basisVec m)| =
          ‖∑' m, f.val m * T (RapidDecaySeq.basisVec m)‖ :=
        (Real.norm_eq_abs _).symm
      _ ≤ ∑' m, ‖f.val m * T (RapidDecaySeq.basisVec m)‖ :=
        norm_tsum_le_tsum_norm hsum.norm
      _ ≤ ∑' m, (A / (1 + a *
          ((signedVal Nt x.1).natAbs : ℝ)) ^ 2) *
          (|f.val m| * (1 + (m : ℝ)) ^ (S + 2)) :=
        Summable.tsum_le_tsum hterm hsum.norm hmajor
      _ = A * q f /
          (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2 := by
        change (∑' m : ℕ,
            (A / (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2) *
            (|f.val m| * (1 + (m : ℝ)) ^ (S + 2))) =
          A * (∑' m : ℕ, |f.val m| * (1 + (m : ℝ)) ^ (S + 2)) /
            (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2
        rw [tsum_mul_left]
        ring

end Pphi2
