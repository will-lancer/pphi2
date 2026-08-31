/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Pointwise source control on the isotropic asymmetric lattice

The GJ-normalized lattice source is the physical source multiplied by the
inverse cell area.  For a cylinder test function its temporal factors are
periodized Schwartz functions.  The centered periodization estimate and the
Dynin-Mityagin expansion therefore give a uniform inverse-square bound in the
centered temporal lattice coordinate.
-/

import Pphi2.AsymTorus.AsymDDJSource
import Pphi2.IRLimit.CylinderEmbedding
import Pphi2.TorusContinuumLimit.TorusPropagatorConvergence

noncomputable section

namespace Pphi2

open GaussianField MeasureTheory

/-! The only Schwartz seminorm used by the centered periodization estimate. -/

private def centeredSchwartzSeminorm : Seminorm ℝ (SchwartzMap ℝ ℝ) :=
  (Finset.Iic ((2 : ℕ), (0 : ℕ))).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2)

private theorem centeredSchwartzSeminorm_continuous :
    Continuous centeredSchwartzSeminorm := by
  refine Seminorm.continuous_of_le
    (p := centeredSchwartzSeminorm)
    (q := ∑ m ∈ Finset.Iic ((2 : ℕ), (0 : ℕ)),
      SchwartzMap.seminorm ℝ m.1 m.2) ?_ ?_
  · change Continuous fun h : SchwartzMap ℝ ℝ =>
      (∑ m ∈ Finset.Iic ((2 : ℕ), (0 : ℕ)),
        SchwartzMap.seminorm ℝ m.1 m.2) h
    simpa only [SchwartzMap.schwartzSeminormFamily_apply] using
      (continuous_finsetSum (Finset.Iic ((2 : ℕ), (0 : ℕ))) fun m _ =>
        (schwartz_withSeminorms (𝕜 := ℝ) (E := ℝ) (F := ℝ)).continuous_seminorm m)
  · simpa only [centeredSchwartzSeminorm] using
      (Seminorm.finset_sup_le_sum
        (𝕜 := ℝ) (E := SchwartzMap ℝ ℝ)
        (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2)
        (Finset.Iic ((2 : ℕ), (0 : ℕ))))

private theorem centeredSchwartzSeminorm_basis_poly_bound :
    ∃ D : ℝ, 0 < D ∧ ∃ S : ℕ, ∀ m : ℕ,
      centeredSchwartzSeminorm
          (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) m) ≤
        D * (1 + (m : ℝ)) ^ S := by
  classical
  obtain ⟨t, Cnn, hCnn, hle⟩ := Seminorm.bound_of_continuous
    (schwartz_withSeminorms (𝕜 := ℝ) (E := ℝ) (F := ℝ))
    centeredSchwartzSeminorm centeredSchwartzSeminorm_continuous
  obtain ⟨D, hD, S, hb⟩ := GaussianField.finset_sup_poly_bound
    (DyninMityaginSpace.p (E := SchwartzMap ℝ ℝ))
    t
    (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ))
    (fun i _ => DyninMityaginSpace.basis_growth
      (E := SchwartzMap ℝ ℝ) i)
  refine ⟨(Cnn : ℝ) * D, ?_, S, ?_⟩
  · have hCpos : (0 : ℝ) < Cnn :=
      NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hCnn)
    positivity
  · intro m
    calc
      centeredSchwartzSeminorm
          (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) m) ≤
          (Cnn : ℝ) *
            (t.sup (DyninMityaginSpace.p (E := SchwartzMap ℝ ℝ)))
              (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) m) := hle _
      _ ≤ (Cnn : ℝ) * (D * (1 + (m : ℝ)) ^ S) := by
        exact mul_le_mul_of_nonneg_left (hb m) (NNReal.coe_nonneg Cnn)
      _ = (Cnn : ℝ) * D * (1 + (m : ℝ)) ^ S := by ring

private theorem cylinderSpatialBasis_pointwise_bound
    {Ls : ℝ} [Fact (0 < Ls)] :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ns : ℕ) [NeZero Ns]
      (x : ZMod Ns) (m : ℕ),
      |circleRestriction Ls Ns
          (DyninMityaginSpace.basis (E := SmoothMap_Circle Ls ℝ) m) x| ≤
        Real.sqrt (Ls / Ns) * C := by
  obtain ⟨C, hC, hCb⟩ :=
    SmoothMap_Circle.sobolevSeminorm_fourierBasis_le (L := Ls) 0
  refine ⟨C, hC, ?_⟩
  intro Ns _ x m
  rw [dm_basis_eq_fourierBasis (L := Ls) m, circleRestriction_apply,
    circleSpacing_eq, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  calc
    |(SmoothMap_Circle.fourierBasis (L := Ls) m : ℝ → ℝ)
        (circlePoint Ls Ns x)| =
        ‖iteratedDeriv 0
          ((SmoothMap_Circle.fourierBasis (L := Ls) m : ℝ → ℝ))
          (circlePoint Ls Ns x)‖ := by
      rw [iteratedDeriv_zero, Real.norm_eq_abs]
    _ ≤ SmoothMap_Circle.sobolevSeminorm 0
        (SmoothMap_Circle.fourierBasis m) :=
      SmoothMap_Circle.norm_iteratedDeriv_le_sobolevSeminorm' _ 0 _
    _ ≤ C := by
      simpa only [pow_zero, mul_one] using hCb m

private theorem cylinderEmbeddedBasis_raw_bound
    (Lt Ls : ℝ) [Fact (0 < Lt)] [Fact (0 < Ls)]
    (hLt1 : 1 ≤ Lt)
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a : ℝ) (ha : 0 < a)
    (hLt : (Nt : ℝ) * a = Lt) (hLs : (Ns : ℝ) * a = Ls)
    (D : ℝ) (hD : 0 < D) (S : ℕ)
    (hDb : ∀ r : ℕ,
      centeredSchwartzSeminorm
          (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) r) ≤
        D * (1 + (r : ℝ)) ^ S)
    (Cs : ℝ) (hCs : 0 < Cs)
    (hCsp : ∀ (Ns : ℕ) [NeZero Ns] (x : ZMod Ns) (r : ℕ),
      |circleRestriction Ls Ns
          (DyninMityaginSpace.basis (E := SmoothMap_Circle Ls ℝ) r) x| ≤
        Real.sqrt (Ls / Ns) * Cs)
    (m : ℕ) (x : AsymLatticeSites Nt Ns) :
    |asymRawSource a
        (asymLatticeTestFnIso Lt Ls Nt Ns a
          (cylinderToTorusEmbed Lt Ls
            (RapidDecaySeq.basisVec m))) x| ≤
      (4 + 72 * (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2)) *
        D * Cs * (1 + (m : ℝ)) ^ S /
          (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2 := by
  let i := (Nat.unpair m).1
  let j := (Nat.unpair m).2
  have hNt_pos : (0 : ℝ) < Nt := Nat.cast_pos.mpr (NeZero.pos Nt)
  have hNs_pos : (0 : ℝ) < Ns := Nat.cast_pos.mpr (NeZero.pos Ns)
  have hLt_ratio : Lt / (Nt : ℝ) = a := by
    rw [← hLt]
    field_simp [ne_of_gt hNt_pos]
  have hLs_ratio : Ls / (Ns : ℝ) = a := by
    rw [← hLs]
    field_simp [ne_of_gt hNs_pos]
  have htem := periodizeCLM_circlePoint_centered_decay
    (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) j)
    Lt hLt1 Nt x.1
  have htem' :
      |(periodizeCLM Lt
          (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) j)).toFun
          (circlePoint Lt Nt x.1)| ≤
        (4 + 72 * (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2)) *
          D * (1 + (m : ℝ)) ^ S /
            (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2 := by
    have hjm : j ≤ m := by
      exact Nat.unpair_right_le m
    have hjm_real : (1 + (j : ℝ)) ≤ 1 + (m : ℝ) := by
      have hjm_cast : (j : ℝ) ≤ (m : ℝ) := by
        exact_mod_cast hjm
      linarith
    have hpow : (1 + (j : ℝ)) ^ S ≤ (1 + (m : ℝ)) ^ S := by
      exact pow_le_pow_left₀ (by positivity) hjm_real S
    have hsem : centeredSchwartzSeminorm
          (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) j) ≤
        D * (1 + (m : ℝ)) ^ S := by
      exact (hDb j).trans
        (mul_le_mul_of_nonneg_left hpow (le_of_lt hD))
    have hden :
        1 + |((signedVal Nt x.1 : ℤ) : ℝ) * Lt / Nt| =
          1 + a * ((signedVal Nt x.1).natAbs : ℝ) := by
      have hs_abs : ((signedVal Nt x.1).natAbs : ℝ) =
          |((signedVal Nt x.1 : ℤ) : ℝ)| := by
        simpa using (Nat.cast_natAbs (α := ℝ) (signedVal Nt x.1))
      rw [show ((signedVal Nt x.1 : ℤ) : ℝ) * Lt / Nt =
          ((signedVal Nt x.1 : ℤ) : ℝ) * (Lt / Nt) by ring,
        hLt_ratio, abs_mul, abs_of_pos ha, hs_abs]
      ring
    calc
      |(periodizeCLM Lt
          (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) j)).toFun
          (circlePoint Lt Nt x.1)| ≤
          (4 + 72 * (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2)) *
            centeredSchwartzSeminorm
              (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) j) /
            (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2 := by
          simpa only [hden] using htem
      _ ≤ (4 + 72 * (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2)) *
            (D * (1 + (m : ℝ)) ^ S) /
            (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2 := by
          apply div_le_div_of_nonneg_right
          · exact mul_le_mul_of_nonneg_left hsem (by positivity)
          · positivity
      _ = (4 + 72 * (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2)) *
            D * (1 + (m : ℝ)) ^ S /
            (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2 := by ring
  have hsp' := hCsp Ns x.2 i
  have htem_bound_nonneg :
      0 ≤
        (4 + 72 * (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2)) *
          D * (1 + (m : ℝ)) ^ S /
            (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2 :=
    (abs_nonneg _).trans htem'
  have hformula :
      asymRawSource a
        (asymLatticeTestFnIso Lt Ls Nt Ns a
          (cylinderToTorusEmbed Lt Ls
            (RapidDecaySeq.basisVec m))) x =
      a⁻¹ *
        (circleRestriction Lt Nt
          (periodizeCLM Lt
            (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) j)) x.1) *
        (circleRestriction Ls Ns
          (DyninMityaginSpace.basis (E := SmoothMap_Circle Ls ℝ) i) x.2) := by
    rw [asymRawSource_asymLatticeTestFnIso_apply Lt Ls Nt Ns a ha]
    rw [show RapidDecaySeq.basisVec m =
        NuclearTensorProduct.pure
          (DyninMityaginSpace.basis (E := SmoothMap_Circle Ls ℝ) i)
          (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) j) by
      rw [NuclearTensorProduct.basisVec_eq_pure
        (DyninMityaginSpace.HasBiorthogonalBasis.coeff_basis
          (E := SmoothMap_Circle Ls ℝ))
        (DyninMityaginSpace.HasBiorthogonalBasis.coeff_basis
          (E := SchwartzMap ℝ ℝ)) m]]

    simp [cylinderToTorusEmbed_pure, evalAsymTorusAtSite,
      NuclearTensorProduct.evalCLM_pure, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply]
    ring
  rw [hformula, abs_mul, abs_mul, abs_of_pos (inv_pos.mpr ha)]
  have htem_apply :
      circleRestriction Lt Nt
          (periodizeCLM Lt
            (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) j)) x.1 =
        Real.sqrt (Lt / Nt) *
          (periodizeCLM Lt
            (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) j)).toFun
            (circlePoint Lt Nt x.1) := by
    rw [circleRestriction_apply, circleSpacing_eq]
    rfl
  rw [htem_apply, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hroot : a⁻¹ * Real.sqrt (Lt / Nt) * Real.sqrt (Ls / Ns) = 1 := by
    rw [hLt_ratio, hLs_ratio]
    have hsqrt : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha.le
    field_simp [ne_of_gt ha]
    nlinarith
  calc
    a⁻¹ * (Real.sqrt (Lt / Nt) *
          |(periodizeCLM Lt
            (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) j)).toFun
            (circlePoint Lt Nt x.1)|) *
        |circleRestriction Ls Ns
          (DyninMityaginSpace.basis (E := SmoothMap_Circle Ls ℝ) i) x.2| ≤
      a⁻¹ * Real.sqrt (Lt / Nt) * Real.sqrt (Ls / Ns) *
        ((4 + 72 * (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2)) *
            D * (1 + (m : ℝ)) ^ S /
            (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2) * Cs := by
      calc
        a⁻¹ * (Real.sqrt (Lt / Nt) *
              |(periodizeCLM Lt
                (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) j)).toFun
                (circlePoint Lt Nt x.1)|) *
            |circleRestriction Ls Ns
              (DyninMityaginSpace.basis (E := SmoothMap_Circle Ls ℝ) i) x.2| =
          (a⁻¹ * Real.sqrt (Lt / Nt)) *
              |(periodizeCLM Lt
                (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) j)).toFun
                (circlePoint Lt Nt x.1)| *
            |circleRestriction Ls Ns
              (DyninMityaginSpace.basis (E := SmoothMap_Circle Ls ℝ) i) x.2| := by
          ring
        _ ≤ (a⁻¹ * Real.sqrt (Lt / Nt)) *
              ((4 + 72 * (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2)) *
                D * (1 + (m : ℝ)) ^ S /
                (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2) *
            |circleRestriction Ls Ns
              (DyninMityaginSpace.basis (E := SmoothMap_Circle Ls ℝ) i) x.2| := by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_left htem' (by positivity)
          · exact abs_nonneg _
        _ ≤ (a⁻¹ * Real.sqrt (Lt / Nt)) *
              ((4 + 72 * (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2)) *
                D * (1 + (m : ℝ)) ^ S /
                (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2) *
            (Real.sqrt (Ls / Ns) * Cs) := by
          apply mul_le_mul_of_nonneg_left hsp'
          exact mul_nonneg
            (mul_nonneg (inv_nonneg.mpr ha.le) (Real.sqrt_nonneg _))
            htem_bound_nonneg
        _ = a⁻¹ * Real.sqrt (Lt / Nt) * Real.sqrt (Ls / Ns) *
              ((4 + 72 * (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2)) *
                D * (1 + (m : ℝ)) ^ S /
                (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2) * Cs := by
          ring
    _ = (4 + 72 * (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2)) *
        D * Cs * (1 + (m : ℝ)) ^ S /
          (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2 := by
      rw [hroot]
      ring

/-! The source bound for arbitrary cylinder tests. -/

theorem asymRawSource_pointwise_centered_decay
    (Ls : ℝ) [Fact (0 < Ls)] :
    ∃ (A : ℝ) (q : Seminorm ℝ (CylinderTestFunction Ls)),
      0 < A ∧ Continuous q ∧
      ∀ (Lt : ℝ) [Fact (0 < Lt)], 1 ≤ Lt →
        ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
          (a : ℝ) (ha : 0 < a),
          (Nt : ℝ) * a = Lt → (Ns : ℝ) * a = Ls →
          ∀ (f : CylinderTestFunction Ls)
            (x : AsymLatticeSites Nt Ns),
            |asymRawSource a
                (asymLatticeTestFnIso Lt Ls Nt Ns a
                  (cylinderToTorusEmbed Lt Ls f)) x| ≤
              A * q f /
                (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2 := by
  obtain ⟨D, hD, S, hDb⟩ := centeredSchwartzSeminorm_basis_poly_bound
  obtain ⟨Cs, hCs, hCsp⟩ := cylinderSpatialBasis_pointwise_bound (Ls := Ls)
  let K : ℝ := 4 + 72 * (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2)
  let A : ℝ := K * D * Cs
  let q : Seminorm ℝ (CylinderTestFunction Ls) :=
    RapidDecaySeq.rapidDecaySeminorm S
  refine ⟨A, q, ?_, ?_, ?_⟩
  · dsimp [A, K]
    positivity
  · exact RapidDecaySeq.rapidDecay_withSeminorms.continuous_seminorm S
  · intro Lt hLt hLt1 Nt Ns _ _ a ha hLtphys hLsphys f x
    let T : CylinderTestFunction Ls →L[ℝ] ℝ :=
      (a⁻¹ : ℝ) •
        (evalAsymTorusAtSite Lt Ls Nt Ns x).comp
          (cylinderToTorusEmbed Lt Ls)
    have hTf : T f =
        asymRawSource a
          (asymLatticeTestFnIso Lt Ls Nt Ns a
            (cylinderToTorusEmbed Lt Ls f)) x := by
      change a⁻¹ * evalAsymTorusAtSite Lt Ls Nt Ns x
          (cylinderToTorusEmbed Lt Ls f) =
        asymRawSource a
          (asymLatticeTestFnIso Lt Ls Nt Ns a
            (cylinderToTorusEmbed Lt Ls f)) x
      exact (asymRawSource_asymLatticeTestFnIso_apply
        Lt Ls Nt Ns a ha (cylinderToTorusEmbed Lt Ls f) x).symm
    rw [← hTf, DyninMityaginSpace.expansion T f]
    have hf_sum : Summable (fun m : ℕ =>
        |f.val m| * (1 + (m : ℝ)) ^ S) := by
      simpa [q, RapidDecaySeq.rapidDecaySeminorm] using f.rapid_decay S
    have hmajor : Summable (fun m : ℕ =>
        (K * D * Cs /
          (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2) *
          (|f.val m| * (1 + (m : ℝ)) ^ S)) := by
      exact hf_sum.mul_left _
    have hterm : ∀ m : ℕ, ‖f.val m * T (RapidDecaySeq.basisVec m)‖ ≤
        (K * D * Cs /
          (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2) *
          (|f.val m| * (1 + (m : ℝ)) ^ S) := by
      intro m
      rw [Real.norm_eq_abs, abs_mul]
      have hb := cylinderEmbeddedBasis_raw_bound Lt Ls hLt1 Nt Ns a ha
        hLtphys hLsphys D hD S hDb Cs hCs hCsp m x
      have hTbasis : T (RapidDecaySeq.basisVec m) =
          asymRawSource a
            (asymLatticeTestFnIso Lt Ls Nt Ns a
              (cylinderToTorusEmbed Lt Ls
                (RapidDecaySeq.basisVec m))) x := by
        change a⁻¹ * evalAsymTorusAtSite Lt Ls Nt Ns x
            (cylinderToTorusEmbed Lt Ls (RapidDecaySeq.basisVec m)) =
          asymRawSource a
            (asymLatticeTestFnIso Lt Ls Nt Ns a
              (cylinderToTorusEmbed Lt Ls (RapidDecaySeq.basisVec m))) x
        exact (asymRawSource_asymLatticeTestFnIso_apply
          Lt Ls Nt Ns a ha
            (cylinderToTorusEmbed Lt Ls (RapidDecaySeq.basisVec m)) x).symm
      rw [hTbasis]
      calc
        |f.val m| *
            |asymRawSource a
              (asymLatticeTestFnIso Lt Ls Nt Ns a
                (cylinderToTorusEmbed Lt Ls
                  (RapidDecaySeq.basisVec m))) x| ≤
          |f.val m| *
            (K * D * Cs * (1 + (m : ℝ)) ^ S /
              (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2) := by
            exact mul_le_mul_of_nonneg_left hb (abs_nonneg _)
        _ = (K * D * Cs /
            (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2) *
            (|f.val m| * (1 + (m : ℝ)) ^ S) := by ring
    have hsum : Summable (fun m : ℕ =>
        f.val m * T (RapidDecaySeq.basisVec m)) :=
      hmajor.of_norm_bounded hterm
    calc
      |∑' m, f.val m * T (RapidDecaySeq.basisVec m)| =
          ‖∑' m, f.val m * T (RapidDecaySeq.basisVec m)‖ :=
        (Real.norm_eq_abs _).symm
      _ ≤ ∑' m, ‖f.val m * T (RapidDecaySeq.basisVec m)‖ :=
        norm_tsum_le_tsum_norm hsum.norm
      _ ≤ ∑' m, (K * D * Cs /
          (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2) *
          (|f.val m| * (1 + (m : ℝ)) ^ S) :=
        Summable.tsum_le_tsum hterm hsum.norm hmajor
      _ = A * q f /
          (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2 := by
        change (∑' m : ℕ,
            (K * D * Cs /
              (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2) *
            (|f.val m| * (1 + (m : ℝ)) ^ S)) =
          (K * D * Cs) *
            (∑' m : ℕ, |f.val m| * (1 + (m : ℝ)) ^ S) /
              (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2
        rw [tsum_mul_left]
        ring

end Pphi2
