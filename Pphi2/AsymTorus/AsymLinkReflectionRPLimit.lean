/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Codex
-/

import Pphi2.AsymTorus.AsymLinkReflectionRP
import Pphi2.AsymTorus.AsymEnergyFactorization
import Pphi2.AsymTorus.AsymFreeSpectral

/-!
# Link-reflection positivity in the UV limit

Analytic estimates for passing the finite-spacing link-reflection matrix
inequality to cylinder time reflection.
-/

open Filter GaussianField MeasureTheory

namespace Pphi2

/-! ## Uniform heterogeneous Gaussian control -/

/-- The rectangular grid evaluations are bounded by a fixed continuous
rapid-decay seminorm, uniformly in the two lattice sizes. -/
theorem asymTorusSiteEval_norm_sq_le_seminorm
    (Lt Ls : ℝ) [Fact (0 < Lt)] [Fact (0 < Ls)]
    (C₀t : ℝ) (hC₀t_pos : 0 < C₀t)
    (hC₀t : ∀ m, SmoothMap_Circle.sobolevSeminorm (L := Lt) 0
      (SmoothMap_Circle.fourierBasis m) ≤ C₀t)
    (C₀s : ℝ) (hC₀s_pos : 0 < C₀s)
    (hC₀s : ∀ m, SmoothMap_Circle.sobolevSeminorm (L := Ls) 0
      (SmoothMap_Circle.fourierBasis m) ≤ C₀s)
    (f : AsymTorusTestFunction Lt Ls) (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] :
    ∑ x : AsymLatticeSites Nt Ns,
        (evalAsymTorusAtSite Lt Ls Nt Ns x f) ^ 2 ≤
      Lt * Ls * C₀t ^ 2 * C₀s ^ 2 *
        (RapidDecaySeq.rapidDecaySeminorm 0 f) ^ 2 := by
  set p₀f := RapidDecaySeq.rapidDecaySeminorm 0 f
  have hf_sum : Summable (fun m => |f.val m|) :=
    (f.rapid_decay 0).congr (fun m => by simp [pow_zero])
  have hcr_t : ∀ m (x : ZMod Nt),
      |circleRestriction Lt Nt
        (DyninMityaginSpace.basis m : SmoothMap_Circle Lt ℝ) x| ≤
        Real.sqrt (Lt / Nt) * C₀t := by
    intro m x
    rw [dm_basis_eq_fourierBasis (L := Lt), circleRestriction_apply,
      circleSpacing_eq, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    calc
      |(SmoothMap_Circle.fourierBasis (L := Lt) m : ℝ → ℝ)
          (circlePoint Lt Nt x)| =
          ‖iteratedDeriv 0
            ((SmoothMap_Circle.fourierBasis (L := Lt) m : ℝ → ℝ))
            (circlePoint Lt Nt x)‖ := by
        rw [iteratedDeriv_zero, Real.norm_eq_abs]
      _ ≤ SmoothMap_Circle.sobolevSeminorm 0
          (SmoothMap_Circle.fourierBasis m) :=
        SmoothMap_Circle.norm_iteratedDeriv_le_sobolevSeminorm' _ 0 _
      _ ≤ C₀t := hC₀t m
  have hcr_s : ∀ m (x : ZMod Ns),
      |circleRestriction Ls Ns
        (DyninMityaginSpace.basis m : SmoothMap_Circle Ls ℝ) x| ≤
        Real.sqrt (Ls / Ns) * C₀s := by
    intro m x
    rw [dm_basis_eq_fourierBasis (L := Ls), circleRestriction_apply,
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
      _ ≤ C₀s := hC₀s m
  have hbasis : ∀ (x : AsymLatticeSites Nt Ns) (m : ℕ),
      |evalAsymTorusAtSite Lt Ls Nt Ns x (RapidDecaySeq.basisVec m)| ≤
        Real.sqrt (Lt / Nt) * C₀t * (Real.sqrt (Ls / Ns) * C₀s) := by
    intro x m
    unfold evalAsymTorusAtSite
    rw [NuclearTensorProduct.basisVec_eq_pure
      (DyninMityaginSpace.HasBiorthogonalBasis.coeff_basis
        (E := SmoothMap_Circle Lt ℝ))
      (DyninMityaginSpace.HasBiorthogonalBasis.coeff_basis
        (E := SmoothMap_Circle Ls ℝ)) m]
    rw [NuclearTensorProduct.evalCLM_pure]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
    rw [abs_mul]
    exact mul_le_mul (hcr_t _ _) (hcr_s _ _) (abs_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) hC₀t_pos.le)
  set B := Real.sqrt (Lt / Nt) * C₀t * (Real.sqrt (Ls / Ns) * C₀s)
  have hB_nonneg : 0 ≤ B :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hC₀t_pos.le)
      (mul_nonneg (Real.sqrt_nonneg _) hC₀s_pos.le)
  have hpw : ∀ x : AsymLatticeSites Nt Ns,
      |evalAsymTorusAtSite Lt Ls Nt Ns x f| ≤ B * p₀f := by
    intro x
    rw [DyninMityaginSpace.expansion (evalAsymTorusAtSite Lt Ls Nt Ns x) f]
    have hsf : Summable (fun m =>
        f.val m * evalAsymTorusAtSite Lt Ls Nt Ns x
          (RapidDecaySeq.basisVec m)) :=
      (hf_sum.mul_right B).of_norm_bounded
        (fun m => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_left (hbasis x m) (abs_nonneg _))
    calc
      |∑' m, f.val m * evalAsymTorusAtSite Lt Ls Nt Ns x
          (RapidDecaySeq.basisVec m)| =
          ‖∑' m, f.val m * evalAsymTorusAtSite Lt Ls Nt Ns x
            (RapidDecaySeq.basisVec m)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∑' m, ‖f.val m * evalAsymTorusAtSite Lt Ls Nt Ns x
          (RapidDecaySeq.basisVec m)‖ := norm_tsum_le_tsum_norm hsf.norm
      _ ≤ ∑' m, |f.val m| * B := by
        apply Summable.tsum_le_tsum _ hsf.norm (hf_sum.mul_right _)
        intro m
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (hbasis x m) (abs_nonneg _)
      _ = B * ∑' m, |f.val m| := by rw [tsum_mul_right]; ring
      _ = B * p₀f := by
        congr 1
        change ∑' m, |f.val m| = ∑' m, |f.val m| * (1 + (m : ℝ)) ^ 0
        simp
  have hLtNt : 0 ≤ Lt / (Nt : ℝ) :=
    (div_pos (Fact.out : 0 < Lt) (Nat.cast_pos.mpr (NeZero.pos Nt))).le
  have hLsNs : 0 ≤ Ls / (Ns : ℝ) :=
    (div_pos (Fact.out : 0 < Ls) (Nat.cast_pos.mpr (NeZero.pos Ns))).le
  calc
    ∑ x : AsymLatticeSites Nt Ns,
        (evalAsymTorusAtSite Lt Ls Nt Ns x f) ^ 2 ≤
        ∑ _x : AsymLatticeSites Nt Ns, (B * p₀f) ^ 2 := by
      apply Finset.sum_le_sum
      intro x _
      have hneg := neg_abs_le (evalAsymTorusAtSite Lt Ls Nt Ns x f)
      exact sq_le_sq' (by linarith [hpw x, hneg])
        (le_of_abs_le (hpw x))
    _ = ((Nt : ℝ) * (Ns : ℝ)) * (B * p₀f) ^ 2 := by
      simp [AsymLatticeSites, ZMod.card, nsmul_eq_mul]
    _ = Lt * Ls * C₀t ^ 2 * C₀s ^ 2 * p₀f ^ 2 := by
      have hNt_ne : (Nt : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne Nt)
      have hNs_ne : (Ns : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne Ns)
      change (Nt : ℝ) * (Ns : ℝ) *
          ((Real.sqrt (Lt / Nt) * C₀t *
            (Real.sqrt (Ls / Ns) * C₀s)) * p₀f) ^ 2 = _
      rw [show ((Real.sqrt (Lt / Nt) * C₀t *
          (Real.sqrt (Ls / Ns) * C₀s)) * p₀f) ^ 2 =
        (Lt / Nt) * C₀t ^ 2 * (Ls / Ns) * C₀s ^ 2 * p₀f ^ 2 by
          rw [mul_pow, mul_pow, mul_pow, mul_pow,
            Real.sq_sqrt hLtNt, Real.sq_sqrt hLsNs]
          ring]
      field_simp [hNt_ne, hNs_ne]

/-- Uniform heterogeneous Gaussian second-moment estimate in a fixed
rapid-decay seminorm. The constant is independent of `Nt`, `Ns`, `a`, and
the test function. -/
theorem asymGaussianIso_second_moment_le_seminorm
    (Lt Ls : ℝ) [Fact (0 < Lt)] [Fact (0 < Ls)]
    (mass : ℝ) (hmass : 0 < mass) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (ha : 0 < a)
        (f : AsymTorusTestFunction Lt Ls),
        ∫ ω : Configuration (AsymLatticeField Nt Ns),
            (ω (asymLatticeTestFnIso Lt Ls Nt Ns a f)) ^ 2
            ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) ≤
          C * (RapidDecaySeq.rapidDecaySeminorm 0 f) ^ 2 := by
  obtain ⟨C₀t, hC₀t_pos, hC₀t_bound⟩ :=
    SmoothMap_Circle.sobolevSeminorm_fourierBasis_le (L := Lt) 0
  have hC₀t : ∀ m, SmoothMap_Circle.sobolevSeminorm (L := Lt) 0
      (SmoothMap_Circle.fourierBasis m) ≤ C₀t := fun m => by
    specialize hC₀t_bound m
    simpa only [pow_zero, mul_one] using hC₀t_bound
  obtain ⟨C₀s, hC₀s_pos, hC₀s_bound⟩ :=
    SmoothMap_Circle.sobolevSeminorm_fourierBasis_le (L := Ls) 0
  have hC₀s : ∀ m, SmoothMap_Circle.sobolevSeminorm (L := Ls) 0
      (SmoothMap_Circle.fourierBasis m) ≤ C₀s := fun m => by
    specialize hC₀s_bound m
    simpa only [pow_zero, mul_one] using hC₀s_bound
  let C := mass⁻¹ ^ 2 * Lt * Ls * C₀t ^ 2 * C₀s ^ 2
  have hC_pos : 0 < C := by
    dsimp [C]
    exact mul_pos
      (mul_pos
        (mul_pos
          (mul_pos (sq_pos_of_pos (inv_pos.mpr hmass)) (Fact.out : 0 < Lt))
          (Fact.out : 0 < Ls))
        (sq_pos_of_pos hC₀t_pos))
      (sq_pos_of_pos hC₀s_pos)
  refine ⟨C, hC_pos, ?_⟩
  intro Nt Ns _ _ a ha f
  let G : AsymLatticeField Nt Ns :=
    fun x => evalAsymTorusAtSite Lt Ls Nt Ns x f
  have hmoment :
      ∫ ω : Configuration (AsymLatticeField Nt Ns),
          (ω (asymLatticeTestFnIso Lt Ls Nt Ns a f)) ^ 2
          ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) =
        covariance (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass) G G := by
    calc
      ∫ ω : Configuration (AsymLatticeField Nt Ns),
          (ω (asymLatticeTestFnIso Lt Ls Nt Ns a f)) ^ 2
          ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) =
        covariance (latticeCovarianceAsymGJ Nt Ns a mass ha hmass)
          (asymLatticeTestFnIso Lt Ls Nt Ns a f)
          (asymLatticeTestFnIso Lt Ls Nt Ns a f) :=
        second_moment_eq_covariance _ _
      _ = covariance (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass) G G := by
        exact second_moment_asym_eq_spectral Lt Ls Nt Ns a mass ha hmass f f
  rw [hmoment, covariance_spectralLatticeCovarianceAsym_eq]
  simp_rw [show ∀ k : AsymLatticeSites Nt Ns,
      ((massEigenvaluesAsym Nt Ns a mass k)⁻¹ *
          ∑ x, (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * G x) *
        ∑ x, (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * G x =
      (massEigenvaluesAsym Nt Ns a mass k)⁻¹ *
        (∑ x, (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * G x) ^ 2
      by intro k; ring]
  change (∑ k : AsymLatticeSites Nt Ns,
      (massEigenvaluesAsym Nt Ns a mass k)⁻¹ *
        (asymModeCoeff Nt Ns a mass k G) ^ 2) ≤
    C * (RapidDecaySeq.rapidDecaySeminorm 0 f) ^ 2
  have heigen_ge : ∀ k : AsymLatticeSites Nt Ns,
      mass ^ 2 ≤ massEigenvaluesAsym Nt Ns a mass k := by
    intro k
    let e : AsymLatticeField Nt Ns :=
      massEigenvectorBasisAsym Nt Ns a mass k
    have he_norm : ∑ x : AsymLatticeSites Nt Ns, e x ^ 2 = 1 := by
      have hnorm := (massEigenvectorBasisAsym Nt Ns a mass).orthonormal.1 k
      simp only [EuclideanSpace.norm_eq] at hnorm
      have hsqrt : Real.sqrt (∑ x : AsymLatticeSites Nt Ns, ‖e x‖ ^ 2) = 1 := by
        simpa [e] using hnorm
      have hsum_nonneg : 0 ≤ ∑ x : AsymLatticeSites Nt Ns, ‖e x‖ ^ 2 :=
        Finset.sum_nonneg fun x _ => sq_nonneg ‖e x‖
      have hsquares : ∑ x : AsymLatticeSites Nt Ns, e x ^ 2 =
          ∑ x : AsymLatticeSites Nt Ns, ‖e x‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Real.norm_eq_abs, sq_abs]
      rw [hsquares]
      nlinarith [Real.sq_sqrt hsum_nonneg]
    have hQe : massOperatorAsym Nt Ns a mass e =
        massEigenvaluesAsym Nt Ns a mass k • e := by
      ext x
      rw [massOperatorAsym_eq_matrix_mulVec Nt Ns a mass e x]
      simpa [massEigenvaluesAsym, massEigenvectorBasisAsym, e] using
        congrFun (Matrix.IsHermitian.mulVec_eigenvectorBasis
          (hA := massOperatorMatrixAsym_isHermitian Nt Ns a mass) k) x
    have hquad := massOperatorAsym_quadratic_form_bonds
      (Nt := Nt) (Ns := Ns) a mass e
    rw [hQe] at hquad
    have htime_nonneg : 0 ≤ a⁻¹ ^ 2 *
        ∑ x : AsymLatticeSites Nt Ns,
          (e (x + ((1 : ZMod Nt), (0 : ZMod Ns))) - e x) ^ 2 :=
      mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun x _ => sq_nonneg _)
    have hspace_nonneg : 0 ≤ a⁻¹ ^ 2 *
        ∑ x : AsymLatticeSites Nt Ns,
          (e (x + ((0 : ZMod Nt), (1 : ZMod Ns))) - e x) ^ 2 :=
      mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun x _ => sq_nonneg _)
    simp only [Pi.smul_apply, smul_eq_mul] at hquad
    have hleft : ∑ x : AsymLatticeSites Nt Ns,
        e x * (massEigenvaluesAsym Nt Ns a mass k * e x) =
        massEigenvaluesAsym Nt Ns a mass k := by
      calc
        ∑ x : AsymLatticeSites Nt Ns,
            e x * (massEigenvaluesAsym Nt Ns a mass k * e x) =
            massEigenvaluesAsym Nt Ns a mass k * ∑ x, e x ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          ring
        _ = massEigenvaluesAsym Nt Ns a mass k := by rw [he_norm, mul_one]
    rw [hleft, he_norm, mul_one] at hquad
    linarith
  have hinv_le : ∀ k : AsymLatticeSites Nt Ns,
      (massEigenvaluesAsym Nt Ns a mass k)⁻¹ ≤ mass⁻¹ ^ 2 := by
    intro k
    rw [inv_pow, ← one_div, ← one_div]
    exact div_le_div_of_nonneg_left zero_le_one (sq_pos_of_pos hmass) (heigen_ge k)
  calc
    ∑ k : AsymLatticeSites Nt Ns,
        (massEigenvaluesAsym Nt Ns a mass k)⁻¹ *
          (asymModeCoeff Nt Ns a mass k G) ^ 2 ≤
        ∑ k : AsymLatticeSites Nt Ns,
          mass⁻¹ ^ 2 * (asymModeCoeff Nt Ns a mass k G) ^ 2 := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_right (hinv_le k) (sq_nonneg _)
    _ = mass⁻¹ ^ 2 * ∑ k : AsymLatticeSites Nt Ns,
        (asymModeCoeff Nt Ns a mass k G) ^ 2 := by rw [Finset.mul_sum]
    _ = mass⁻¹ ^ 2 * ∑ x : AsymLatticeSites Nt Ns, (G x) ^ 2 := by
      rw [sum_asymModeCoeff_sq]
    _ ≤ mass⁻¹ ^ 2 *
        (Lt * Ls * C₀t ^ 2 * C₀s ^ 2 *
          (RapidDecaySeq.rapidDecaySeminorm 0 f) ^ 2) := by
      apply mul_le_mul_of_nonneg_left
      · exact asymTorusSiteEval_norm_sq_le_seminorm Lt Ls
          C₀t hC₀t_pos hC₀t C₀s hC₀s_pos hC₀s f Nt Ns
      · exact sq_nonneg _
    _ = C * (RapidDecaySeq.rapidDecaySeminorm 0 f) ^ 2 := by
      dsimp [C]
      ring

/-- The heterogeneous lattice Gaussian second moments vanish along every
cylinder test-function sequence tending to zero. This is the diagonal
covariance control required by the moving-reflection RP limit. -/
theorem asymCylinderLatticeSecondMoment_tendsto_zero_of_tendsto
    (Lt Ls : ℝ) [Fact (0 < Lt)] [Fact (0 < Ls)]
    (mass : ℝ) (hmass : 0 < mass)
    (Nt Ns : ℕ → ℕ) (a : ℕ → ℝ)
    (hNt : ∀ k, NeZero (Nt k)) (hNs : ∀ k, NeZero (Ns k))
    (ha : ∀ k, 0 < a k)
    (hseq : ℕ → CylinderTestFunction Ls)
    (hseq0 : Tendsto hseq atTop (nhds 0)) :
    Tendsto (fun k =>
      haveI := hNt k
      haveI := hNs k
      ∫ ω : Configuration (AsymLatticeField (Nt k) (Ns k)),
        (ω (asymLatticeTestFnIso Lt Ls (Nt k) (Ns k) (a k)
          (cylinderToTorusEmbed Lt Ls (hseq k)))) ^ 2
        ∂(latticeGaussianMeasureAsym (Nt k) (Ns k) (a k) mass (ha k) hmass))
      atTop (nhds 0) := by
  obtain ⟨C, hC_pos, hbound⟩ :=
    asymGaussianIso_second_moment_le_seminorm Lt Ls mass hmass
  have hembed : Tendsto
      (fun k => cylinderToTorusEmbed Lt Ls (hseq k))
      atTop (nhds 0) := by
    have h := (cylinderToTorusEmbed Lt Ls).cont.continuousAt.tendsto.comp hseq0
    simpa using h
  have hp0 : Tendsto
      (fun k => RapidDecaySeq.rapidDecaySeminorm 0
        (cylinderToTorusEmbed Lt Ls (hseq k)))
      atTop (nhds 0) := by
    have h :=
      (RapidDecaySeq.rapidDecay_withSeminorms.continuous_seminorm 0).continuousAt.tendsto.comp
        hembed
    convert h using 1
    exact congrArg nhds (map_zero (RapidDecaySeq.rapidDecaySeminorm 0)).symm
  have hupper : Tendsto
      (fun k => C * (RapidDecaySeq.rapidDecaySeminorm 0
        (cylinderToTorusEmbed Lt Ls (hseq k))) ^ 2)
      atTop (nhds 0) := by
    simpa using (hp0.pow 2).const_mul C
  refine squeeze_zero (fun k => ?_) (fun k => ?_) hupper
  · haveI := hNt k
    haveI := hNs k
    exact integral_nonneg fun _ => sq_nonneg _
  · haveI := hNt k
    haveI := hNs k
    exact hbound (Nt k) (Ns k) (a k) (ha k)
      (cylinderToTorusEmbed Lt Ls (hseq k))

/-- The heterogeneous lattice Gaussian second moment is quadratic under real
scaling of the cylinder test function. -/
theorem asymCylinderLatticeSecondMoment_smul
    (Lt Ls : ℝ) [Fact (0 < Lt)] [Fact (0 < Ls)]
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (t : ℝ) (h : CylinderTestFunction Ls) :
    ∫ ω : Configuration (AsymLatticeField Nt Ns),
        (ω (asymLatticeTestFnIso Lt Ls Nt Ns a
          (cylinderToTorusEmbed Lt Ls (t • h)))) ^ 2
        ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) =
      t ^ 2 * ∫ ω : Configuration (AsymLatticeField Nt Ns),
        (ω (asymLatticeTestFnIso Lt Ls Nt Ns a
          (cylinderToTorusEmbed Lt Ls h))) ^ 2
        ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) := by
  have hpoint : (fun ω : Configuration (AsymLatticeField Nt Ns) =>
      (ω (asymLatticeTestFnIso Lt Ls Nt Ns a
        (cylinderToTorusEmbed Lt Ls (t • h)))) ^ 2) =
      fun ω => t ^ 2 *
        (ω (asymLatticeTestFnIso Lt Ls Nt Ns a
          (cylinderToTorusEmbed Lt Ls h))) ^ 2 := by
    have htest : asymLatticeTestFnIso Lt Ls Nt Ns a
        (cylinderToTorusEmbed Lt Ls (t • h)) =
        t • asymLatticeTestFnIso Lt Ls Nt Ns a
          (cylinderToTorusEmbed Lt Ls h) := by
      funext x
      simp [asymLatticeTestFnIso, map_smul, Pi.smul_apply, smul_eq_mul]
    funext ω
    rw [htest, map_smul]
    simp only [smul_eq_mul]
    ring
  rw [hpoint, integral_const_mul]

/-- A scaled exponential-moment bound controls the absolute first moment by
the square root of its variance parameter.

The rescaling is essential: applying the exponential bound only at `t = 1`
would leave a nonzero constant when `sigmaSq` tends to zero. -/
theorem absMoment_le_of_uniform_expMoment
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (μ : Measure (Configuration E)) (h : E) (K C sigmaSq : ℝ)
    (hK : 0 < K) (hC : 0 < C) (hsigmaSq : 0 ≤ sigmaSq)
    (hExp : ∀ t : ℝ,
      Integrable (fun ω : Configuration E => Real.exp |ω (t • h)|) μ ∧
      ∫ ω : Configuration E, Real.exp |ω (t • h)| ∂μ ≤
        K * Real.exp (C * t ^ 2 * sigmaSq)) :
    Integrable (fun ω : Configuration E => |ω h|) μ ∧
    ∫ ω : Configuration E, |ω h| ∂μ ≤
      K * Real.exp 1 * Real.sqrt C * Real.sqrt sigmaSq := by
  have habs_meas : AEStronglyMeasurable
      (fun ω : Configuration E => |ω h|) μ :=
    (configuration_eval_measurable h).abs.aestronglyMeasurable
  have habs_int : Integrable (fun ω : Configuration E => |ω h|) μ := by
    refine (hExp 1).1.mono' habs_meas (ae_of_all _ fun ω => ?_)
    simpa [Real.norm_eq_abs, abs_of_nonneg] using
      ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp |ω h|))
  refine ⟨habs_int, ?_⟩
  have hscaled_abs_int : ∀ t : ℝ,
      Integrable (fun ω : Configuration E => |ω (t • h)|) μ := by
    intro t
    have hmeas : AEStronglyMeasurable
        (fun ω : Configuration E => |ω (t • h)|) μ :=
      (configuration_eval_measurable (t • h)).abs.aestronglyMeasurable
    refine (hExp t).1.mono' hmeas (ae_of_all _ fun ω => ?_)
    simpa [Real.norm_eq_abs, abs_of_nonneg] using
      ((le_add_of_nonneg_right zero_le_one).trans
        (Real.add_one_le_exp |ω (t • h)|))
  have hscaled_abs : ∀ t : ℝ,
      ∫ ω : Configuration E, |ω (t • h)| ∂μ =
        |t| * ∫ ω : Configuration E, |ω h| ∂μ := by
    intro t
    simp_rw [map_smul, smul_eq_mul, abs_mul]
    exact integral_const_mul |t| (fun ω : Configuration E => |ω h|)
  have hscaled_bound : ∀ t : ℝ,
      ∫ ω : Configuration E, |ω (t • h)| ∂μ ≤
        K * Real.exp (C * t ^ 2 * sigmaSq) := by
    intro t
    exact (integral_mono (hscaled_abs_int t) (hExp t).1
      (fun ω => (le_add_of_nonneg_right zero_le_one).trans
        (Real.add_one_le_exp _))).trans (hExp t).2
  rcases eq_or_lt_of_le hsigmaSq with hsigmaSq_zero | hsigmaSq_pos
  · subst sigmaSq
    have hmoment_nonneg : 0 ≤ ∫ ω : Configuration E, |ω h| ∂μ :=
      integral_nonneg fun _ => abs_nonneg _
    have hmoment_zero : ∫ ω : Configuration E, |ω h| ∂μ = 0 := by
      apply le_antisymm
      · by_contra hnot
        have hmoment_pos : 0 < ∫ ω : Configuration E, |ω h| ∂μ :=
          lt_of_not_ge hnot
        let t : ℝ := K / (∫ ω : Configuration E, |ω h| ∂μ) + 1
        have ht_pos : 0 < t := by
          dsimp [t]
          positivity
        have hle : t * (∫ ω : Configuration E, |ω h| ∂μ) ≤ K := by
          calc
            t * (∫ ω : Configuration E, |ω h| ∂μ) =
                ∫ ω : Configuration E, |ω (t • h)| ∂μ := by
              rw [hscaled_abs t, abs_of_pos ht_pos]
            _ ≤ K * Real.exp (C * t ^ 2 * 0) := hscaled_bound t
            _ = K := by simp
        have hlt : K < t * (∫ ω : Configuration E, |ω h| ∂μ) := by
          dsimp [t]
          field_simp [ne_of_gt hmoment_pos]
          linarith
        exact (not_lt_of_ge hle) hlt
      · exact hmoment_nonneg
    simp [hmoment_zero]
  · have hCsigmaSq_pos : 0 < C * sigmaSq := mul_pos hC hsigmaSq_pos
    have hsqrt_CsigmaSq_pos : 0 < Real.sqrt (C * sigmaSq) :=
      Real.sqrt_pos.2 hCsigmaSq_pos
    let t : ℝ := (Real.sqrt (C * sigmaSq))⁻¹
    have ht_pos : 0 < t := inv_pos.mpr hsqrt_CsigmaSq_pos
    have ht_sq_mul : t ^ 2 * (C * sigmaSq) = 1 := by
      dsimp [t]
      rw [inv_pow, Real.sq_sqrt hCsigmaSq_pos.le]
      exact inv_mul_cancel₀ (ne_of_gt hCsigmaSq_pos)
    have hdiv_bound :
        (∫ ω : Configuration E, |ω h| ∂μ) / Real.sqrt (C * sigmaSq) ≤
          K * Real.exp 1 := by
      calc
        (∫ ω : Configuration E, |ω h| ∂μ) / Real.sqrt (C * sigmaSq) =
            ∫ ω : Configuration E, |ω (t • h)| ∂μ := by
          rw [hscaled_abs t, abs_of_pos ht_pos]
          simp [t, div_eq_mul_inv, mul_comm]
        _ ≤ K * Real.exp (C * t ^ 2 * sigmaSq) := hscaled_bound t
        _ = K * Real.exp 1 := by
          congr 2
          calc
            C * t ^ 2 * sigmaSq = t ^ 2 * (C * sigmaSq) := by ring
            _ = 1 := ht_sq_mul
    have hbound := (div_le_iff₀ hsqrt_CsigmaSq_pos).mp hdiv_bound
    calc
      ∫ ω : Configuration E, |ω h| ∂μ ≤
          K * Real.exp 1 * Real.sqrt (C * sigmaSq) := hbound
      _ = K * Real.exp 1 * Real.sqrt C * Real.sqrt sigmaSq := by
        rw [Real.sqrt_mul hC.le]
        ring

/-- Bounded-continuous convergence on torus configurations gives
characteristic-functional convergence after cylinder pullback. -/
theorem cylinderPullbackMeasure_cexp_tendsto_of_tendsto_bc
    (Lt Ls : ℝ) [Fact (0 < Lt)] [Fact (0 < Ls)]
    (μseq : ℕ → Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    (hμseq_prob : ∀ k, IsProbabilityMeasure (μseq k))
    (hμ_prob : IsProbabilityMeasure μ)
    (hbc : ∀ (g : Configuration (AsymTorusTestFunction Lt Ls) → ℝ),
      Continuous g → (∃ B, ∀ x, |g x| ≤ B) →
      Tendsto (fun k => ∫ ω, g ω ∂(μseq k)) atTop (nhds (∫ ω, g ω ∂μ)))
    (f : CylinderTestFunction Ls) :
    Tendsto
      (fun k => ∫ ω, Complex.exp (Complex.I * ↑(ω f))
        ∂(cylinderPullbackMeasure Lt Ls (μseq k)))
      atTop
      (nhds (∫ ω, Complex.exp (Complex.I * ↑(ω f))
        ∂(cylinderPullbackMeasure Lt Ls μ))) := by
  let F : AsymTorusTestFunction Lt Ls := cylinderToTorusEmbed Lt Ls f
  have hcos : Tendsto
      (fun k => ∫ ω, Real.cos (ω F) ∂(μseq k))
      atTop (nhds (∫ ω, Real.cos (ω F) ∂μ)) :=
    hbc (fun ω => Real.cos (ω F))
      (Real.continuous_cos.comp (WeakDual.eval_continuous F))
      ⟨1, fun ω => Real.abs_cos_le_one (ω F)⟩
  have hsin : Tendsto
      (fun k => ∫ ω, Real.sin (ω F) ∂(μseq k))
      atTop (nhds (∫ ω, Real.sin (ω F) ∂μ)) :=
    hbc (fun ω => Real.sin (ω F))
      (Real.continuous_sin.comp (WeakDual.eval_continuous F))
      ⟨1, fun ω => Real.abs_sin_le_one (ω F)⟩
  have hre : Tendsto
      (fun k => (∫ ω, Complex.exp (Complex.I * ↑(ω F)) ∂(μseq k)).re)
      atTop (nhds ((∫ ω, Complex.exp (Complex.I * ↑(ω F)) ∂μ).re)) := by
    have hseq :
        (fun k => (∫ ω, Complex.exp (Complex.I * ↑(ω F)) ∂(μseq k)).re) =
          fun k => ∫ ω, Real.cos (ω F) ∂(μseq k) := by
      funext k
      letI := hμseq_prob k
      exact configuration_expIntegral_re_eq_integral_cos (μseq k) F
    have hlim : (∫ ω, Complex.exp (Complex.I * ↑(ω F)) ∂μ).re =
        ∫ ω, Real.cos (ω F) ∂μ := by
      letI := hμ_prob
      exact configuration_expIntegral_re_eq_integral_cos μ F
    rw [hseq, hlim]
    exact hcos
  have him : Tendsto
      (fun k => (∫ ω, Complex.exp (Complex.I * ↑(ω F)) ∂(μseq k)).im)
      atTop (nhds ((∫ ω, Complex.exp (Complex.I * ↑(ω F)) ∂μ).im)) := by
    have hseq :
        (fun k => (∫ ω, Complex.exp (Complex.I * ↑(ω F)) ∂(μseq k)).im) =
          fun k => ∫ ω, Real.sin (ω F) ∂(μseq k) := by
      funext k
      letI := hμseq_prob k
      exact configuration_expIntegral_im_eq_integral_sin (μseq k) F
    have hlim : (∫ ω, Complex.exp (Complex.I * ↑(ω F)) ∂μ).im =
        ∫ ω, Real.sin (ω F) ∂μ := by
      letI := hμ_prob
      exact configuration_expIntegral_im_eq_integral_sin μ F
    rw [hseq, hlim]
    exact hsin
  have htorus : Tendsto
      (fun k => ∫ ω, Complex.exp (Complex.I * ↑(ω F)) ∂(μseq k))
      atTop (nhds (∫ ω, Complex.exp (Complex.I * ↑(ω F)) ∂μ)) := by
    have hpair := hre.prodMk_nhds him
    have hcomplex := (Complex.equivRealProdCLM.symm.continuous.tendsto
      (((∫ ω, Complex.exp (Complex.I * ↑(ω F)) ∂μ).re),
       ((∫ ω, Complex.exp (Complex.I * ↑(ω F)) ∂μ).im))).comp hpair
    simpa [Complex.equivRealProdCLM_symm_apply, Complex.re_add_im] using hcomplex
  have hmap : ∀ ν : Measure (Configuration (AsymTorusTestFunction Lt Ls)),
      ∫ ω, Complex.exp (Complex.I * ↑(ω f))
          ∂(cylinderPullbackMeasure Lt Ls ν) =
        ∫ ω, Complex.exp (Complex.I * ↑(ω F)) ∂ν := by
    intro ν
    unfold cylinderPullbackMeasure
    have hmeas : Measurable (cylinderPullback Lt Ls) :=
      configuration_measurable_of_eval_measurable _
        (fun φ => configuration_eval_measurable _)
    have hsm : StronglyMeasurable
        (fun ω : Configuration (CylinderTestFunction Ls) =>
          Complex.exp (Complex.I * ↑(ω f))) :=
      (Complex.measurable_exp.comp (measurable_const.mul
        (Complex.measurable_ofReal.comp
          (configuration_eval_measurable f)))).stronglyMeasurable
    rw [integral_map_of_stronglyMeasurable
      hmeas hsm]
    simp [F, cylinderPullback_eval]
  simpa only [hmap] using htorus

/-- The characteristic integrand is pointwise Lipschitz in its real source. -/
theorem configuration_cexp_eval_dist_le_abs_eval_sub
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (f g : E) (ω : Configuration E) :
    configuration_cexp_eval_dist f g ω ≤ |ω (g - f)| := by
  change ‖Complex.exp (Complex.I * ↑(ω g)) -
    Complex.exp (Complex.I * ↑(ω f))‖ ≤ |ω (g - f)|
  have hfactor :
      Complex.exp (Complex.I * ↑(ω g)) - Complex.exp (Complex.I * ↑(ω f)) =
        Complex.exp (Complex.I * ↑(ω f)) *
          (Complex.exp (Complex.I * ↑(ω g - ω f)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
  rw [hfactor, norm_mul, mul_comm Complex.I (↑(ω f) : ℂ),
    Complex.norm_exp_ofReal_mul_I, one_mul,
    Complex.norm_exp_I_mul_ofReal_sub_one]
  calc
    ‖2 * Real.sin ((ω g - ω f) / 2)‖ =
        2 * |Real.sin ((ω g - ω f) / 2)| := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ 2 * |(ω g - ω f) / 2| :=
      mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by norm_num)
    _ = |ω g - ω f| := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      ring
    _ = |ω (g - f)| := by rw [map_sub]

/-- A seminorm-controlled exponential moment makes the characteristic
functional Lipschitz in that seminorm. -/
theorem norm_configuration_expIntegral_sub_le_seminorm
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (μ : Measure (Configuration E)) [IsProbabilityMeasure μ]
    (K C : ℝ) (hK : 0 < K) (hC : 0 < C) (q : Seminorm ℝ E)
    (hExp : ∀ h : E,
      Integrable (fun ω : Configuration E => Real.exp |ω h|) μ ∧
      ∫ ω : Configuration E, Real.exp |ω h| ∂μ ≤
        K * Real.exp (C * q h ^ 2))
    (f g : E) :
    ‖(∫ ω, Complex.exp (Complex.I * ↑(ω g)) ∂μ) -
        ∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂μ‖ ≤
      K * Real.exp 1 * Real.sqrt C * q (g - f) := by
  let h := g - f
  have hExp_scaled : ∀ t : ℝ,
      Integrable (fun ω : Configuration E => Real.exp |ω (t • h)|) μ ∧
      ∫ ω : Configuration E, Real.exp |ω (t • h)| ∂μ ≤
        K * Real.exp (C * t ^ 2 * q h ^ 2) := by
    intro t
    obtain ⟨hint, hle⟩ := hExp (t • h)
    refine ⟨hint, ?_⟩
    rw [SeminormClass.map_smul_eq_mul] at hle
    have hsq : (|t| * q h) ^ 2 = t ^ 2 * q h ^ 2 := by
      rw [mul_pow, sq_abs]
    simpa [Real.norm_eq_abs, abs_mul, hsq, mul_assoc] using hle
  obtain ⟨habs_int, habs_bound⟩ := absMoment_le_of_uniform_expMoment
    μ h K C (q h ^ 2) hK hC (sq_nonneg (q h)) hExp_scaled
  have hdist_int : Integrable (configuration_cexp_eval_dist f g) μ := by
    have hg_int := configuration_cexp_eval_integrable μ g
    have hf_int := configuration_cexp_eval_integrable μ f
    simpa [configuration_cexp_eval_dist,
      configuration_cexp_eval_sub_integrand] using (hg_int.sub hf_int).norm
  calc
    ‖(∫ ω, Complex.exp (Complex.I * ↑(ω g)) ∂μ) -
        ∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂μ‖
        ≤ ∫ ω, configuration_cexp_eval_dist f g ω ∂μ :=
      norm_configuration_expIntegral_sub_le_integral_cexp_eval_dist μ f g
    _ ≤ ∫ ω, |ω h| ∂μ := by
      apply integral_mono hdist_int habs_int
      intro ω
      exact configuration_cexp_eval_dist_le_abs_eval_sub f g ω
    _ ≤ K * Real.exp 1 * Real.sqrt C * Real.sqrt (q h ^ 2) := habs_bound
    _ = K * Real.exp 1 * Real.sqrt C * q (g - f) := by
      rw [Real.sqrt_sq (NonnegHomClass.apply_nonneg q h)]

/-- A seminorm-controlled exponential moment makes the characteristic
functional continuous in the test-function topology. -/
theorem continuous_configuration_expIntegral_of_expMoment_seminorm
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (μ : Measure (Configuration E)) [IsProbabilityMeasure μ]
    (K C : ℝ) (hK : 0 < K) (hC : 0 < C) (q : Seminorm ℝ E)
    (hq : Continuous q)
    (hExp : ∀ h : E,
      Integrable (fun ω : Configuration E => Real.exp |ω h|) μ ∧
      ∫ ω : Configuration E, Real.exp |ω h| ∂μ ≤
        K * Real.exp (C * q h ^ 2)) :
    Continuous (fun h : E =>
      ∫ ω, Complex.exp (Complex.I * ↑(ω h)) ∂μ) := by
  rw [continuous_iff_continuousAt]
  intro f
  change Tendsto (fun h : E =>
    ∫ ω, Complex.exp (Complex.I * ↑(ω h)) ∂μ) (nhds f)
      (nhds (∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂μ))
  rw [Metric.tendsto_nhds]
  intro ε hε
  let D := K * Real.exp 1 * Real.sqrt C
  have hD : 0 < D := mul_pos (mul_pos hK (Real.exp_pos 1)) (Real.sqrt_pos.2 hC)
  have hcontrol : Continuous (fun g : E => D * q (g - f)) :=
    continuous_const.mul (hq.comp (continuous_id.sub continuous_const))
  have hevent : ∀ᶠ g : E in nhds f, D * q (g - f) < ε := by
    apply hcontrol.continuousAt.eventually_lt continuousAt_const
    simpa [D] using hε
  filter_upwards [hevent] with g hg
  rw [dist_eq_norm]
  exact lt_of_le_of_lt
    (norm_configuration_expIntegral_sub_le_seminorm μ K C hK hC q hExp f g) hg

/-- Reflection positivity on the algebraic span of compact positive-time pure
tensors extends to the full positive-time cylinder submodule when the
characteristic functional obeys a continuous-seminorm exponential bound. -/
theorem cylinderMeasureReflectionPositive_of_compactSpan
    (Ls : ℝ) [Fact (0 < Ls)]
    (μ : Measure (Configuration (CylinderTestFunction Ls))) [IsProbabilityMeasure μ]
    (K C : ℝ) (hK : 0 < K) (hC : 0 < C)
    (q : Seminorm ℝ (CylinderTestFunction Ls)) (hq : Continuous q)
    (hExp : ∀ h : CylinderTestFunction Ls,
      Integrable (fun ω : Configuration (CylinderTestFunction Ls) => Real.exp |ω h|) μ ∧
      ∫ ω : Configuration (CylinderTestFunction Ls), Real.exp |ω h| ∂μ ≤
        K * Real.exp (C * q h ^ 2))
    (hRPspan : ∀ (n : ℕ)
      (f : Fin n → ↥(cylinderPositiveTimeSubmodule Ls)) (c : Fin n → ℂ),
      (∀ i, (f i : CylinderTestFunction Ls) ∈
        Submodule.span ℝ (cylinderPositiveTimeCompactPureTensors Ls)) →
      CylinderRPMatrixNonnegative Ls μ n f c) :
    CylinderMeasureReflectionPositive Ls μ := by
  have hχ : Continuous (fun h : CylinderTestFunction Ls =>
      ∫ ω, Complex.exp (Complex.I * ↑(ω h)) ∂μ) :=
    continuous_configuration_expIntegral_of_expMoment_seminorm
      μ K C hK hC q hq hExp
  let S := Submodule.span ℝ (cylinderPositiveTimeCompactPureTensors Ls)
  let P := cylinderPositiveTimeSubmodule Ls
  have hSP : (S : Set (CylinderTestFunction Ls)) ⊆ P := by
    intro u hu
    apply Submodule.span_induction (R := ℝ) (M := CylinderTestFunction Ls)
      (s := cylinderPositiveTimeCompactPureTensors Ls)
      (p := fun v _ => v ∈ P)
    · intro v hv
      rcases hv with ⟨g, h, T, _hT, hh, _hsupp, rfl⟩
      exact pure_mem_cylinderPositiveTimeSubmodule Ls g h hh
    · exact P.zero_mem
    · intro x y _ _ hx hy
      exact P.add_mem hx hy
    · intro r x _ hx
      exact P.smul_mem r hx
    · exact hu
  let e : S → P := Set.inclusion hSP
  have he : DenseRange e := by
    apply (denseRange_inclusion_iff hSP).2
    intro u hu
    have heq := cylinderPositiveTimeSubmodule_eq_closure_span_compactPure Ls
    change (u : CylinderTestFunction Ls) ∈ closure (S : Set (CylinderTestFunction Ls))
    rw [← Submodule.topologicalClosure_coe]
    rw [← heq]
    exact hu
  intro n f c
  let χ : CylinderTestFunction Ls → ℂ := fun h =>
    ∫ ω, Complex.exp (Complex.I * ↑(ω h)) ∂μ
  let Q : (Fin n → P) → ℝ := fun F =>
    (∑ i, ∑ j, c i * starRingEnd ℂ (c j) *
      χ ((F i : CylinderTestFunction Ls) -
        cylinderTimeReflection Ls (F j : CylinderTestFunction Ls))).re
  have hQ : Continuous Q := by
    apply Complex.continuous_re.comp
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    apply continuous_const.mul
    apply hχ.comp
    exact (continuous_subtype_val.comp (continuous_apply i)).sub
      ((cylinderTimeReflection Ls).cont.comp
        (continuous_subtype_val.comp (continuous_apply j)))
  have hePi : DenseRange (Pi.map fun _ : Fin n => e) :=
    DenseRange.piMap fun _ => he
  change 0 ≤ Q f
  refine DenseRange.induction_on hePi (p := fun F => 0 ≤ Q F) f ?_ ?_
  · exact isClosed_Ici.preimage hQ
  · intro g
    have hg := hRPspan n (Pi.map (fun _ : Fin n => e) g) c (fun i => (g i).property)
    simpa [CylinderRPMatrixNonnegative, Q, χ, e] using hg

/-- Characteristic-functional convergence transfers one eventually
nonnegative cylinder RP matrix to the limit. -/
theorem cylinderRPMatrixNonnegative_of_tendsto_cf
    (Ls : ℝ) [Fact (0 < Ls)]
    (νseq : ℕ → Measure (Configuration (CylinderTestFunction Ls)))
    (ν : Measure (Configuration (CylinderTestFunction Ls)))
    (hcf : ∀ h : CylinderTestFunction Ls,
      Tendsto (fun k => ∫ ω, Complex.exp (Complex.I * ↑(ω h)) ∂(νseq k))
        atTop (nhds (∫ ω, Complex.exp (Complex.I * ↑(ω h)) ∂ν)))
    (n : ℕ) (f : Fin n → ↥(cylinderPositiveTimeSubmodule Ls)) (c : Fin n → ℂ)
    (hrp : ∀ᶠ k in atTop, CylinderRPMatrixNonnegative Ls (νseq k) n f c) :
    CylinderRPMatrixNonnegative Ls ν n f c := by
  have hentry : ∀ i j : Fin n,
      Tendsto (fun k => ∫ ω, Complex.exp (Complex.I *
        ↑(ω ((f i : CylinderTestFunction Ls) -
          cylinderTimeReflection Ls (f j : CylinderTestFunction Ls)))) ∂(νseq k))
        atTop (nhds (∫ ω, Complex.exp (Complex.I *
          ↑(ω ((f i : CylinderTestFunction Ls) -
            cylinderTimeReflection Ls (f j : CylinderTestFunction Ls)))) ∂ν)) := by
    intro i j
    exact hcf ((f i : CylinderTestFunction Ls) -
      cylinderTimeReflection Ls (f j : CylinderTestFunction Ls))
  have hsum : Tendsto (fun k =>
      (∑ i, ∑ j, c i * starRingEnd ℂ (c j) *
        ∫ ω, Complex.exp (Complex.I *
          ↑(ω ((f i : CylinderTestFunction Ls) -
            cylinderTimeReflection Ls (f j : CylinderTestFunction Ls)))) ∂(νseq k)).re)
      atTop (nhds ((∑ i, ∑ j, c i * starRingEnd ℂ (c j) *
        ∫ ω, Complex.exp (Complex.I *
          ↑(ω ((f i : CylinderTestFunction Ls) -
            cylinderTimeReflection Ls (f j : CylinderTestFunction Ls)))) ∂ν).re)) := by
    apply Complex.continuous_re.continuousAt.tendsto.comp
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    exact Filter.Tendsto.const_mul (c i * starRingEnd ℂ (c j)) (hentry i j)
  unfold CylinderRPMatrixNonnegative
  exact ge_of_tendsto hsum hrp

/-- No-wrap RP at finite periods, characteristic-functional convergence, and
a continuous exponential-moment bound imply full cylinder RP at the IR
limit. The density extension is performed only after `Lt → ∞`. -/
theorem cylinderMeasureReflectionPositive_of_noWrap_limit
    (Ls : ℝ) [Fact (0 < Ls)]
    (Lt : ℕ → ℝ) (hLt_tend : Tendsto Lt atTop atTop)
    (νseq : ℕ → Measure (Configuration (CylinderTestFunction Ls)))
    (ν : Measure (Configuration (CylinderTestFunction Ls))) [IsProbabilityMeasure ν]
    (hcf : ∀ h : CylinderTestFunction Ls,
      Tendsto (fun k => ∫ ω, Complex.exp (Complex.I * ↑(ω h)) ∂(νseq k))
        atTop (nhds (∫ ω, Complex.exp (Complex.I * ↑(ω h)) ∂ν)))
    (hnoWrap : ∀ k, CylinderMeasureNoWrapReflectionPositive (Lt k) Ls (νseq k))
    (K C : ℝ) (hK : 0 < K) (hC : 0 < C)
    (q : Seminorm ℝ (CylinderTestFunction Ls)) (hq : Continuous q)
    (hExp : ∀ h : CylinderTestFunction Ls,
      Integrable (fun ω : Configuration (CylinderTestFunction Ls) => Real.exp |ω h|) ν ∧
      ∫ ω : Configuration (CylinderTestFunction Ls), Real.exp |ω h| ∂ν ≤
        K * Real.exp (C * q h ^ 2)) :
    CylinderMeasureReflectionPositive Ls ν := by
  apply cylinderMeasureReflectionPositive_of_compactSpan Ls ν K C hK hC q hq hExp
  intro n f c hf
  obtain ⟨R, hR, hfR⟩ :=
    finite_mem_span_cylinderPositiveTimeCompactPureTensors_exists_radius Ls n
      (fun i => (f i : CylinderTestFunction Ls)) hf
  have hperiod : ∀ᶠ k in atTop, 2 * R < Lt k := by
    have hlarge : ∀ᶠ k in atTop, 2 * R + 1 ≤ Lt k := tendsto_atTop.1 hLt_tend (2 * R + 1)
    exact hlarge.mono fun k hk => by linarith
  apply cylinderRPMatrixNonnegative_of_tendsto_cf Ls νseq ν hcf n f c
  exact hperiod.mono fun k hk => hnoWrap k R hR hk n f c hfR

/-- Joint weak-measure and link-reflection limit for one fixed cylinder RP
matrix. The finite matrices may use a moving link reflection, provided their
quadratic moment controls vanish on every test-function sequence tending to
zero. -/
theorem cylinderRPMatrixNonnegative_of_link_limit
    (Lt Ls : ℝ) [Fact (0 < Lt)] [Fact (0 < Ls)]
    (μseq : ℕ → Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    (hμseq_prob : ∀ k, IsProbabilityMeasure (μseq k))
    (hμ_prob : IsProbabilityMeasure μ)
    (hbc : ∀ (g : Configuration (AsymTorusTestFunction Lt Ls) → ℝ),
      Continuous g → (∃ B, ∀ x, |g x| ≤ B) →
      Tendsto (fun k => ∫ ω, g ω ∂(μseq k)) atTop (nhds (∫ ω, g ω ∂μ)))
    (a : ℕ → ℝ) (ha0 : Tendsto a atTop (nhds 0))
    (sigmaSq : ℕ → CylinderTestFunction Ls → ℝ)
    (K C : ℝ) (hK : 0 < K) (hC : 0 < C)
    (hsigmaSq_nonneg : ∀ k h, 0 ≤ sigmaSq k h)
    (hsigmaSq_smul : ∀ k t h, sigmaSq k (t • h) = t ^ 2 * sigmaSq k h)
    (hsigmaSq_zero : ∀ hseq : ℕ → CylinderTestFunction Ls,
      Tendsto hseq atTop (nhds 0) →
      Tendsto (fun k => sigmaSq k (hseq k)) atTop (nhds 0))
    (hExp : ∀ k h,
      Integrable (fun ω : Configuration (CylinderTestFunction Ls) =>
        Real.exp |ω h|) (cylinderPullbackMeasure Lt Ls (μseq k)) ∧
      ∫ ω : Configuration (CylinderTestFunction Ls), Real.exp |ω h|
          ∂(cylinderPullbackMeasure Lt Ls (μseq k)) ≤
        K * Real.exp (C * sigmaSq k h))
    (n : ℕ) (f : Fin n → ↥(cylinderPositiveTimeSubmodule Ls))
    (c : Fin n → ℂ)
    (hlink : ∀ k, CylinderLinkRPMatrixNonnegative Ls
      (cylinderPullbackMeasure Lt Ls (μseq k)) (a k) n f c) :
    CylinderRPMatrixNonnegative Ls (cylinderPullbackMeasure Lt Ls μ) n f c := by
  have hcf : ∀ g : CylinderTestFunction Ls,
      Tendsto
        (fun k => ∫ ω, Complex.exp (Complex.I * ↑(ω g))
          ∂(cylinderPullbackMeasure Lt Ls (μseq k)))
        atTop
        (nhds (∫ ω, Complex.exp (Complex.I * ↑(ω g))
          ∂(cylinderPullbackMeasure Lt Ls μ))) :=
    cylinderPullbackMeasure_cexp_tendsto_of_tendsto_bc
      Lt Ls μseq μ hμseq_prob hμ_prob hbc
  have hentry : ∀ i j : Fin n,
      Tendsto
        (fun k => ∫ ω, Complex.exp (Complex.I *
          ↑(ω ((f i : CylinderTestFunction Ls) -
            cylinderLinkReflection Ls (a k) (f j : CylinderTestFunction Ls))))
          ∂(cylinderPullbackMeasure Lt Ls (μseq k)))
        atTop
        (nhds (∫ ω, Complex.exp (Complex.I *
          ↑(ω ((f i : CylinderTestFunction Ls) -
            cylinderTimeReflection Ls (f j : CylinderTestFunction Ls))))
          ∂(cylinderPullbackMeasure Lt Ls μ))) := by
    intro i j
    let gtime : CylinderTestFunction Ls :=
      (f i : CylinderTestFunction Ls) -
        cylinderTimeReflection Ls (f j : CylinderTestFunction Ls)
    let glink : ℕ → CylinderTestFunction Ls := fun k =>
      (f i : CylinderTestFunction Ls) -
        cylinderLinkReflection Ls (a k) (f j : CylinderTestFunction Ls)
    let d : ℕ → CylinderTestFunction Ls := fun k =>
      cylinderTimeReflection Ls (f j : CylinderTestFunction Ls) -
        cylinderLinkReflection Ls (a k) (f j : CylinderTestFunction Ls)
    have href_tend : Tendsto
        (fun k => cylinderLinkReflection Ls (a k) (f j : CylinderTestFunction Ls))
        atTop (nhds (cylinderTimeReflection Ls (f j : CylinderTestFunction Ls))) :=
      (cylinderLinkReflection_tendsto_timeReflection
        (Ls := Ls) (f j : CylinderTestFunction Ls)).comp ha0
    have hd_tend : Tendsto d atTop (nhds 0) := by
      have hsub := Filter.Tendsto.const_sub
        (cylinderTimeReflection Ls (f j : CylinderTestFunction Ls)) href_tend
      simpa [d] using hsub
    have hsigma_tend : Tendsto (fun k => sigmaSq k (d k)) atTop (nhds 0) :=
      hsigmaSq_zero d hd_tend
    have hsqrt_tend : Tendsto (fun k => Real.sqrt (sigmaSq k (d k)))
        atTop (nhds 0) := by
      simpa using Real.continuous_sqrt.continuousAt.tendsto.comp hsigma_tend
    have hupper_tend : Tendsto
        (fun k => K * Real.exp 1 * Real.sqrt C * Real.sqrt (sigmaSq k (d k)))
        atTop (nhds 0) := by
      simpa [mul_assoc] using hsqrt_tend.const_mul (K * Real.exp 1 * Real.sqrt C)
    have hdiff : Tendsto
        (fun k =>
          (∫ ω, Complex.exp (Complex.I * ↑(ω (glink k)))
              ∂(cylinderPullbackMeasure Lt Ls (μseq k))) -
            ∫ ω, Complex.exp (Complex.I * ↑(ω gtime))
              ∂(cylinderPullbackMeasure Lt Ls (μseq k)))
        atTop (nhds 0) := by
      apply squeeze_zero_norm
      · intro k
        letI : IsProbabilityMeasure (μseq k) := hμseq_prob k
        haveI : IsProbabilityMeasure (cylinderPullbackMeasure Lt Ls (μseq k)) := by
          unfold cylinderPullbackMeasure
          have hmeas : Measurable (cylinderPullback Lt Ls) :=
            configuration_measurable_of_eval_measurable _
              (fun φ => configuration_eval_measurable _)
          exact Measure.isProbabilityMeasure_map
            hmeas.aemeasurable
        have hExp_scaled : ∀ t : ℝ,
            Integrable (fun ω : Configuration (CylinderTestFunction Ls) =>
              Real.exp |ω (t • d k)|) (cylinderPullbackMeasure Lt Ls (μseq k)) ∧
            ∫ ω : Configuration (CylinderTestFunction Ls), Real.exp |ω (t • d k)|
                ∂(cylinderPullbackMeasure Lt Ls (μseq k)) ≤
              K * Real.exp (C * t ^ 2 * sigmaSq k (d k)) := by
          intro t
          obtain ⟨hint, hle⟩ := hExp k (t • d k)
          refine ⟨hint, ?_⟩
          rw [hsigmaSq_smul k t (d k)] at hle
          simpa [mul_assoc] using hle
        obtain ⟨hd_int, hd_bound⟩ := absMoment_le_of_uniform_expMoment
          (cylinderPullbackMeasure Lt Ls (μseq k)) (d k) K C
          (sigmaSq k (d k)) hK hC (hsigmaSq_nonneg k (d k)) hExp_scaled
        have hdist_int : Integrable
            (configuration_cexp_eval_dist gtime (glink k))
            (cylinderPullbackMeasure Lt Ls (μseq k)) := by
          have hglink_int := configuration_cexp_eval_integrable
            (cylinderPullbackMeasure Lt Ls (μseq k)) (glink k)
          have hgtime_int := configuration_cexp_eval_integrable
            (cylinderPullbackMeasure Lt Ls (μseq k)) gtime
          simpa [configuration_cexp_eval_dist,
            configuration_cexp_eval_sub_integrand] using
              (hglink_int.sub hgtime_int).norm
        calc
          ‖(∫ ω, Complex.exp (Complex.I * ↑(ω (glink k)))
                ∂(cylinderPullbackMeasure Lt Ls (μseq k))) -
              ∫ ω, Complex.exp (Complex.I * ↑(ω gtime))
                ∂(cylinderPullbackMeasure Lt Ls (μseq k))‖
              ≤ ∫ ω, configuration_cexp_eval_dist gtime (glink k) ω
                  ∂(cylinderPullbackMeasure Lt Ls (μseq k)) :=
            norm_configuration_expIntegral_sub_le_integral_cexp_eval_dist
              (cylinderPullbackMeasure Lt Ls (μseq k)) gtime (glink k)
          _ ≤ ∫ ω, |ω (d k)| ∂(cylinderPullbackMeasure Lt Ls (μseq k)) := by
            apply integral_mono hdist_int hd_int
            intro ω
            simpa [gtime, glink, d] using
              configuration_cexp_eval_dist_le_abs_eval_sub gtime (glink k) ω
          _ ≤ K * Real.exp 1 * Real.sqrt C * Real.sqrt (sigmaSq k (d k)) :=
            hd_bound
      · exact hupper_tend
    have htime := hcf gtime
    have hadd := htime.add hdiff
    simpa [gtime, glink, add_sub_cancel_left] using hadd
  have hsum_tend : Tendsto
      (fun k =>
        (∑ i, ∑ j, c i * starRingEnd ℂ (c j) *
          ∫ ω, Complex.exp (Complex.I *
            ↑(ω ((f i : CylinderTestFunction Ls) -
              cylinderLinkReflection Ls (a k) (f j : CylinderTestFunction Ls))))
            ∂(cylinderPullbackMeasure Lt Ls (μseq k))).re)
      atTop
      (nhds ((∑ i, ∑ j, c i * starRingEnd ℂ (c j) *
        ∫ ω, Complex.exp (Complex.I *
          ↑(ω ((f i : CylinderTestFunction Ls) -
            cylinderTimeReflection Ls (f j : CylinderTestFunction Ls))))
          ∂(cylinderPullbackMeasure Lt Ls μ)).re)) := by
    apply Complex.continuous_re.continuousAt.tendsto.comp
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      Filter.Tendsto.const_mul (c i * starRingEnd ℂ (c j)) (hentry i j)
  unfold CylinderRPMatrixNonnegative
  exact ge_of_tendsto hsum_tend
    (Filter.Eventually.of_forall fun k => by
      simpa [CylinderLinkRPMatrixNonnegative] using hlink k)

end Pphi2
