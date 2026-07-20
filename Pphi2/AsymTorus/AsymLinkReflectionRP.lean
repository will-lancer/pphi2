/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/

import Pphi2.AsymTorus.AsymLinkReflection
import Pphi2.AsymTorus.AsymReflectionPositivity
import Pphi2.AsymTorus.AsymTorusEmbeddingIso
import Pphi2.IRLimit.CylinderOS

/-!
# Finite Link-Reflection RP Scaffold

This file isolates the finite cylinder link-reflection matrix used by the
Phase-2 A′ adapter. The theorem landed here is conditional on the remaining
torus/lattice no-wrap transport lemma from the Phase-1 lattice RP theorem.
-/

noncomputable section

namespace Pphi2

open GaussianField MeasureTheory
open scoped BigOperators

variable (Lt Ls : ℝ) [Fact (0 < Lt)] [Fact (0 < Ls)]

/-- Torus link-reflection RP matrix for a finite family of torus test functions. -/
def AsymTorusLinkRPMatrixNonnegative
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    (a : ℝ) (n : ℕ) (F : Fin n → AsymTorusTestFunction Lt Ls)
    (c : Fin n → ℂ) : Prop :=
  0 ≤ (∑ i, ∑ j, c i * starRingEnd ℂ (c j) *
    ∫ ω, Complex.exp (Complex.I *
      ↑(ω (F i - asymTorusLinkReflection Lt Ls a (F j)))) ∂μ).re

/-- Cylinder link-reflection RP matrix for a finite family of positive-time cylinder tests. -/
def CylinderLinkRPMatrixNonnegative
    (ν : Measure (Configuration (CylinderTestFunction Ls)))
    (a : ℝ) (n : ℕ)
    (f : Fin n → ↥(cylinderPositiveTimeSubmodule Ls)) (c : Fin n → ℂ) : Prop :=
  0 ≤ (∑ i, ∑ j, c i * starRingEnd ℂ (c j) *
    ∫ ω, Complex.exp (Complex.I *
      ↑(ω ((f i : CylinderTestFunction Ls) -
        cylinderLinkReflection Ls a (f j : CylinderTestFunction Ls)))) ∂ν).re

/-- Compact positive-time pure cylinder tensors supported inside a fixed
symmetric interval. -/
def cylinderPositiveTimeCompactPureTensorsWithin (R : ℝ) :
    Set (CylinderTestFunction Ls) :=
  {u | ∃ (g : SmoothMap_Circle Ls ℝ) (h : SchwartzMap ℝ ℝ),
    h ∈ schwartzPositiveTimeSubmodule ∧
    (∀ t, R < |t| → h t = 0) ∧
    u = NuclearTensorProduct.pure g h}

theorem cylinderPositiveTimeCompactPureTensorsWithin_mono
    {R S : ℝ} (hRS : R ≤ S) :
    cylinderPositiveTimeCompactPureTensorsWithin Ls R ⊆
      cylinderPositiveTimeCompactPureTensorsWithin Ls S := by
  intro u hu
  rcases hu with ⟨g, h, hh, hsupp, rfl⟩
  exact ⟨g, h, hh, fun t ht => hsupp t (lt_of_le_of_lt hRS ht), rfl⟩

/-- Every element of the compact-pure algebraic span has a single positive
support radius containing all pure tensors used in one finite expression. -/
theorem mem_span_cylinderPositiveTimeCompactPureTensors_exists_radius
    (u : CylinderTestFunction Ls)
    (hu : u ∈ Submodule.span ℝ (cylinderPositiveTimeCompactPureTensors Ls)) :
    ∃ R : ℝ, 0 < R ∧ u ∈
      Submodule.span ℝ (cylinderPositiveTimeCompactPureTensorsWithin Ls R) := by
  apply Submodule.span_induction (R := ℝ) (M := CylinderTestFunction Ls)
    (s := cylinderPositiveTimeCompactPureTensors Ls)
    (p := fun v _ => ∃ R : ℝ, 0 < R ∧ v ∈
      Submodule.span ℝ (cylinderPositiveTimeCompactPureTensorsWithin Ls R))
  · intro v hv
    rcases hv with ⟨g, h, T, hT, hh, hsupp, rfl⟩
    exact ⟨T, hT, Submodule.subset_span ⟨g, h, hh, hsupp, rfl⟩⟩
  · exact ⟨1, zero_lt_one, Submodule.zero_mem _⟩
  · intro x y _ _ hx hy
    rcases hx with ⟨Rx, hRx, hx⟩
    rcases hy with ⟨Ry, hRy, hy⟩
    refine ⟨Rx + Ry, add_pos hRx hRy, ?_⟩
    exact Submodule.add_mem _
      (Submodule.span_mono
        (cylinderPositiveTimeCompactPureTensorsWithin_mono Ls (le_add_of_nonneg_right hRy.le)) hx)
      (Submodule.span_mono
        (cylinderPositiveTimeCompactPureTensorsWithin_mono Ls (le_add_of_nonneg_left hRx.le)) hy)
  · intro r x _ hx
    rcases hx with ⟨R, hR, hx⟩
    exact ⟨R, hR, Submodule.smul_mem _ r hx⟩
  · exact hu

/-- A finite family in the compact-pure span admits one common positive
support radius. -/
theorem finite_mem_span_cylinderPositiveTimeCompactPureTensors_exists_radius
    (n : ℕ) (f : Fin n → CylinderTestFunction Ls)
    (hf : ∀ i, f i ∈ Submodule.span ℝ (cylinderPositiveTimeCompactPureTensors Ls)) :
    ∃ R : ℝ, 0 < R ∧ ∀ i, f i ∈
      Submodule.span ℝ (cylinderPositiveTimeCompactPureTensorsWithin Ls R) := by
  choose Ri hRi hfi using fun i =>
    mem_span_cylinderPositiveTimeCompactPureTensors_exists_radius Ls (f i) (hf i)
  let R : ℝ := 1 + ∑ i, Ri i
  have hR : 0 < R := by
    dsimp [R]
    have hsum : 0 ≤ ∑ i, Ri i := Finset.sum_nonneg fun i _ => (hRi i).le
    linarith
  refine ⟨R, hR, fun i => ?_⟩
  have hRi_le : Ri i ≤ R := by
    dsimp [R]
    have hle : Ri i ≤ ∑ j, Ri j :=
      Finset.single_le_sum (fun j _ => (hRi j).le) (Finset.mem_univ i)
    linarith
  exact Submodule.span_mono
    (cylinderPositiveTimeCompactPureTensorsWithin_mono Ls hRi_le) (hfi i)

/-- Cylinder RP restricted to no-wrap compact-span families at a fixed time
period. This is the finite-period property that is eventually available as
the period tends to infinity. -/
def CylinderMeasureNoWrapReflectionPositive
    (ν : Measure (Configuration (CylinderTestFunction Ls))) : Prop :=
  ∀ (R : ℝ), 0 < R → 2 * R < Lt →
    ∀ (n : ℕ) (f : Fin n → ↥(cylinderPositiveTimeSubmodule Ls)) (c : Fin n → ℂ),
      (∀ i, (f i : CylinderTestFunction Ls) ∈
        Submodule.span ℝ (cylinderPositiveTimeCompactPureTensorsWithin Ls R)) →
      CylinderRPMatrixNonnegative Ls ν n f c

/-- Pulling back a torus link-RP matrix along the cylinder embedding gives the cylinder
link-RP matrix. This is the Stage-0 equivariance square at matrix level. -/
theorem cylinderPullbackMeasure_linkRPMatrix_of_asymTorus
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    (a : ℝ) (n : ℕ)
    (f : Fin n → ↥(cylinderPositiveTimeSubmodule Ls)) (c : Fin n → ℂ)
    (hRP : AsymTorusLinkRPMatrixNonnegative Lt Ls μ a n
      (fun i => cylinderToTorusEmbed Lt Ls (f i : CylinderTestFunction Ls)) c) :
    CylinderLinkRPMatrixNonnegative Ls (cylinderPullbackMeasure Lt Ls μ) a n f c := by
  have hentry : ∀ i j,
      (∫ ω, Complex.exp (Complex.I *
        ↑(ω ((f i : CylinderTestFunction Ls) -
          cylinderLinkReflection Ls a (f j : CylinderTestFunction Ls))))
          ∂(cylinderPullbackMeasure Lt Ls μ)) =
      ∫ ω, Complex.exp (Complex.I *
        ↑(ω ((cylinderToTorusEmbed Lt Ls (f i : CylinderTestFunction Ls)) -
          asymTorusLinkReflection Lt Ls a
            (cylinderToTorusEmbed Lt Ls (f j : CylinderTestFunction Ls))))) ∂μ := by
    intro i j
    unfold cylinderPullbackMeasure
    have hmeas : Measurable (cylinderPullback Lt Ls) :=
      configuration_measurable_of_eval_measurable _
        (fun _ => configuration_eval_measurable _)
    let g : CylinderTestFunction Ls :=
      (f i : CylinderTestFunction Ls) -
        cylinderLinkReflection Ls a (f j : CylinderTestFunction Ls)
    have hsm :
        StronglyMeasurable
          (fun ω : Configuration (CylinderTestFunction Ls) =>
            Complex.exp (Complex.I * ↑(ω g))) := by
      have h_eval :
          Measurable (fun ω : Configuration (CylinderTestFunction Ls) => ω g) :=
        configuration_eval_measurable g
      exact (Complex.continuous_exp.measurable.comp
        (measurable_const.mul
          (Complex.continuous_ofReal.measurable.comp h_eval))).stronglyMeasurable
    rw [integral_map_of_stronglyMeasurable hmeas hsm]
    simp only [cylinderPullback_eval, g]
    congr 3
    rw [map_sub]
    simp [cylinderToTorusEmbed_comp_linkReflection]
  unfold AsymTorusLinkRPMatrixNonnegative at hRP
  unfold CylinderLinkRPMatrixNonnegative
  simpa only [hentry] using hRP

/-- A′, conditional finite-lattice form.

For the finite interacting torus measure
`ν = asymTorusInteractingMeasureIso Lt Ls (2*M) Ns a P mass ha hmass`, a torus
link-RP matrix for the embedded cylinder family implies the corresponding
cylinder link-RP matrix for the cylinder pullback measure. The remaining
upstream A′ lemma is precisely to prove the `hRP` hypothesis from
`interactingLatticeMeasureAsym_isReflectionPositive_link` plus the no-wrap
positive-time support condition. -/
theorem asymTorusInteractingMeasureIso_cylinderLinkRPMatrix_conditional
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (M Ns : ℕ) [NeZero M] [NeZero Ns]
    (_hvol_t : ((2 * M : ℕ) : ℝ) * a = Lt)
    (_hvol_s : (Ns : ℝ) * a = Ls)
    (n : ℕ) (f : Fin n → ↥(cylinderPositiveTimeSubmodule Ls)) (c : Fin n → ℂ)
    (hRP :
      AsymTorusLinkRPMatrixNonnegative Lt Ls
        (asymTorusInteractingMeasureIso Lt Ls (2 * M) Ns a P mass ha hmass)
        a n
        (fun i => cylinderToTorusEmbed Lt Ls (f i : CylinderTestFunction Ls)) c) :
    CylinderLinkRPMatrixNonnegative Ls
      (cylinderPullbackMeasure Lt Ls
        (asymTorusInteractingMeasureIso Lt Ls (2 * M) Ns a P mass ha hmass))
      a n f c := by
  exact cylinderPullbackMeasure_linkRPMatrix_of_asymTorus Lt Ls
    (asymTorusInteractingMeasureIso Lt Ls (2 * M) Ns a P mass ha hmass)
    a n f c hRP

private theorem complex_exp_I_sub_eq_exp_mul_conj (a b : ℝ) :
    Complex.exp (Complex.I * ↑(a - b)) =
      Complex.exp (Complex.I * ↑a) * starRingEnd ℂ (Complex.exp (Complex.I * ↑b)) := by
  rw [Complex.ofReal_sub]
  rw [show Complex.I * (↑a - ↑b) = Complex.I * ↑a - Complex.I * ↑b by ring]
  rw [Complex.exp_sub]
  rw [show starRingEnd ℂ (Complex.exp (Complex.I * ↑b)) =
      Complex.exp (-(Complex.I * ↑b)) by
    rw [← Complex.exp_conj]
    congr
    simp]
  rw [Complex.exp_neg]
  field_simp [Complex.exp_ne_zero]

private theorem complexExpMatrix_nonnegative_of_reflectionPositive
    {Ω : Type*} [m0 : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {θ : Ω → Ω} {mPos : MeasurableSpace Ω}
    (hθ : @Measurable Ω Ω m0 m0 θ)
    (hRP : @MeasureTheory.Measure.IsReflectionPositive Ω m0 μ θ mPos)
    (n : ℕ) (c : Fin n → ℂ) (u : Fin n → Ω → ℝ)
    (huPos : ∀ i, @Measurable Ω ℝ mPos _ (u i))
    (hu : ∀ i, @Measurable Ω ℝ m0 _ (u i)) :
    0 ≤ (∑ i, ∑ j, c i * starRingEnd ℂ (c j) *
      ∫ ω, Complex.exp (Complex.I * ↑(u i ω - u j (θ ω))) ∂μ).re := by
  let Z : Ω → ℂ := fun ω => ∑ i, c i * Complex.exp (Complex.I * ↑(u i ω))
  have hZ_meas : @Measurable Ω ℂ m0 _ Z := by
    dsimp [Z]
    exact Finset.measurable_sum Finset.univ (fun i _ =>
      measurable_const.mul
        (Complex.continuous_exp.measurable.comp
          (measurable_const.mul
            (Complex.continuous_ofReal.measurable.comp (hu i)))))
  have hZ_mPos : @Measurable Ω ℂ mPos _ Z := by
    dsimp [Z]
    exact Finset.measurable_sum Finset.univ (fun i _ =>
      measurable_const.mul
        (Complex.continuous_exp.measurable.comp
          (measurable_const.mul
            (Complex.continuous_ofReal.measurable.comp (huPos i)))))
  have hZ_theta_meas : @Measurable Ω ℂ m0 _ (fun ω => Z (θ ω)) := hZ_meas.comp hθ
  have hZ_re_mPos : @Measurable Ω ℝ mPos _ (fun ω => (Z ω).re) :=
    Complex.continuous_re.measurable.comp hZ_mPos
  have hZ_im_mPos : @Measurable Ω ℝ mPos _ (fun ω => (Z ω).im) :=
    Complex.continuous_im.measurable.comp hZ_mPos
  let C : ℝ := ∑ i, ‖c i‖
  have hZ_bound : ∀ ω, ‖Z ω‖ ≤ C := by
    intro ω
    calc
      ‖Z ω‖ ≤ ∑ i : Fin n, ‖c i * Complex.exp (Complex.I * ↑(u i ω))‖ :=
        norm_sum_le _ _
      _ = C := by
        simp [C, Complex.norm_exp_I_mul_ofReal]
  have hprod_int : Integrable (fun ω => Z ω * starRingEnd ℂ (Z (θ ω))) μ := by
    have hsm : @AEStronglyMeasurable Ω ℂ _ m0 m0
        (fun ω => Z ω * starRingEnd ℂ (Z (θ ω))) μ :=
      (hZ_meas.mul (Complex.continuous_conj.measurable.comp hZ_theta_meas)).aestronglyMeasurable
    refine Integrable.of_bound hsm (C * C) (ae_of_all _ fun ω => ?_)
    calc
      ‖Z ω * starRingEnd ℂ (Z (θ ω))‖ = ‖Z ω‖ * ‖Z (θ ω)‖ := by
        simp
      _ ≤ C * C := by
        exact mul_le_mul (hZ_bound ω) (hZ_bound (θ ω)) (norm_nonneg _) (by positivity)
  have hRe_int : Integrable (fun ω => (Z ω).re * (Z (θ ω)).re) μ := by
    have hsm : @AEStronglyMeasurable Ω ℝ _ m0 m0
        (fun ω => (Z ω).re * (Z (θ ω)).re) μ :=
      ((Complex.continuous_re.measurable.comp hZ_meas).mul
        (Complex.continuous_re.measurable.comp hZ_theta_meas)).aestronglyMeasurable
    refine Integrable.of_bound hsm (C * C) (ae_of_all _ fun ω => ?_)
    have hr1 : |(Z ω).re| ≤ C := le_trans (Complex.abs_re_le_norm (Z ω)) (hZ_bound ω)
    have hr2 : |(Z (θ ω)).re| ≤ C :=
      le_trans (Complex.abs_re_le_norm (Z (θ ω))) (hZ_bound (θ ω))
    calc
      ‖(Z ω).re * (Z (θ ω)).re‖ = |(Z ω).re * (Z (θ ω)).re| := by rfl
      _ = |(Z ω).re| * |(Z (θ ω)).re| := abs_mul _ _
      _ ≤ C * C := mul_le_mul hr1 hr2 (abs_nonneg _) (by positivity)
  have hIm_int : Integrable (fun ω => (Z ω).im * (Z (θ ω)).im) μ := by
    have hsm : @AEStronglyMeasurable Ω ℝ _ m0 m0
        (fun ω => (Z ω).im * (Z (θ ω)).im) μ :=
      ((Complex.continuous_im.measurable.comp hZ_meas).mul
        (Complex.continuous_im.measurable.comp hZ_theta_meas)).aestronglyMeasurable
    refine Integrable.of_bound hsm (C * C) (ae_of_all _ fun ω => ?_)
    have hi1 : |(Z ω).im| ≤ C := le_trans (Complex.abs_im_le_norm (Z ω)) (hZ_bound ω)
    have hi2 : |(Z (θ ω)).im| ≤ C :=
      le_trans (Complex.abs_im_le_norm (Z (θ ω))) (hZ_bound (θ ω))
    calc
      ‖(Z ω).im * (Z (θ ω)).im‖ = |(Z ω).im * (Z (θ ω)).im| := by rfl
      _ = |(Z ω).im| * |(Z (θ ω)).im| := abs_mul _ _
      _ ≤ C * C := mul_le_mul hi1 hi2 (abs_nonneg _) (by positivity)
  have hRe_nonneg :
      0 ≤ @MeasureTheory.Measure.reflectionInnerProduct Ω m0 μ θ
        (fun ω => (Z ω).re) (fun ω => (Z ω).re) :=
    hRP (fun ω => (Z ω).re) hZ_re_mPos hRe_int
  have hIm_nonneg :
      0 ≤ @MeasureTheory.Measure.reflectionInnerProduct Ω m0 μ θ
        (fun ω => (Z ω).im) (fun ω => (Z ω).im) :=
    hRP (fun ω => (Z ω).im) hZ_im_mPos hIm_int
  have hprod_re_nonneg : 0 ≤ (∫ ω, Z ω * starRingEnd ℂ (Z (θ ω)) ∂μ).re := by
    let fRe : Ω → ℝ := fun ω => (Z ω).re * (Z (θ ω)).re
    let fIm : Ω → ℝ := fun ω => (Z ω).im * (Z (θ ω)).im
    let fC : Ω → ℂ := fun ω => Z ω * starRingEnd ℂ (Z (θ ω))
    have hpoint : (fun ω => (fC ω).re) = fun ω => fRe ω + fIm ω := by
      funext ω
      simp [fC, fRe, fIm, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    have hre : ∫ ω, (fC ω).re ∂μ = (∫ ω, fC ω ∂μ).re :=
      @integral_re Ω m0 μ ℂ _ fC hprod_int
    have hadd : ∫ ω, fRe ω + fIm ω ∂μ = ∫ ω, fRe ω ∂μ + ∫ ω, fIm ω ∂μ :=
      @integral_add Ω ℝ _ _ m0 μ fRe fIm hRe_int hIm_int
    have hreal : (∫ ω, Z ω * starRingEnd ℂ (Z (θ ω)) ∂μ).re =
        ∫ ω, (Z ω).re * (Z (θ ω)).re + (Z ω).im * (Z (θ ω)).im ∂μ := by
      change (∫ ω, fC ω ∂μ).re = ∫ ω, fRe ω + fIm ω ∂μ
      rw [← hre, hpoint]
    rw [hreal]
    rw [hadd]
    exact add_nonneg hRe_nonneg hIm_nonneg
  have hentry_int : ∀ i j, Integrable
      (fun ω => c i * starRingEnd ℂ (c j) *
        Complex.exp (Complex.I * ↑(u i ω - u j (θ ω)))) μ := by
    intro i j
    have harg : @Measurable Ω ℝ m0 _ (fun ω => u i ω - u j (θ ω)) :=
      (hu i).sub ((hu j).comp hθ)
    have hfactor : @Measurable Ω ℂ m0 _
        (fun ω => Complex.exp (Complex.I * ↑(u i ω - u j (θ ω)))) :=
      Complex.continuous_exp.measurable.comp
        (measurable_const.mul (Complex.continuous_ofReal.measurable.comp harg))
    have hconst : @Measurable Ω ℂ m0 _ (fun _ => c i * starRingEnd ℂ (c j)) :=
      measurable_const
    have hsm : @AEStronglyMeasurable Ω ℂ _ m0 m0
        (fun ω => c i * starRingEnd ℂ (c j) *
          Complex.exp (Complex.I * ↑(u i ω - u j (θ ω)))) μ :=
      (hconst.mul hfactor).aestronglyMeasurable
    refine Integrable.of_bound hsm (‖c i * starRingEnd ℂ (c j)‖) (ae_of_all _ fun ω => ?_)
    have hexp : ‖Complex.exp (Complex.I * ↑(u i ω - u j (θ ω)))‖ = 1 := by
      simpa using Complex.norm_exp_I_mul_ofReal (u i ω - u j (θ ω))
    calc
      ‖c i * starRingEnd ℂ (c j) *
          Complex.exp (Complex.I * ↑(u i ω - u j (θ ω)))‖ =
          ‖c i * starRingEnd ℂ (c j)‖ *
            ‖Complex.exp (Complex.I * ↑(u i ω - u j (θ ω)))‖ := by
            rw [norm_mul]
      _ = ‖c i * starRingEnd ℂ (c j)‖ := by rw [hexp, mul_one]
      _ ≤ ‖c i * starRingEnd ℂ (c j)‖ := le_rfl
  have hmatrix_eq :
      (∑ i, ∑ j, c i * starRingEnd ℂ (c j) *
        ∫ ω, Complex.exp (Complex.I * ↑(u i ω - u j (θ ω))) ∂μ) =
      ∫ ω, Z ω * starRingEnd ℂ (Z (θ ω)) ∂μ := by
    calc
      (∑ i, ∑ j, c i * starRingEnd ℂ (c j) *
          ∫ ω, Complex.exp (Complex.I * ↑(u i ω - u j (θ ω))) ∂μ)
          = ∑ i, ∑ j, ∫ ω, c i * starRingEnd ℂ (c j) *
              Complex.exp (Complex.I * ↑(u i ω - u j (θ ω))) ∂μ := by
            simp_rw [← integral_const_mul]
      _ = ∫ ω, ∑ i, ∑ j, c i * starRingEnd ℂ (c j) *
              Complex.exp (Complex.I * ↑(u i ω - u j (θ ω))) ∂μ := by
            rw [MeasureTheory.integral_finsetSum Finset.univ (fun i _ =>
              MeasureTheory.integrable_finsetSum Finset.univ (fun j _ => hentry_int i j))]
            congr 1
            ext i
            rw [MeasureTheory.integral_finsetSum Finset.univ (fun j _ => hentry_int i j)]
      _ = ∫ ω, Z ω * starRingEnd ℂ (Z (θ ω)) ∂μ := by
            refine integral_congr_ae (ae_of_all _ fun ω => ?_)
            dsimp [Z]
            rw [map_sum, Finset.sum_mul]
            simp_rw [map_mul]
            simp_rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            rw [complex_exp_I_sub_eq_exp_mul_conj]
            ring
  rw [hmatrix_eq]
  exact hprod_re_nonneg

private theorem periodizeCLM_eq_on_large_symmetric_halfPeriod
    {Lt : ℝ} [Fact (0 < Lt)]
    (h : SchwartzMap ℝ ℝ) (T : ℝ) (hT : 0 < T)
    (hsupp : ∀ t, T < |t| → h t = 0)
    (hLt_large : 2 * T < Lt) :
    ∀ t ∈ Set.Icc (-Lt / 2) (Lt / 2),
      (@periodizeCLM Lt ‹Fact (0 < Lt)› h).toFun t = h t := by
  intro t ht
  by_cases ht_nonneg : 0 ≤ t
  · have htI : t ∈ Set.Icc (0 : ℝ) (Lt / 2) := ⟨ht_nonneg, ht.2⟩
    exact periodizeCLM_eq_on_large_period
      (L := Lt) h T hT hsupp (by linarith) t htI
  · have href_supp : ∀ u, T < |u| → schwartzReflection h u = 0 := by
      intro u hu
      simpa [schwartzReflection_apply, abs_neg] using hsupp (-u) (by simpa [abs_neg] using hu)
    have htI : -t ∈ Set.Icc (0 : ℝ) (Lt / 2) := by
      constructor <;> linarith [ht.1, ht.2]
    have href :=
      periodizeCLM_eq_on_large_period
        (L := Lt) (schwartzReflection h) T hT href_supp (by linarith) (-t) htI
    have hcomm :
        (@periodizeCLM Lt ‹Fact (0 < Lt)› (schwartzReflection h)).toFun (-t) =
          (@periodizeCLM Lt ‹Fact (0 < Lt)› h).toFun t := by
      simpa [circleReflection] using
        congrArg (fun f : SmoothMap_Circle Lt ℝ => f (-t))
          (periodizeCLM_comp_schwartzReflection (L := Lt) h)
    calc
      (@periodizeCLM Lt ‹Fact (0 < Lt)› h).toFun t
        = (@periodizeCLM Lt ‹Fact (0 < Lt)› (schwartzReflection h)).toFun (-t) := by
            symm
            exact hcomm
      _ = (schwartzReflection h) (-t) := href
      _ = h t := by simp [schwartzReflection_apply]

private theorem periodizeCLM_eq_sub_period_on_upper_strip
    {Lt : ℝ} [Fact (0 < Lt)]
    (h : SchwartzMap ℝ ℝ) (T : ℝ) (hT : 0 < T)
    (hsupp : ∀ t, T < |t| → h t = 0)
    (hLt_large : 2 * T < Lt) :
    ∀ t ∈ Set.Icc (Lt / 2) Lt,
      (@periodizeCLM Lt ‹Fact (0 < Lt)› h).toFun t = h (t - Lt) := by
  intro t ht
  have hper : (@periodizeCLM Lt ‹Fact (0 < Lt)› h).toFun t =
      (@periodizeCLM Lt ‹Fact (0 < Lt)› h).toFun (t - Lt) := by
    simpa [sub_eq_add_neg, add_assoc] using
      ((@periodizeCLM Lt ‹Fact (0 < Lt)› h).periodic' (t - Lt))
  have ht_sub : t - Lt ∈ Set.Icc (-Lt / 2) (Lt / 2) := by
    constructor <;> linarith [ht.1, ht.2]
  calc
    (@periodizeCLM Lt ‹Fact (0 < Lt)› h).toFun t
      = (@periodizeCLM Lt ‹Fact (0 < Lt)› h).toFun (t - Lt) := hper
    _ = h (t - Lt) :=
      periodizeCLM_eq_on_large_symmetric_halfPeriod h T hT hsupp hLt_large (t - Lt) ht_sub

private theorem asymLatticeTestFnIso_cylinderPure_noWrap_vanish_negative
    (Lt Ls : ℝ) [Fact (0 < Lt)] [Fact (0 < Ls)]
    (M Ns : ℕ) [NeZero M] [NeZero Ns]
    (a R : ℝ) (hR : 0 < R) (hLtR : 2 * R < Lt)
    (g : SmoothMap_Circle Ls ℝ) (h : SchwartzMap ℝ ℝ)
    (hh : h ∈ schwartzPositiveTimeSubmodule)
    (hsupp : ∀ t, R < |t| → h t = 0)
    (x : AsymLatticeSites (2 * M) Ns) (hx : M ≤ x.1.val) :
    asymLatticeTestFnIso Lt Ls (2 * M) Ns a
      (cylinderToTorusEmbed Lt Ls (NuclearTensorProduct.pure g h)) x = 0 := by
  let τ : ℝ := (x.1.val : ℝ) * Lt / (2 * (M : ℝ))
  have hMpos_nat : 0 < M := NeZero.pos M
  have hMpos : 0 < (M : ℝ) := Nat.cast_pos.mpr hMpos_nat
  have hden_pos : (0 : ℝ) < 2 * (M : ℝ) := by nlinarith
  have hden_ne : (2 * (M : ℝ)) ≠ 0 := ne_of_gt hden_pos
  have hden_cast : (((2 * M : ℕ) : ℝ)) = 2 * (M : ℝ) := by norm_num
  have hτ_lower : Lt / 2 ≤ τ := by
    have hLt_pos : 0 < Lt := Fact.out
    have hx_real : (M : ℝ) ≤ (x.1.val : ℝ) := by exact_mod_cast hx
    calc
      Lt / 2 = (M : ℝ) * Lt / (2 * (M : ℝ)) := by field_simp [ne_of_gt hMpos]
      _ ≤ (x.1.val : ℝ) * Lt / (2 * (M : ℝ)) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hx_real (le_of_lt hLt_pos)) (le_of_lt hden_pos)
  have hτ_upper : τ ≤ Lt := by
    have hLt_pos : 0 < Lt := Fact.out
    have hxlt_nat : x.1.val < 2 * M := ZMod.val_lt x.1
    have hxlt_real : (x.1.val : ℝ) ≤ 2 * (M : ℝ) := by
      have : (x.1.val : ℝ) ≤ (((2 * M : ℕ) : ℝ)) := by
        exact_mod_cast (le_of_lt hxlt_nat)
      linarith [hden_cast]
    calc
      (x.1.val : ℝ) * Lt / (2 * (M : ℝ)) ≤
          (2 * (M : ℝ)) * Lt / (2 * (M : ℝ)) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hxlt_real (le_of_lt hLt_pos)) (le_of_lt hden_pos)
      _ = Lt := by field_simp [hden_ne]
  have hper_zero : (@periodizeCLM Lt ‹Fact (0 < Lt)› h).toFun τ = 0 := by
    have hper :=
      periodizeCLM_eq_sub_period_on_upper_strip h R hR hsupp hLtR τ ⟨hτ_lower, hτ_upper⟩
    rw [hper]
    exact hh (τ - Lt) (by linarith)
  have hcoord : x.1.cast * Lt / (2 * (M : ℝ)) = τ := by
    dsimp [τ]
    rw [ZMod.cast_eq_val]
  have hper_zero' : ((periodizeCLM Lt) h) (x.1.cast * Lt / (2 * (M : ℝ))) = 0 := by
    rw [hcoord]
    exact hper_zero
  simp [asymLatticeTestFnIso, evalAsymTorusAtSiteGJ_apply, evalAsymTorusAtSite,
    cylinderToTorusEmbed_pure, NuclearTensorProduct.evalCLM_pure, circleRestriction_apply,
    circlePoint, hden_cast, hper_zero']

private theorem config_eval_measurable_asymLinkMPos_of_vanish_negative
    (M Ns : ℕ) [NeZero M] [NeZero Ns]
    (G : AsymLatticeField (2 * M) Ns)
    (hG : ∀ x : AsymLatticeSites (2 * M) Ns, M ≤ x.1.val → G x = 0) :
    Measurable[asymLinkMPos M Ns]
      (fun ω : Configuration (AsymLatticeField (2 * M) Ns) => ω G) := by
  let H : (AsymHalfSites M Ns → ℝ) → ℝ :=
    fun φp => ∑ i : AsymHalfSites M Ns,
      G (asymLinkPositiveSite M Ns i) * φp i
  have hH : Measurable H := by
    dsimp [H]
    exact Finset.measurable_sum Finset.univ
      (fun i _ => measurable_const.mul (measurable_pi_apply i))
  have hfactor : (fun ω : Configuration (AsymLatticeField (2 * M) Ns) => ω G) =
      H ∘ asymLinkPositivePartConfig M Ns := by
    funext ω
    rw [config_apply_eq_sum_evalMapAsym]
    dsimp [H, asymLinkPositivePartConfig]
    change (∑ x : AsymLatticeSites (2 * M) Ns,
        G x * evalMapAsym (2 * M) Ns ω x) =
      ∑ i : AsymHalfSites M Ns,
        G (asymLinkPositiveSite M Ns i) *
          asymLinkPositivePart M Ns (evalMapAsym (2 * M) Ns ω) i
    rw [show (∑ x : AsymLatticeSites (2 * M) Ns,
        G x * evalMapAsym (2 * M) Ns ω x) =
      ∑ y : Sum (AsymHalfSites M Ns) (AsymHalfSites M Ns),
        G (asymLinkSiteEquiv M Ns y) *
          evalMapAsym (2 * M) Ns ω (asymLinkSiteEquiv M Ns y) by
        symm
        exact Fintype.sum_equiv (asymLinkSiteEquiv M Ns)
          (fun y => G (asymLinkSiteEquiv M Ns y) *
            evalMapAsym (2 * M) Ns ω (asymLinkSiteEquiv M Ns y))
          (fun x => G x * evalMapAsym (2 * M) Ns ω x)
          (fun y => by simp)]
    rw [Fintype.sum_sum_type]
    simp only [asymLinkSiteEquiv_apply_inl, asymLinkSiteEquiv_apply_inr,
      asymLinkPositivePart_apply]
    rw [add_eq_left]
    apply Finset.sum_eq_zero
    intro i _
    rw [hG (asymLinkNegativeSite M Ns i)]
    · simp
    · rcases i with ⟨t, s⟩
      have hval := asymLinkNegativeSite_val (M := M) (Ns := Ns) t s
      have htlt : (t : ℕ) < M := t.2
      omega
  rw [hfactor]
  exact hH.comp (comap_measurable (asymLinkPositivePartConfig M Ns))

private theorem circleRestriction_comp_latticeTranslation
    (P : ℝ) [Fact (0 < P)] (N : ℕ) [NeZero N]
    (k : ZMod N) (j : ℤ) :
    ((ContinuousLinearMap.proj k).comp (circleRestriction P N)).comp
        (circleTranslation P (circleSpacing P N * j)) =
      (ContinuousLinearMap.proj (k - (j : ZMod N))).comp (circleRestriction P N) := by
  ext g
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    circleRestriction_apply, circlePoint, circleSpacing]
  change Real.sqrt (P / ↑N) * g (↑(ZMod.val k) * P / ↑N - P / ↑N * ↑j) =
    Real.sqrt (P / ↑N) * g (↑(ZMod.val (k - (j : ZMod N))) * P / ↑N)
  congr 1
  have hN_ne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hcong : (↑(ZMod.val k) - j : ℤ) ≡
      ↑(ZMod.val (k - (j : ZMod N))) [ZMOD (N : ℤ)] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    simp
  obtain ⟨m, hm⟩ := Int.modEq_iff_dvd.mp hcong
  have arith : ↑(ZMod.val k) * P / ↑N - P / ↑N * ↑j =
      ↑(ZMod.val (k - (j : ZMod N))) * P / ↑N + ↑(-m) * P := by
    have hm_real :
        (↑(ZMod.val (k - (j : ZMod N))) : ℝ) - (↑(ZMod.val k) - ↑j) =
        ↑N * ↑m := by exact_mod_cast hm
    rw [show ↑(ZMod.val k) * P / ↑N - P / ↑N * ↑j =
      (↑(ZMod.val k) - ↑j) * P / ↑N from by ring]
    rw [show (↑(ZMod.val k) - ↑j : ℝ) =
      ↑(ZMod.val (k - (j : ZMod N))) - ↑N * ↑m from by linarith]
    rw [show (↑(ZMod.val (k - (j : ZMod N))) - ↑N * ↑m) * P / ↑N =
      ↑(ZMod.val (k - (j : ZMod N))) * P / ↑N -
        ↑m * (↑N * P / ↑N) from by ring]
    rw [show (↑N : ℝ) * P / ↑N = P from by
      rw [mul_comm]
      exact mul_div_cancel_of_imp (fun h => absurd h hN_ne)]
    push_cast
    linarith
  rw [arith]
  exact (g.periodic.int_mul (-m)) _

private theorem circleRestriction_comp_reflection
    (P : ℝ) [Fact (0 < P)] (N : ℕ) [NeZero N] (k : ZMod N) :
    ((ContinuousLinearMap.proj k).comp (circleRestriction P N)).comp (circleReflection P) =
      (ContinuousLinearMap.proj (-k)).comp (circleRestriction P N) := by
  ext g
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    circleRestriction_apply, circleReflection, circlePoint]
  congr 1
  rw [ZMod.neg_val k]
  split
  · next hk => simp [hk]
  · next hk =>
    have hval_le : ZMod.val k ≤ N := le_of_lt (ZMod.val_lt k)
    have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    rw [show (↑(N - ZMod.val k) : ℝ) * P / ↑N =
        -(↑(ZMod.val k) * P / ↑N) + P from by
      rw [Nat.cast_sub hval_le]
      field_simp [hN]
      ring]
    exact (g.periodic' _).symm

private theorem evalAsymTorusAtSite_linkReflection_of_spacing
    (Lt Ls : ℝ) [Fact (0 < Lt)] [Fact (0 < Ls)]
    (M Ns : ℕ) [NeZero M] [NeZero Ns]
    (a : ℝ) (ha : a = circleSpacing Lt (2 * M))
    (x : AsymLatticeSites (2 * M) Ns) (F : AsymTorusTestFunction Lt Ls) :
    evalAsymTorusAtSite Lt Ls (2 * M) Ns x (asymTorusLinkReflection Lt Ls a F) =
      evalAsymTorusAtSite Lt Ls (2 * M) Ns (asymLinkReflectionSite M Ns x) F := by
  simp only [asymTorusLinkReflection, ContinuousLinearMap.comp_apply]
  simp only [evalAsymTorusAtSite, asymTorusTimeReflection, asymTorusTranslation]
  rw [evalCLM_comp_mapCLM (smoothCircle_coeff_basis Lt) (smoothCircle_coeff_basis Ls)]
  simp only [ContinuousLinearMap.comp_id]
  rw [circleRestriction_comp_reflection Lt (2 * M) x.1]
  rw [evalCLM_comp_mapCLM (smoothCircle_coeff_basis Lt) (smoothCircle_coeff_basis Ls)]
  have htime : ((ContinuousLinearMap.proj (-x.1)).comp
      (circleRestriction Lt (2 * M))).comp (circleTranslation Lt a) =
      (ContinuousLinearMap.proj (-1 - x.1)).comp (circleRestriction Lt (2 * M)) := by
    rw [ha]
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      circleRestriction_comp_latticeTranslation Lt (2 * M) (-x.1) (1 : ℤ)
  have hspace : ((ContinuousLinearMap.proj x.2).comp
      (circleRestriction Ls Ns)).comp (circleTranslation Ls 0) =
      (ContinuousLinearMap.proj x.2).comp (circleRestriction Ls Ns) := by
    rw [circleTranslation_zero]
    simp
  rw [htime, hspace]
  rfl

private theorem asymLatticeTestFnIso_linkReflection_of_spacing
    (Lt Ls : ℝ) [Fact (0 < Lt)] [Fact (0 < Ls)]
    (M Ns : ℕ) [NeZero M] [NeZero Ns]
    (a : ℝ) (ha : a = circleSpacing Lt (2 * M))
    (F : AsymTorusTestFunction Lt Ls) :
    asymLatticeTestFnIso Lt Ls (2 * M) Ns a (asymTorusLinkReflection Lt Ls a F) =
      fun x => asymLatticeTestFnIso Lt Ls (2 * M) Ns a F (asymLinkReflectionSite M Ns x) := by
  funext x
  simp [asymLatticeTestFnIso, evalAsymTorusAtSiteGJ_apply,
    evalAsymTorusAtSite_linkReflection_of_spacing Lt Ls M Ns a ha x F]

private theorem asymLinkReflectionConfig_eval
    (M Ns : ℕ) [NeZero M] [NeZero Ns]
    (ω : Configuration (AsymLatticeField (2 * M) Ns))
    (G : AsymLatticeField (2 * M) Ns) :
    (asymLinkReflectionConfig M Ns ω) G =
      ω (fun x => G (asymLinkReflectionSite M Ns x)) := by
  rw [config_apply_eq_sum_evalMapAsym, config_apply_eq_sum_evalMapAsym]
  simp only [asymLinkReflectionConfig_evalMap, asymLinkReflectionField, Function.comp_apply]
  let e : AsymLatticeSites (2 * M) Ns ≃ AsymLatticeSites (2 * M) Ns :=
    Equiv.ofBijective (asymLinkReflectionSite M Ns)
      (Function.Involutive.bijective (asymLinkReflectionSite_involutive (M := M) (Ns := Ns)))
  calc
    ∑ x : AsymLatticeSites (2 * M) Ns,
        G x * evalMapAsym (2 * M) Ns ω (asymLinkReflectionSite M Ns x)
      = ∑ x : AsymLatticeSites (2 * M) Ns,
          G (asymLinkReflectionSite M Ns x) * evalMapAsym (2 * M) Ns ω x := by
          exact Fintype.sum_equiv e
            (fun x => G x * evalMapAsym (2 * M) Ns ω (asymLinkReflectionSite M Ns x))
            (fun x => G (asymLinkReflectionSite M Ns x) * evalMapAsym (2 * M) Ns ω x)
            (fun x => by simp [e, asymLinkReflectionSite_involutive])
    _ = ∑ x : AsymLatticeSites (2 * M) Ns,
          (fun y => G (asymLinkReflectionSite M Ns y)) x *
            evalMapAsym (2 * M) Ns ω x := rfl

private theorem asymLinkReflectionConfig_measurable
    (M Ns : ℕ) [NeZero M] [NeZero Ns] :
    Measurable (asymLinkReflectionConfig M Ns) := by
  apply configuration_measurable_of_eval_measurable
  intro G
  have hEq : (fun ω : Configuration (AsymLatticeField (2 * M) Ns) =>
      (asymLinkReflectionConfig M Ns ω) G) =
      fun ω => ω (fun x => G (asymLinkReflectionSite M Ns x)) := by
    funext ω
    exact asymLinkReflectionConfig_eval M Ns ω G
  rw [hEq]
  exact configuration_eval_measurable _

/-- Link-reflection positivity for embedded cylinder tests whose lattice images
vanish on the negative link half. This is the exact finite-dimensional support
condition consumed by lattice reflection positivity. -/
theorem asymTorusInteractingMeasureIso_linkRPMatrix_of_vanish_negative
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (M Ns : ℕ) [NeZero M] [NeZero Ns]
    (hvol_t : ((2 * M : ℕ) : ℝ) * a = Lt)
    (_hvol_s : (Ns : ℝ) * a = Ls)
    (n : ℕ) (f : Fin n → ↥(cylinderPositiveTimeSubmodule Ls)) (c : Fin n → ℂ)
    (hvanish : ∀ i (x : AsymLatticeSites (2 * M) Ns), M ≤ x.1.val →
      asymLatticeTestFnIso Lt Ls (2 * M) Ns a
        (cylinderToTorusEmbed Lt Ls (f i : CylinderTestFunction Ls)) x = 0) :
    AsymTorusLinkRPMatrixNonnegative Lt Ls
      (asymTorusInteractingMeasureIso Lt Ls (2 * M) Ns a P mass ha hmass)
      a n (fun i => cylinderToTorusEmbed Lt Ls (f i : CylinderTestFunction Ls)) c := by
  let μL := interactingLatticeMeasureAsym (2 * M) Ns P a mass ha hmass
  let F : Fin n → AsymTorusTestFunction Lt Ls :=
    fun i => cylinderToTorusEmbed Lt Ls (f i : CylinderTestFunction Ls)
  let G : Fin n → AsymLatticeField (2 * M) Ns :=
    fun i => asymLatticeTestFnIso Lt Ls (2 * M) Ns a (F i)
  haveI : IsProbabilityMeasure μL := by
    dsimp [μL]
    exact interactingLatticeMeasureAsym_isProbability (2 * M) Ns P a mass ha hmass
  have hspacing : a = circleSpacing Lt (2 * M) := by
    unfold circleSpacing
    have hden_ne : (((2 * M : ℕ) : ℝ)) ≠ 0 :=
      Nat.cast_ne_zero.mpr (NeZero.ne (2 * M))
    rw [← hvol_t]
    field_simp [hden_ne]
  have hG_pos : ∀ i, Measurable[asymLinkMPos M Ns]
      (fun ω : Configuration (AsymLatticeField (2 * M) Ns) => ω (G i)) := by
    intro i
    apply config_eval_measurable_asymLinkMPos_of_vanish_negative
    intro x hx
    exact hvanish i x hx
  have hG_meas : ∀ i, Measurable
      (fun ω : Configuration (AsymLatticeField (2 * M) Ns) => ω (G i)) :=
    fun i => configuration_eval_measurable (G i)
  have hRP_lattice :
      0 ≤ (∑ i, ∑ j, c i * starRingEnd ℂ (c j) *
        ∫ ω : Configuration (AsymLatticeField (2 * M) Ns),
          Complex.exp (Complex.I *
            (↑(ω (G i)) - ↑((asymLinkReflectionConfig M Ns ω) (G j)))) ∂μL).re := by
    simpa [μL, Complex.ofReal_sub] using
      complexExpMatrix_nonnegative_of_reflectionPositive
        (μ := μL) (θ := asymLinkReflectionConfig M Ns)
        (hθ := asymLinkReflectionConfig_measurable M Ns)
        (hRP := interactingLatticeMeasureAsym_isReflectionPositive_link
          (M := M) (Ns := Ns) P a mass ha hmass)
        n c (fun i ω => ω (G i)) hG_pos hG_meas
  have hentry : ∀ i j,
      (∫ ω, Complex.exp (Complex.I *
        (↑(ω (F i)) - ↑(ω (asymTorusLinkReflection Lt Ls a (F j)))))
        ∂(asymTorusInteractingMeasureIso Lt Ls (2 * M) Ns a P mass ha hmass)) =
      ∫ ω : Configuration (AsymLatticeField (2 * M) Ns),
        Complex.exp (Complex.I *
          (↑(ω (G i)) - ↑((asymLinkReflectionConfig M Ns ω) (G j)))) ∂μL := by
    intro i j
    unfold asymTorusInteractingMeasureIso
    have hmeas : Measurable (asymTorusEmbedLiftIso Lt Ls (2 * M) Ns a) :=
      asymTorusEmbedLiftIso_measurable Lt Ls (2 * M) Ns a
    have hsm :
        StronglyMeasurable
          (fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
            Complex.exp (Complex.I *
              (↑(ω (F i)) -
                ↑(ω (asymTorusLinkReflection Lt Ls a (F j)))))) := by
      have h_evalF : Measurable
          (fun ω : Configuration (AsymTorusTestFunction Lt Ls) => ω (F i)) :=
        configuration_eval_measurable (F i)
      have h_evalR : Measurable
          (fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
            ω (asymTorusLinkReflection Lt Ls a (F j))) :=
        configuration_eval_measurable (asymTorusLinkReflection Lt Ls a (F j))
      have h_evalC : Measurable
          (fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
            (↑(ω (F i)) -
              ↑(ω (asymTorusLinkReflection Lt Ls a (F j))) : ℂ)) :=
        (Complex.continuous_ofReal.measurable.comp h_evalF).sub
          (Complex.continuous_ofReal.measurable.comp h_evalR)
      exact (Complex.continuous_exp.measurable.comp
        (measurable_const.mul h_evalC)).stronglyMeasurable
    rw [integral_map_of_stronglyMeasurable hmeas hsm]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    have hEval_i :
        (asymTorusEmbedLiftIso Lt Ls (2 * M) Ns a ω) (F i) = ω (G i) := by
      simpa [G] using asymTorusEmbedLiftIso_eval_eq Lt Ls (2 * M) Ns a (F i) ω
    have hEval_j :
        (asymTorusEmbedLiftIso Lt Ls (2 * M) Ns a ω)
          (asymTorusLinkReflection Lt Ls a (F j)) =
        (asymLinkReflectionConfig M Ns ω) (G j) := by
      rw [asymTorusEmbedLiftIso_eval_eq Lt Ls (2 * M) Ns a
        (asymTorusLinkReflection Lt Ls a (F j)) ω]
      rw [asymLatticeTestFnIso_linkReflection_of_spacing Lt Ls M Ns a hspacing (F j)]
      rw [asymLinkReflectionConfig_eval M Ns ω (G j)]
    change Complex.exp (Complex.I *
        (↑((asymTorusEmbedLiftIso Lt Ls (2 * M) Ns a ω) (F i)) -
          ↑((asymTorusEmbedLiftIso Lt Ls (2 * M) Ns a ω)
            (asymTorusLinkReflection Lt Ls a (F j))))) =
      Complex.exp (Complex.I *
        (↑(ω (G i)) - ↑((asymLinkReflectionConfig M Ns ω) (G j))))
    rw [hEval_i, hEval_j]
  unfold AsymTorusLinkRPMatrixNonnegative
  simpa [F, G, hentry] using hRP_lattice

/-- A′ no-wrap link-reflection positivity for embedded cylinder pure tensors.

The hypotheses say that each positive-time cylinder test is a pure tensor with
time factor supported in `(0, R)` and that the torus time length satisfies
`Lt = 2*M*a > 2R`, so the embedded lattice observable lies in the positive
link half without wrapping. -/
theorem asymTorusInteractingMeasureIso_linkRPMatrix_noWrap
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (M Ns : ℕ) [NeZero M] [NeZero Ns]
    (hvol_t : ((2 * M : ℕ) : ℝ) * a = Lt)
    (hvol_s : (Ns : ℝ) * a = Ls)
    (R : ℝ) (hR : 0 < R) (hLtR : 2 * R < Lt)
    (n : ℕ) (f : Fin n → ↥(cylinderPositiveTimeSubmodule Ls)) (c : Fin n → ℂ)
    (hf : ∀ i, ∃ (g : SmoothMap_Circle Ls ℝ) (h : SchwartzMap ℝ ℝ),
      h ∈ schwartzPositiveTimeSubmodule ∧
      (∀ t, R < |t| → h t = 0) ∧
      (f i : CylinderTestFunction Ls) = NuclearTensorProduct.pure g h) :
    AsymTorusLinkRPMatrixNonnegative Lt Ls
      (asymTorusInteractingMeasureIso Lt Ls (2 * M) Ns a P mass ha hmass)
      a n (fun i => cylinderToTorusEmbed Lt Ls (f i : CylinderTestFunction Ls)) c := by
  apply asymTorusInteractingMeasureIso_linkRPMatrix_of_vanish_negative
    Lt Ls P a mass ha hmass M Ns hvol_t hvol_s n f c
  intro i x hx
  rcases hf i with ⟨g, h, hh, hsupp, hfi⟩
  rw [hfi]
  exact asymLatticeTestFnIso_cylinderPure_noWrap_vanish_negative
    Lt Ls M Ns a R hR hLtR g h hh hsupp x hx

/-- A′ no-wrap link-reflection positivity for the real span of compact pure
cylinder tensors with a common support radius. -/
theorem asymTorusInteractingMeasureIso_linkRPMatrix_span_noWrap
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (M Ns : ℕ) [NeZero M] [NeZero Ns]
    (hvol_t : ((2 * M : ℕ) : ℝ) * a = Lt)
    (hvol_s : (Ns : ℝ) * a = Ls)
    (R : ℝ) (hR : 0 < R) (hLtR : 2 * R < Lt)
    (n : ℕ) (f : Fin n → ↥(cylinderPositiveTimeSubmodule Ls)) (c : Fin n → ℂ)
    (hf : ∀ i, (f i : CylinderTestFunction Ls) ∈
      Submodule.span ℝ (cylinderPositiveTimeCompactPureTensorsWithin Ls R)) :
    AsymTorusLinkRPMatrixNonnegative Lt Ls
      (asymTorusInteractingMeasureIso Lt Ls (2 * M) Ns a P mass ha hmass)
      a n (fun i => cylinderToTorusEmbed Lt Ls (f i : CylinderTestFunction Ls)) c := by
  apply asymTorusInteractingMeasureIso_linkRPMatrix_of_vanish_negative
    Lt Ls P a mass ha hmass M Ns hvol_t hvol_s n f c
  intro i x hx
  apply Submodule.span_induction (R := ℝ) (M := CylinderTestFunction Ls)
    (s := cylinderPositiveTimeCompactPureTensorsWithin Ls R)
    (p := fun u _ =>
      asymLatticeTestFnIso Lt Ls (2 * M) Ns a
        (cylinderToTorusEmbed Lt Ls u) x = 0)
  · intro u hu
    change ∃ (g : SmoothMap_Circle Ls ℝ) (h : SchwartzMap ℝ ℝ),
      h ∈ schwartzPositiveTimeSubmodule ∧
      (∀ t, R < |t| → h t = 0) ∧
      u = NuclearTensorProduct.pure g h at hu
    rcases hu with ⟨g, h, hh, hsupp, rfl⟩
    exact asymLatticeTestFnIso_cylinderPure_noWrap_vanish_negative
      Lt Ls M Ns a R hR hLtR g h hh hsupp x hx
  · simp [asymLatticeTestFnIso]
  · intro u v _ _ hu hv
    change a * evalAsymTorusAtSite Lt Ls (2 * M) Ns x
        (cylinderToTorusEmbed Lt Ls u) = 0 at hu
    change a * evalAsymTorusAtSite Lt Ls (2 * M) Ns x
        (cylinderToTorusEmbed Lt Ls v) = 0 at hv
    simp only [map_add, asymLatticeTestFnIso, evalAsymTorusAtSiteGJ_apply]
    linarith
  · intro r u _ hu
    change a * evalAsymTorusAtSite Lt Ls (2 * M) Ns x
        (cylinderToTorusEmbed Lt Ls u) = 0 at hu
    simp only [map_smul, asymLatticeTestFnIso, evalAsymTorusAtSiteGJ_apply,
      smul_eq_mul]
    rw [hu, mul_zero]
  · exact hf i

/-- Cylinder-pullback form of A′ for compact pure-tensor spans with a common
no-wrap radius. -/
theorem asymTorusInteractingMeasureIso_cylinderLinkRPMatrix_span_noWrap
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (M Ns : ℕ) [NeZero M] [NeZero Ns]
    (hvol_t : ((2 * M : ℕ) : ℝ) * a = Lt)
    (hvol_s : (Ns : ℝ) * a = Ls)
    (R : ℝ) (hR : 0 < R) (hLtR : 2 * R < Lt)
    (n : ℕ) (f : Fin n → ↥(cylinderPositiveTimeSubmodule Ls)) (c : Fin n → ℂ)
    (hf : ∀ i, (f i : CylinderTestFunction Ls) ∈
      Submodule.span ℝ (cylinderPositiveTimeCompactPureTensorsWithin Ls R)) :
    CylinderLinkRPMatrixNonnegative Ls
      (cylinderPullbackMeasure Lt Ls
        (asymTorusInteractingMeasureIso Lt Ls (2 * M) Ns a P mass ha hmass))
      a n f c := by
  apply asymTorusInteractingMeasureIso_cylinderLinkRPMatrix_conditional
    Lt Ls P a mass ha hmass M Ns hvol_t hvol_s n f c
  exact asymTorusInteractingMeasureIso_linkRPMatrix_span_noWrap
    Lt Ls P a mass ha hmass M Ns hvol_t hvol_s R hR hLtR n f c hf

end Pphi2
