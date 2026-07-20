/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Pphi2.AsymTorus.AsymLinkReflectionRPLimit
import Pphi2.AsymTorus.AsymTorusOS
import Pphi2.AsymTorus.AsymWickVariance
import Pphi2.AsymTorus.MomentBoundOS1
import GaussianField.Symmetry

/-!
# OS symmetry for the heterogeneous isotropic cutoff family

This file proves the translation and time-reflection invariances needed for
the metric-correct `asymTorusInteractingMeasureIso` construction.  The older
results in `AsymTorusOS` concern the square, geometric-mean-spacing cutoff
family and therefore do not apply to the heterogeneous `ZMod Nt × ZMod Ns`
family used by the cylinder construction.
-/

noncomputable section

open GaussianField MeasureTheory Filter Complex

namespace Pphi2

variable (Lt Ls : ℝ) [hLt : Fact (0 < Lt)] [hLs : Fact (0 < Ls)]

/-! ## Finite heterogeneous-lattice symmetries -/

/-- The linear action on lattice test fields induced by a permutation of the
heterogeneous lattice sites. -/
private noncomputable def asymIsoSitePermuteCLM {Nt Ns : ℕ} [NeZero Nt] [NeZero Ns]
    (σ : AsymLatticeSites Nt Ns ≃ AsymLatticeSites Nt Ns) :
    AsymLatticeField Nt Ns →L[ℝ] AsymLatticeField Nt Ns :=
  let L : AsymLatticeField Nt Ns →ₗ[ℝ] AsymLatticeField Nt Ns :=
    { toFun := fun f => f ∘ σ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  { L with cont := L.continuous_of_finiteDimensional }

@[simp] private theorem asymIsoSitePermuteCLM_apply {Nt Ns : ℕ}
    [NeZero Nt] [NeZero Ns]
    (σ : AsymLatticeSites Nt Ns ≃ AsymLatticeSites Nt Ns)
    (f : AsymLatticeField Nt Ns) (x : AsymLatticeSites Nt Ns) :
    asymIsoSitePermuteCLM σ f x = f (σ x) := by
  rfl

private theorem asymIsoSitePermuteCLM_delta {Nt Ns : ℕ}
    [NeZero Nt] [NeZero Ns]
    (σ : AsymLatticeSites Nt Ns ≃ AsymLatticeSites Nt Ns)
    (x : AsymLatticeSites Nt Ns) :
    asymIsoSitePermuteCLM σ (asymLatticeDelta Nt Ns x) =
      asymLatticeDelta Nt Ns (σ.symm x) := by
  ext y
  simp only [asymIsoSitePermuteCLM_apply, asymLatticeDelta]
  simp only [σ.apply_eq_iff_eq_symm_apply]

/-- A covariance-preserving site permutation preserves the heterogeneous
interacting lattice measure. -/
private theorem asymInteractingLatticeMeasureIso_symmetry_map
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (σ : AsymLatticeSites Nt Ns ≃ AsymLatticeSites Nt Ns)
    (hσ_cov : ∀ f : AsymLatticeField Nt Ns,
      covariance (latticeCovarianceAsymGJ Nt Ns a mass ha hmass)
          (asymIsoSitePermuteCLM σ f) (asymIsoSitePermuteCLM σ f) =
        covariance (latticeCovarianceAsymGJ Nt Ns a mass ha hmass) f f) :
    (interactingLatticeMeasureAsym Nt Ns P a mass ha hmass).map
        (configurationPullback (asymIsoSitePermuteCLM σ)) =
      interactingLatticeMeasureAsym Nt Ns P a mass ha hmass := by
  set μG := latticeGaussianMeasureAsym Nt Ns a mass ha hmass
  set bw := boltzmannWeightAsym Nt Ns P a mass
  set Lσ := asymIsoSitePermuteCLM σ
  have hμG_map : μG.map (configurationPullback Lσ) = μG := by
    dsimp only [μG, latticeGaussianMeasureAsym]
    apply measure_invariant_of_covariance_preserved
    intro f
    change covariance (latticeCovarianceAsymGJ Nt Ns a mass ha hmass)
        (Lσ f) (Lσ f) =
      covariance (latticeCovarianceAsymGJ Nt Ns a mass ha hmass) f f
    exact hσ_cov f
  have hΦ_mp : MeasurePreserving (configurationPullback Lσ) μG μG :=
    ⟨measurable_configurationPullback Lσ, hμG_map⟩
  have hBW_config : ∀ ω : Configuration (AsymLatticeField Nt Ns),
      bw (configurationPullback Lσ ω) = bw ω := by
    intro ω
    suffices hV : interactionFunctionalAsym Nt Ns P a mass
        (configurationPullback Lσ ω) =
        interactionFunctionalAsym Nt Ns P a mass ω by
      simp only [bw, boltzmannWeightAsym, hV]
    unfold interactionFunctionalAsym
    congr 1
    have heval : ∀ x : AsymLatticeSites Nt Ns,
        (configurationPullback Lσ ω) (asymLatticeDelta Nt Ns x) =
          ω (asymLatticeDelta Nt Ns (σ.symm x)) := by
      intro x
      rw [configurationPullback_apply, asymIsoSitePermuteCLM_delta]
    simp_rw [heval]
    simpa using (Equiv.sum_comp σ.symm (fun x : AsymLatticeSites Nt Ns =>
      wickPolynomial P (wickConstantAsym Nt Ns a mass)
        (ω (asymLatticeDelta Nt Ns x))))
  ext s hs
  rw [Measure.map_apply (measurable_configurationPullback Lσ) hs]
  unfold interactingLatticeMeasureAsym
  rw [Measure.smul_apply, Measure.smul_apply,
    withDensity_apply _ ((measurable_configurationPullback Lσ hs)),
    withDensity_apply _ hs]
  congr 1
  have hρ_meas : Measurable (fun ω : Configuration (AsymLatticeField Nt Ns) =>
      ENNReal.ofReal (bw ω)) :=
    ENNReal.measurable_ofReal.comp
      ((interactionFunctionalAsym_measurable Nt Ns P a mass).neg.exp)
  rw [show ∫⁻ ω in configurationPullback Lσ ⁻¹' s, ENNReal.ofReal (bw ω) ∂μG =
      ∫⁻ ω in configurationPullback Lσ ⁻¹' s,
        ENNReal.ofReal (bw (configurationPullback Lσ ω)) ∂μG from
    setLIntegral_congr_fun ((measurable_configurationPullback Lσ) hs)
      (fun ω _ => congrArg ENNReal.ofReal (hBW_config ω).symm)]
  exact hΦ_mp.setLIntegral_comp_preimage hs hρ_meas

/-! ### Translation -/

private theorem asymIsoGJCovariance_translation_invariant
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (v : AsymLatticeSites Nt Ns) (f g : AsymLatticeField Nt Ns) :
    covariance (latticeCovarianceAsymGJ Nt Ns a mass ha hmass)
        (asymShift Nt Ns v f) (asymShift Nt Ns v g) =
      covariance (latticeCovarianceAsymGJ Nt Ns a mass ha hmass) f g := by
  unfold latticeCovarianceAsymGJ covariance
  simp only [ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right,
    starRingEnd_apply, star_trivial]
  rw [show inner ℝ
      ((spectralLatticeCovarianceAsym Nt Ns a mass ha hmass) (asymShift Nt Ns v f))
      ((spectralLatticeCovarianceAsym Nt Ns a mass ha hmass) (asymShift Nt Ns v g)) =
    inner ℝ ((spectralLatticeCovarianceAsym Nt Ns a mass ha hmass) f)
      ((spectralLatticeCovarianceAsym Nt Ns a mass ha hmass) g) from
    covariance_spectralLatticeCovarianceAsym_translation_invariant
      Nt Ns a mass ha hmass v f g]

private theorem asymInteractingLatticeMeasureIso_translation_map
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (j₁ j₂ : ℤ) :
    (interactingLatticeMeasureAsym Nt Ns P a mass ha hmass).map
        (configurationPullback
          (asymIsoSitePermuteCLM (Equiv.subRight
            ((j₁ : ZMod Nt), (j₂ : ZMod Ns))))) =
      interactingLatticeMeasureAsym Nt Ns P a mass ha hmass := by
  apply asymInteractingLatticeMeasureIso_symmetry_map
  intro f
  simpa [asymShift] using
    (asymIsoGJCovariance_translation_invariant Nt Ns a mass ha hmass
      ((j₁ : ZMod Nt), (j₂ : ZMod Ns)) f f)

private theorem evalAsymTorusAtSite_iso_latticeTranslation
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (j₁ j₂ : ℤ) (x : AsymLatticeSites Nt Ns)
    (f : AsymTorusTestFunction Lt Ls) :
    evalAsymTorusAtSite Lt Ls Nt Ns x
        (asymTorusTranslation Lt Ls
          (circleSpacing Lt Nt * j₁, circleSpacing Ls Ns * j₂) f) =
      evalAsymTorusAtSite Lt Ls Nt Ns
        (x - ((j₁ : ZMod Nt), (j₂ : ZMod Ns))) f := by
  simp only [evalAsymTorusAtSite, asymTorusTranslation]
  rw [evalCLM_comp_mapCLM (smoothCircle_coeff_basis Lt) (smoothCircle_coeff_basis Ls)]
  have transl_key : ∀ (P : ℝ) [Fact (0 < P)] (N : ℕ) [NeZero N]
      (k : ZMod N) (j : ℤ),
      ((ContinuousLinearMap.proj k).comp (circleRestriction P N)).comp
          (circleTranslation P (circleSpacing P N * j)) =
        (ContinuousLinearMap.proj (k - (j : ZMod N))).comp
          (circleRestriction P N) := by
    intro P hP N hN k j
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
    have hm_real : (↑(ZMod.val (k - (j : ZMod N))) : ℝ) -
        (↑(ZMod.val k) - ↑j) = ↑N * ↑m := by
      exact_mod_cast hm
    have arith : ↑(ZMod.val k) * P / ↑N - P / ↑N * ↑j =
        ↑(ZMod.val (k - (j : ZMod N))) * P / ↑N + ↑(-m) * P := by
      rw [show ↑(ZMod.val k) * P / ↑N - P / ↑N * ↑j =
        (↑(ZMod.val k) - ↑j) * P / ↑N from by ring]
      rw [show (↑(ZMod.val k) - ↑j : ℝ) =
        ↑(ZMod.val (k - (j : ZMod N))) - ↑N * ↑m from by linarith]
      rw [show (↑(ZMod.val (k - (j : ZMod N))) - ↑N * ↑m) * P / ↑N =
        ↑(ZMod.val (k - (j : ZMod N))) * P / ↑N - ↑m * (↑N * P / ↑N) from by ring]
      rw [show (↑N : ℝ) * P / ↑N = P from by
        rw [mul_comm]
        exact mul_div_cancel_of_imp (fun h => absurd h hN_ne)]
      push_cast
      linarith
    rw [arith]
    exact (g.periodic.int_mul (-m)) _
  rw [transl_key Lt Nt x.1 j₁, transl_key Ls Ns x.2 j₂]
  congr 1

/-- Cutoff-level lattice translation invariance for the heterogeneous Iso
interacting torus measure. -/
theorem asymTorusInteractingMeasureIso_gf_latticeTranslation_invariant
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a : ℝ) (P : InteractionPolynomial) (mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (hvolt : (Nt : ℝ) * a = Lt) (hvols : (Ns : ℝ) * a = Ls)
    (j₁ j₂ : ℤ) (f : AsymTorusTestFunction Lt Ls) :
    asymTorusGeneratingFunctional Lt Ls
        (asymTorusInteractingMeasureIso Lt Ls Nt Ns a P mass ha hmass) f =
      asymTorusGeneratingFunctional Lt Ls
        (asymTorusInteractingMeasureIso Lt Ls Nt Ns a P mass ha hmass)
        (asymTorusTranslation Lt Ls (a * j₁, a * j₂) f) := by
  have hspacing_t : circleSpacing Lt Nt = a := by
    unfold circleSpacing
    rw [← hvolt]
    field_simp [Nat.cast_ne_zero.mpr (NeZero.ne Nt)]
  have hspacing_s : circleSpacing Ls Ns = a := by
    unfold circleSpacing
    rw [← hvols]
    field_simp [Nat.cast_ne_zero.mpr (NeZero.ne Ns)]
  have h_lattice_trans : ∀ x : AsymLatticeSites Nt Ns,
      asymLatticeTestFnIso Lt Ls Nt Ns a
          (asymTorusTranslation Lt Ls (a * j₁, a * j₂) f) x =
        asymLatticeTestFnIso Lt Ls Nt Ns a f
          (x - ((j₁ : ZMod Nt), (j₂ : ZMod Ns))) := by
    intro x
    simp only [asymLatticeTestFnIso, evalAsymTorusAtSiteGJ_apply]
    congr 1
    have h := evalAsymTorusAtSite_iso_latticeTranslation Lt Ls Nt Ns j₁ j₂ x f
    rw [hspacing_t, hspacing_s] at h
    exact h
  unfold asymTorusGeneratingFunctional asymTorusInteractingMeasureIso
  set μL := interactingLatticeMeasureAsym Nt Ns P a mass ha hmass
  have hι : AEMeasurable (asymTorusEmbedLiftIso Lt Ls Nt Ns a) μL :=
    (asymTorusEmbedLiftIso_measurable Lt Ls Nt Ns a).aemeasurable
  have hsm₁ : AEStronglyMeasurable
      (fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
        Complex.exp (Complex.I * ↑(ω f)))
      (Measure.map (asymTorusEmbedLiftIso Lt Ls Nt Ns a) μL) :=
    (Complex.measurable_exp.comp (measurable_const.mul
      (Complex.measurable_ofReal.comp
        (configuration_eval_measurable f)))).aestronglyMeasurable
  have hsm₂ : AEStronglyMeasurable
      (fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
        Complex.exp (Complex.I * ↑(ω
          (asymTorusTranslation Lt Ls (a * j₁, a * j₂) f))))
      (Measure.map (asymTorusEmbedLiftIso Lt Ls Nt Ns a) μL) :=
    (Complex.measurable_exp.comp (measurable_const.mul
      (Complex.measurable_ofReal.comp
        (configuration_eval_measurable _)))).aestronglyMeasurable
  rw [integral_map hι hsm₁, integral_map hι hsm₂]
  simp_rw [asymTorusEmbedLiftIso_eval_eq]
  have hpull : ∀ ω : Configuration (AsymLatticeField Nt Ns),
      ω (asymLatticeTestFnIso Lt Ls Nt Ns a
        (asymTorusTranslation Lt Ls (a * j₁, a * j₂) f)) =
      (configurationPullback
        (asymIsoSitePermuteCLM (Equiv.subRight
          ((j₁ : ZMod Nt), (j₂ : ZMod Ns)))) ω)
        (asymLatticeTestFnIso Lt Ls Nt Ns a f) := by
    intro ω
    rw [configurationPullback_apply]
    congr 1
    ext x
    exact h_lattice_trans x
  simp_rw [hpull]
  let Φ := configurationPullback
    (asymIsoSitePermuteCLM (Equiv.subRight ((j₁ : ZMod Nt), (j₂ : ZMod Ns))))
  let F : Configuration (AsymLatticeField Nt Ns) → ℂ := fun ω =>
    Complex.exp (Complex.I * ↑(ω (asymLatticeTestFnIso Lt Ls Nt Ns a f)))
  have hΦ : Measurable Φ := measurable_configurationPullback _
  have hF : AEStronglyMeasurable F (Measure.map Φ μL) :=
    (Complex.measurable_exp.comp (measurable_const.mul
      (Complex.measurable_ofReal.comp
        (configuration_eval_measurable _)))).aestronglyMeasurable
  calc
    ∫ ω, F ω ∂μL = ∫ ω, F ω ∂(Measure.map Φ μL) := by
      rw [asymInteractingLatticeMeasureIso_translation_map Nt Ns P a mass
        ha hmass j₁ j₂]
    _ = ∫ ω, F (Φ ω) ∂μL := integral_map hΦ.aemeasurable hF

/-! ### Time reflection -/

private def asymIsoTimeReflectionSiteEquiv (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] :
    AsymLatticeSites Nt Ns ≃ AsymLatticeSites Nt Ns where
  toFun x := (-x.1, x.2)
  invFun x := (-x.1, x.2)
  left_inv x := by simp
  right_inv x := by simp

private def asymIsoTimeReflectionField (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (f : AsymLatticeField Nt Ns) : AsymLatticeField Nt Ns :=
  fun x => f (-x.1, x.2)

private theorem finiteLaplacianAsym_timeReflection_commute
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ)
    (f : AsymLatticeField Nt Ns) :
    finiteLaplacianAsym Nt Ns a (asymIsoTimeReflectionField Nt Ns f) =
      asymIsoTimeReflectionField Nt Ns (finiteLaplacianAsym Nt Ns a f) := by
  ext x
  simp only [finiteLaplacianAsym, ContinuousLinearMap.coe_mk', finiteLaplacianAsymLM,
    LinearMap.coe_mk, AddHom.coe_mk, finiteLaplacianAsymFun,
    asymIsoTimeReflectionField]
  congr 2; simp [sub_eq_add_neg, add_comm]

private theorem massOperatorAsym_timeReflection_commute
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass : ℝ)
    (f : AsymLatticeField Nt Ns) :
    massOperatorAsym Nt Ns a mass (asymIsoTimeReflectionField Nt Ns f) =
      asymIsoTimeReflectionField Nt Ns (massOperatorAsym Nt Ns a mass f) := by
  have hΔ := finiteLaplacianAsym_timeReflection_commute Nt Ns a f
  ext x
  simp only [massOperatorAsym, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, Pi.add_apply, Pi.neg_apply, Pi.smul_apply,
    smul_eq_mul, asymIsoTimeReflectionField]
  exact congrArg (fun t => -t + mass ^ 2 * f (-x.1, x.2)) (congr_fun hΔ x)

private theorem asymIsoTimeReflection_sum_mul
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (f g : AsymLatticeField Nt Ns) :
    ∑ x : AsymLatticeSites Nt Ns,
        asymIsoTimeReflectionField Nt Ns f x *
          asymIsoTimeReflectionField Nt Ns g x =
      ∑ x : AsymLatticeSites Nt Ns, f x * g x := by
  exact Fintype.sum_equiv (asymIsoTimeReflectionSiteEquiv Nt Ns)
    (fun x => f x * g x)
    (fun x => asymIsoTimeReflectionField Nt Ns f x *
      asymIsoTimeReflectionField Nt Ns g x)
    (fun x => by simp [asymIsoTimeReflectionField, asymIsoTimeReflectionSiteEquiv]) |>.symm

private theorem covariance_spectralLatticeCovarianceAsym_timeReflection_invariant
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f g : AsymLatticeField Nt Ns) :
    covariance (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass)
        (asymIsoTimeReflectionField Nt Ns f)
        (asymIsoTimeReflectionField Nt Ns g) =
      covariance (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass) f g := by
  obtain ⟨h, rfl⟩ := massOperatorAsym_surjective Nt Ns a mass ha hmass g
  rw [← massOperatorAsym_timeReflection_commute Nt Ns a mass h]
  calc
    covariance (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass)
        (asymIsoTimeReflectionField Nt Ns f)
        (massOperatorAsym Nt Ns a mass (asymIsoTimeReflectionField Nt Ns h)) =
      ∑ x : AsymLatticeSites Nt Ns,
        asymIsoTimeReflectionField Nt Ns f x *
          asymIsoTimeReflectionField Nt Ns h x :=
        spectralCovAsym_massOperator_eq Nt Ns a mass ha hmass _ _
    _ = ∑ x : AsymLatticeSites Nt Ns, f x * h x :=
      asymIsoTimeReflection_sum_mul Nt Ns f h
    _ = covariance (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass) f
        (massOperatorAsym Nt Ns a mass h) :=
      (spectralCovAsym_massOperator_eq Nt Ns a mass ha hmass f h).symm

private theorem asymIsoGJCovariance_timeReflection_invariant
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f g : AsymLatticeField Nt Ns) :
    covariance (latticeCovarianceAsymGJ Nt Ns a mass ha hmass)
        (asymIsoTimeReflectionField Nt Ns f)
        (asymIsoTimeReflectionField Nt Ns g) =
      covariance (latticeCovarianceAsymGJ Nt Ns a mass ha hmass) f g := by
  unfold latticeCovarianceAsymGJ covariance
  simp only [ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right,
    starRingEnd_apply, star_trivial]
  rw [show inner ℝ
      ((spectralLatticeCovarianceAsym Nt Ns a mass ha hmass)
        (asymIsoTimeReflectionField Nt Ns f))
      ((spectralLatticeCovarianceAsym Nt Ns a mass ha hmass)
        (asymIsoTimeReflectionField Nt Ns g)) =
    inner ℝ ((spectralLatticeCovarianceAsym Nt Ns a mass ha hmass) f)
      ((spectralLatticeCovarianceAsym Nt Ns a mass ha hmass) g) from
    covariance_spectralLatticeCovarianceAsym_timeReflection_invariant
      Nt Ns a mass ha hmass f g]

private theorem asymInteractingLatticeMeasureIso_timeReflection_map
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    (interactingLatticeMeasureAsym Nt Ns P a mass ha hmass).map
        (configurationPullback
          (asymIsoSitePermuteCLM (asymIsoTimeReflectionSiteEquiv Nt Ns))) =
      interactingLatticeMeasureAsym Nt Ns P a mass ha hmass := by
  apply asymInteractingLatticeMeasureIso_symmetry_map
  intro f
  simpa [asymIsoTimeReflectionField, asymIsoTimeReflectionSiteEquiv] using
    (asymIsoGJCovariance_timeReflection_invariant Nt Ns a mass ha hmass f f)

private theorem evalAsymTorusAtSite_iso_timeReflection
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (x : AsymLatticeSites Nt Ns) (f : AsymTorusTestFunction Lt Ls) :
    evalAsymTorusAtSite Lt Ls Nt Ns x (asymTorusTimeReflection Lt Ls f) =
      evalAsymTorusAtSite Lt Ls Nt Ns (-x.1, x.2) f := by
  simp only [evalAsymTorusAtSite, asymTorusTimeReflection]
  rw [evalCLM_comp_mapCLM (smoothCircle_coeff_basis Lt) (smoothCircle_coeff_basis Ls)]
  simp only [ContinuousLinearMap.comp_id]
  have key : ((ContinuousLinearMap.proj x.1).comp
      (circleRestriction Lt Nt)).comp (circleReflection Lt) =
    (ContinuousLinearMap.proj (-x.1)).comp (circleRestriction Lt Nt) := by
    ext g
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      circleRestriction_apply, circleReflection, circlePoint]
    congr 1
    rw [ZMod.neg_val x.1]
    split
    · next hk => simp [hk]
    · next hk =>
      have hval_le : ZMod.val x.1 ≤ Nt := le_of_lt (ZMod.val_lt x.1)
      have hN : (Nt : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne Nt)
      rw [show (↑(Nt - ZMod.val x.1) : ℝ) * Lt / ↑Nt =
          -(↑(ZMod.val x.1) * Lt / ↑Nt) + Lt from by
        rw [Nat.cast_sub hval_le]
        field_simp
        ring]
      exact (g.periodic' _).symm
  rw [key]

/-- Cutoff-level time-reflection invariance for the heterogeneous Iso
interacting torus measure. -/
theorem asymTorusInteractingMeasureIso_gf_timeReflection_invariant
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a : ℝ) (P : InteractionPolynomial) (mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (f : AsymTorusTestFunction Lt Ls) :
    asymTorusGeneratingFunctional Lt Ls
        (asymTorusInteractingMeasureIso Lt Ls Nt Ns a P mass ha hmass) f =
      asymTorusGeneratingFunctional Lt Ls
        (asymTorusInteractingMeasureIso Lt Ls Nt Ns a P mass ha hmass)
        (asymTorusTimeReflection Lt Ls f) := by
  have h_lattice_refl : ∀ x : AsymLatticeSites Nt Ns,
      asymLatticeTestFnIso Lt Ls Nt Ns a (asymTorusTimeReflection Lt Ls f) x =
        asymLatticeTestFnIso Lt Ls Nt Ns a f (-x.1, x.2) := by
    intro x
    simp only [asymLatticeTestFnIso, evalAsymTorusAtSiteGJ_apply]
    exact congrArg (fun r => a * r)
      (evalAsymTorusAtSite_iso_timeReflection Lt Ls Nt Ns x f)
  unfold asymTorusGeneratingFunctional asymTorusInteractingMeasureIso
  set μL := interactingLatticeMeasureAsym Nt Ns P a mass ha hmass
  have hι : AEMeasurable (asymTorusEmbedLiftIso Lt Ls Nt Ns a) μL :=
    (asymTorusEmbedLiftIso_measurable Lt Ls Nt Ns a).aemeasurable
  have hsm₁ : AEStronglyMeasurable
      (fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
        Complex.exp (Complex.I * ↑(ω f)))
      (Measure.map (asymTorusEmbedLiftIso Lt Ls Nt Ns a) μL) :=
    (Complex.measurable_exp.comp (measurable_const.mul
      (Complex.measurable_ofReal.comp
        (configuration_eval_measurable f)))).aestronglyMeasurable
  have hsm₂ : AEStronglyMeasurable
      (fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
        Complex.exp (Complex.I * ↑(ω (asymTorusTimeReflection Lt Ls f))))
      (Measure.map (asymTorusEmbedLiftIso Lt Ls Nt Ns a) μL) :=
    (Complex.measurable_exp.comp (measurable_const.mul
      (Complex.measurable_ofReal.comp
        (configuration_eval_measurable _)))).aestronglyMeasurable
  rw [integral_map hι hsm₁, integral_map hι hsm₂]
  simp_rw [asymTorusEmbedLiftIso_eval_eq]
  have hpull : ∀ ω : Configuration (AsymLatticeField Nt Ns),
      ω (asymLatticeTestFnIso Lt Ls Nt Ns a
        (asymTorusTimeReflection Lt Ls f)) =
      (configurationPullback
        (asymIsoSitePermuteCLM (asymIsoTimeReflectionSiteEquiv Nt Ns)) ω)
        (asymLatticeTestFnIso Lt Ls Nt Ns a f) := by
    intro ω
    rw [configurationPullback_apply]
    congr 1
    ext x
    exact h_lattice_refl x
  simp_rw [hpull]
  let Φ := configurationPullback
    (asymIsoSitePermuteCLM (asymIsoTimeReflectionSiteEquiv Nt Ns))
  let F : Configuration (AsymLatticeField Nt Ns) → ℂ := fun ω =>
    Complex.exp (Complex.I * ↑(ω (asymLatticeTestFnIso Lt Ls Nt Ns a f)))
  have hΦ : Measurable Φ := measurable_configurationPullback _
  have hF : AEStronglyMeasurable F (Measure.map Φ μL) :=
    (Complex.measurable_exp.comp (measurable_const.mul
      (Complex.measurable_ofReal.comp
        (configuration_eval_measurable _)))).aestronglyMeasurable
  calc
    ∫ ω, F ω ∂μL = ∫ ω, F ω ∂(Measure.map Φ μL) := by
      rw [asymInteractingLatticeMeasureIso_timeReflection_map Nt Ns P a mass ha hmass]
    _ = ∫ ω, F (Φ ω) ∂μL := integral_map hΦ.aemeasurable hF

/-! ## OS0 and OS1 from the Green moment bound -/

/-- Analyticity for any asymmetric-torus probability measure carrying a
Green-controlled exponential moment bound. -/
theorem asymTorusOS0_of_greenMomentBound
    (mass : ℝ) (hmass : 0 < mass) (K C : ℝ)
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ]
    (hgreen : MeasureHasGreenMomentBound Ls mass hmass K C μ) :
    AsymTorusOS0_Analyticity Lt Ls μ := by
  intro n J
  rw [analyticOn_univ]
  apply analyticOnNhd_integral
  · intro ω z _
    apply AnalyticAt.cexp'
    have h_eq : ∀ w : Fin n → ℂ,
        Complex.I * (↑(ω (∑ i, (w i).re • J i)) +
          Complex.I * ↑(ω (∑ i, (w i).im • J i))) =
        Complex.I * ∑ i : Fin n, w i * ↑(ω (J i)) := by
      intro w
      congr 1
      simp only [map_sum, map_smul, smul_eq_mul, Complex.ofReal_sum,
        Complex.ofReal_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      congr 1
      ext i
      calc
        ↑(w i).re * ↑(ω (J i)) + Complex.I * (↑(w i).im * ↑(ω (J i))) =
            (↑(w i).re + ↑(w i).im * Complex.I) * ↑(ω (J i)) := by ring
        _ = w i * ↑(ω (J i)) := by rw [re_add_im]
    simp_rw [h_eq]
    exact analyticAt_const.mul (Finset.univ.analyticAt_fun_sum (fun i _ =>
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i).analyticAt z).mul
        analyticAt_const))
  · intro z
    apply (Complex.measurable_exp.comp _).aestronglyMeasurable
    exact measurable_const.mul ((Complex.measurable_ofReal.comp
      (configuration_eval_measurable _)).add (measurable_const.mul
      (Complex.measurable_ofReal.comp (configuration_eval_measurable _))))
  · intro S hS
    obtain ⟨D, hD_nn, hD⟩ := compact_im_bound hS
    by_cases hn : n = 0
    · subst hn
      exact ⟨fun _ => 1, integrable_const 1, fun z _ => ae_of_all μ fun ω => by
        simp only [Finset.univ_eq_empty, Finset.sum_empty, map_zero,
          Complex.ofReal_zero, add_zero, mul_zero, Complex.exp_zero, norm_one]
        rfl⟩
    · set bound := fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
        ∑ i : Fin n, Real.exp (↑n * D * |ω (J i)|)
      refine ⟨bound, ?_, fun z hz => ae_of_all μ fun ω => ?_⟩
      · apply integrable_finsetSum
        intro i _
        have hscale : ∀ ω : Configuration (AsymTorusTestFunction Lt Ls),
            Real.exp (↑n * D * |ω (J i)|) =
              Real.exp (|ω ((↑n * D) • J i)|) := by
          intro ω
          rw [map_smul, smul_eq_mul, abs_mul,
            abs_of_nonneg (mul_nonneg (Nat.cast_nonneg' n) hD_nn)]
        simp_rw [hscale]
        exact (hgreen ((↑n * D) • J i)).1
      · rw [Complex.norm_exp]
        have h_re : (Complex.I * (↑(ω (∑ i, (z i).re • J i)) +
            Complex.I * ↑(ω (∑ i, (z i).im • J i)))).re =
            -(ω (∑ i, (z i).im • J i)) := by
          have h : Complex.I * (↑(ω (∑ i, (z i).re • J i)) +
              Complex.I * ↑(ω (∑ i, (z i).im • J i))) =
              -↑(ω (∑ i, (z i).im • J i)) +
                ↑(ω (∑ i, (z i).re • J i)) * Complex.I := by
            rw [mul_add, ← mul_assoc, Complex.I_mul_I, neg_one_mul]
            ring
          rw [h, Complex.add_re, Complex.neg_re, Complex.ofReal_re,
            Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
        rw [h_re]
        calc
          Real.exp (-(ω (∑ i, (z i).im • J i))) ≤
              Real.exp (|ω (∑ i, (z i).im • J i)|) :=
            Real.exp_le_exp_of_le (neg_le_abs _)
          _ ≤ Real.exp (D * ∑ i : Fin n, |ω (J i)|) := by
            apply Real.exp_le_exp_of_le
            rw [map_sum]
            calc
              |∑ i, ω ((z i).im • J i)| ≤ ∑ i, |ω ((z i).im • J i)| :=
                Finset.abs_sum_le_sum_abs _ _
              _ = ∑ i, |(z i).im| * |ω (J i)| := by
                congr 1
                ext i
                rw [map_smul, smul_eq_mul, abs_mul]
              _ ≤ ∑ i, D * |ω (J i)| :=
                Finset.sum_le_sum (fun i _ =>
                  mul_le_mul_of_nonneg_right (hD z hz i) (abs_nonneg _))
              _ = D * ∑ i, |ω (J i)| := (Finset.mul_sum _ _ _).symm
          _ ≤ bound ω := exp_mul_sum_le (Nat.pos_of_ne_zero hn) D hD_nn _

/-- OS1 regularity for any asymmetric-torus probability measure carrying a
positive Green-controlled exponential moment bound. -/
theorem asymTorusOS1_of_greenMomentBound
    (mass : ℝ) (hmass : 0 < mass) (K C : ℝ)
    (hK : 0 < K) (hC : 0 < C)
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ]
    (hgreen : MeasureHasGreenMomentBound Ls mass hmass K C μ) :
    AsymTorusOS1_Regularity Lt Ls μ := by
  let q : AsymTorusTestFunction Lt Ls → ℝ := fun f =>
    C * GaussianField.asymTorusContinuumGreen Ls Lt mass hmass f f + |Real.log K|
  have hq : Continuous q := by
    exact (greenFunctionBilinear_continuous_diag mass hmass).const_mul C |>.add continuous_const
  refine ⟨q, hq, 1, one_pos, ?_⟩
  intro f_re f_im
  obtain ⟨h_int_im, h_exp_im⟩ := hgreen f_im
  have h_tri : ‖∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
      Complex.exp (Complex.I * (↑(ω f_re) + Complex.I * ↑(ω f_im))) ∂μ‖ ≤
      ∫ ω, ‖Complex.exp
        (Complex.I * (↑(ω f_re) + Complex.I * ↑(ω f_im)))‖ ∂μ :=
    norm_integral_le_integral_norm _
  have h_norm : ∀ ω : Configuration (AsymTorusTestFunction Lt Ls),
      ‖Complex.exp (Complex.I * (↑(ω f_re) + Complex.I * ↑(ω f_im)))‖ =
        Real.exp (-(ω f_im)) := by
    intro ω
    rw [Complex.norm_exp]
    congr 1
    have h : Complex.I * (↑(ω f_re) + Complex.I * ↑(ω f_im)) =
        -↑(ω f_im) + ↑(ω f_re) * Complex.I := by
      rw [mul_add, ← mul_assoc, Complex.I_mul_I, neg_one_mul]
      ring
    rw [h, Complex.add_re, Complex.neg_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  calc
    ‖∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
        Complex.exp (Complex.I * (↑(ω f_re) + Complex.I * ↑(ω f_im))) ∂μ‖ ≤
        ∫ ω, ‖Complex.exp
          (Complex.I * (↑(ω f_re) + Complex.I * ↑(ω f_im)))‖ ∂μ := h_tri
    _ = ∫ ω, Real.exp (-(ω f_im)) ∂μ := by
      congr 1
      ext ω
      exact h_norm ω
    _ ≤ ∫ ω, Real.exp (|ω f_im|) ∂μ := by
      apply integral_mono_of_nonneg
      · exact ae_of_all _ (fun _ => (Real.exp_pos _).le)
      · exact h_int_im
      · exact ae_of_all _ (fun ω => Real.exp_le_exp_of_le (neg_le_abs (ω f_im)))
    _ ≤ K * Real.exp
        (C * GaussianField.asymTorusContinuumGreen Ls Lt mass hmass f_im f_im) :=
      h_exp_im
    _ ≤ Real.exp (q f_im) := by
      have hle : K ≤ Real.exp (|Real.log K|) := by
        by_cases h1 : 1 ≤ K
        · rw [abs_of_nonneg (Real.log_nonneg h1), Real.exp_log hK]
        · push Not at h1
          exact le_trans h1.le (Real.one_le_exp (abs_nonneg _))
      calc
        K * Real.exp
            (C * GaussianField.asymTorusContinuumGreen Ls Lt mass hmass f_im f_im) ≤
            Real.exp (|Real.log K|) *
              Real.exp (C * GaussianField.asymTorusContinuumGreen
                Ls Lt mass hmass f_im f_im) :=
          mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
        _ = Real.exp (q f_im) := by
          rw [← Real.exp_add]
          dsimp [q]
          ring_nf
    _ ≤ Real.exp (1 * (q f_re + q f_im)) := by
      rw [one_mul]
      apply Real.exp_le_exp_of_le
      have hgreen_re : 0 ≤ GaussianField.asymTorusContinuumGreen
          Ls Lt mass hmass f_re f_re :=
        greenFunctionBilinear_nonneg mass hmass f_re
      dsimp [q]
      linarith [mul_nonneg hC.le hgreen_re, abs_nonneg (Real.log K)]

/-! ## OS2 for weak limits of heterogeneous Iso cutoffs -/

private lemma asymIsoCosEval_continuous (g : AsymTorusTestFunction Lt Ls) :
    Continuous (fun ω : Configuration (AsymTorusTestFunction Lt Ls) => Real.cos (ω g)) :=
  Real.continuous_cos.comp (WeakDual.eval_continuous g)

private lemma asymIsoCosEval_bounded (g : AsymTorusTestFunction Lt Ls) :
    ∃ D, ∀ ω : Configuration (AsymTorusTestFunction Lt Ls), |Real.cos (ω g)| ≤ D :=
  ⟨1, fun _ => Real.abs_cos_le_one _⟩

private lemma asymIsoSinEval_continuous (g : AsymTorusTestFunction Lt Ls) :
    Continuous (fun ω : Configuration (AsymTorusTestFunction Lt Ls) => Real.sin (ω g)) :=
  Real.continuous_sin.comp (WeakDual.eval_continuous g)

private lemma asymIsoSinEval_bounded (g : AsymTorusTestFunction Lt Ls) :
    ∃ D, ∀ ω : Configuration (AsymTorusTestFunction Lt Ls), |Real.sin (ω g)| ≤ D :=
  ⟨1, fun _ => Real.abs_sin_le_one _⟩

private lemma asymIsoGf_re_eq_cos_integral
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ] (g : AsymTorusTestFunction Lt Ls) :
    (asymTorusGeneratingFunctional Lt Ls μ g).re =
      ∫ ω : Configuration (AsymTorusTestFunction Lt Ls), Real.cos (ω g) ∂μ := by
  simpa [asymTorusGeneratingFunctional] using configuration_expIntegral_re_eq_integral_cos μ g

private lemma asymIsoGf_im_eq_sin_integral
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ] (g : AsymTorusTestFunction Lt Ls) :
    (asymTorusGeneratingFunctional Lt Ls μ g).im =
      ∫ ω : Configuration (AsymTorusTestFunction Lt Ls), Real.sin (ω g) ∂μ := by
  simpa [asymTorusGeneratingFunctional] using configuration_expIntegral_im_eq_integral_sin μ g

/-- Uniform equicontinuity of characteristic functionals from a uniform
second-moment seminorm bound. -/
private theorem asymIsoFamilyGF_sub_norm_le
    (ν : ℕ → Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [∀ n, IsProbabilityMeasure (ν n)]
    (D : ℝ) (hD : 0 < D)
    (p : AsymTorusTestFunction Lt Ls → ℝ) (hp : Continuous p) (hp0 : p 0 = 0)
    (hmom : ∀ (f : AsymTorusTestFunction Lt Ls) (n : ℕ),
      Integrable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) => (ω f) ^ 2) (ν n) ∧
      ∫ ω : Configuration (AsymTorusTestFunction Lt Ls), (ω f) ^ 2 ∂(ν n) ≤
        D * p f ^ 2) :
    ∃ (B : ℝ) (q : AsymTorusTestFunction Lt Ls → ℝ),
      Continuous q ∧ q 0 = 0 ∧
      ∀ (g h : AsymTorusTestFunction Lt Ls) (n : ℕ),
        ‖asymTorusGeneratingFunctional Lt Ls (ν n) g -
          asymTorusGeneratingFunctional Lt Ls (ν n) h‖ ≤ B * q (g - h) := by
  refine ⟨2 * Real.sqrt D, fun f => |p f|, hp.abs, by simp [hp0], ?_⟩
  intro g h n
  let μ := ν n
  have h_combined : ∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
      (ω (g - h)) ^ 2 ∂μ ≤ D * |p (g - h)| ^ 2 := by
    simpa [μ, sq_abs] using (hmom (g - h) n).2
  let F : Configuration (AsymTorusTestFunction Lt Ls) → ℂ := fun ω =>
    Complex.exp (Complex.I * ↑(ω g)) - Complex.exp (Complex.I * ↑(ω h))
  have h_int : ∀ f : AsymTorusTestFunction Lt Ls,
      Integrable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
        Complex.exp (Complex.I * ↑(ω f))) μ := fun f =>
    (integrable_const (1 : ℂ)).mono
      (Complex.continuous_exp.measurable.comp
        (measurable_const.mul (Complex.continuous_ofReal.measurable.comp
          (configuration_eval_measurable f)))).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [norm_one, mul_comm Complex.I]
        exact le_of_eq (Complex.norm_exp_ofReal_mul_I _))
  have h_gf_eq : asymTorusGeneratingFunctional Lt Ls μ g -
      asymTorusGeneratingFunctional Lt Ls μ h = ∫ ω, F ω ∂μ := by
    simp only [asymTorusGeneratingFunctional, F]
    exact (integral_sub (h_int g) (h_int h)).symm
  have hF_bd2 : ∀ ω, ‖F ω‖ ≤ 2 := fun ω => by
    exact (norm_sub_le _ _).trans (by
      rw [mul_comm Complex.I (↑(ω g) : ℂ), Complex.norm_exp_ofReal_mul_I,
        mul_comm Complex.I (↑(ω h) : ℂ), Complex.norm_exp_ofReal_mul_I]
      norm_num)
  have hF_lip : ∀ ω, ‖F ω‖ ≤ |ω (g - h)| := fun ω => by
    have hfactor : F ω = Complex.exp (Complex.I * ↑(ω h)) *
        (Complex.exp (Complex.I * ↑(ω g - ω h)) - 1) := by
      simp only [F]
      rw [mul_sub, mul_one, ← Complex.exp_add]
      congr 1
      push_cast
      ring_nf
    rw [hfactor, norm_mul, mul_comm Complex.I (↑(ω h) : ℂ),
      Complex.norm_exp_ofReal_mul_I, one_mul]
    have h_key : ‖Complex.exp (Complex.I * ↑(ω g - ω h)) - 1‖ ≤
        |ω g - ω h| := by
      rw [Complex.norm_exp_I_mul_ofReal_sub_one]
      calc
        ‖2 * Real.sin ((ω g - ω h) / 2)‖ =
            2 * |Real.sin ((ω g - ω h) / 2)| := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        _ ≤ 2 * |(ω g - ω h) / 2| :=
          mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by norm_num)
        _ = |ω g - ω h| := by
          rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          ring
    exact h_key.trans (by rw [map_sub])
  have hF_sq : ∀ ω, ‖F ω‖ ^ 2 ≤ (ω (g - h)) ^ 2 := fun ω =>
    (sq_le_sq' (by linarith [norm_nonneg (F ω), abs_nonneg (ω (g - h))])
      (hF_lip ω)).trans (le_of_eq (sq_abs _))
  have hF_meas : Measurable F :=
    (Complex.continuous_exp.measurable.comp
      (measurable_const.mul (Complex.continuous_ofReal.measurable.comp
        (configuration_eval_measurable g)))).sub
    (Complex.continuous_exp.measurable.comp
      (measurable_const.mul (Complex.continuous_ofReal.measurable.comp
        (configuration_eval_measurable h))))
  have hF_norm_int : Integrable (fun ω => ‖F ω‖) μ :=
    (integrable_const (2 : ℝ)).mono hF_meas.norm.aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_of_nonneg (norm_nonneg _),
          Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        exact hF_bd2 ω)
  have hF_sq_int : Integrable (fun ω => ‖F ω‖ ^ 2) μ :=
    (integrable_const (4 : ℝ)).mono (hF_meas.norm.pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ ‖F ω‖ ^ 2),
          Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
        exact (sq_le_sq' (by linarith [norm_nonneg (F ω)]) (hF_bd2 ω)).trans
          (by norm_num))
  have hX_sq_int : Integrable
      (fun ω : Configuration (AsymTorusTestFunction Lt Ls) => (ω (g - h)) ^ 2) μ := by
    simpa [μ] using (hmom (g - h) n).1
  have h_sq_bound : ‖asymTorusGeneratingFunctional Lt Ls μ g -
      asymTorusGeneratingFunctional Lt Ls μ h‖ ^ 2 ≤ D * |p (g - h)| ^ 2 := by
    calc
      ‖asymTorusGeneratingFunctional Lt Ls μ g -
          asymTorusGeneratingFunctional Lt Ls μ h‖ ^ 2 = ‖∫ ω, F ω ∂μ‖ ^ 2 := by
        rw [h_gf_eq]
      _ ≤ (∫ ω, ‖F ω‖ ∂μ) ^ 2 :=
        sq_le_sq' (by
          have h1 := norm_nonneg (∫ ω, F ω ∂μ)
          have h2 : (0 : ℝ) ≤ ∫ ω, ‖F ω‖ ∂μ := integral_nonneg fun ω => norm_nonneg (F ω)
          linarith) (norm_integral_le_integral_norm _)
      _ ≤ ∫ ω, ‖F ω‖ ^ 2 ∂μ :=
        ConvexOn.map_integral_le (Even.convexOn_pow (n := 2) even_two)
          (continuousOn_pow 2) isClosed_univ (ae_of_all _ fun _ => Set.mem_univ _)
          hF_norm_int hF_sq_int
      _ ≤ ∫ ω, (ω (g - h)) ^ 2 ∂μ :=
        integral_mono hF_sq_int hX_sq_int (fun ω => hF_sq ω)
      _ ≤ D * |p (g - h)| ^ 2 := h_combined
  calc
    ‖asymTorusGeneratingFunctional Lt Ls μ g -
        asymTorusGeneratingFunctional Lt Ls μ h‖ ≤
        Real.sqrt (D * |p (g - h)| ^ 2) := by
      rw [← Real.sqrt_sq (norm_nonneg _)]
      exact Real.sqrt_le_sqrt h_sq_bound
    _ = Real.sqrt D * |p (g - h)| := by
      rw [Real.sqrt_mul hD.le, Real.sqrt_sq_eq_abs, abs_abs]
    _ ≤ 2 * Real.sqrt D * |p (g - h)| := by
      have hnonneg : 0 ≤ Real.sqrt D * |p (g - h)| :=
        mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
      linarith

private theorem asymIsoFamilyGF_latticeApproximation_error_vanishes
    (ν : ℕ → Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [∀ n, IsProbabilityMeasure (ν n)]
    (D : ℝ) (hD : 0 < D)
    (p : AsymTorusTestFunction Lt Ls → ℝ) (hp : Continuous p) (hp0 : p 0 = 0)
    (hmom : ∀ (f : AsymTorusTestFunction Lt Ls) (n : ℕ),
      Integrable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) => (ω f) ^ 2) (ν n) ∧
      ∫ ω : Configuration (AsymTorusTestFunction Lt Ls), (ω f) ^ 2 ∂(ν n) ≤
        D * p f ^ 2)
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) (ha0 : Tendsto a atTop (nhds 0))
    (htrans : ∀ (n : ℕ) (j₁ j₂ : ℤ) (f : AsymTorusTestFunction Lt Ls),
      asymTorusGeneratingFunctional Lt Ls (ν n) f =
        asymTorusGeneratingFunctional Lt Ls (ν n)
          (asymTorusTranslation Lt Ls (a n * j₁, a n * j₂) f))
    (v : ℝ × ℝ) (f : AsymTorusTestFunction Lt Ls) :
    Tendsto (fun n =>
      asymTorusGeneratingFunctional Lt Ls (ν n) (asymTorusTranslation Lt Ls v f) -
        asymTorusGeneratingFunctional Lt Ls (ν n) f) atTop (nhds 0) := by
  obtain ⟨B, q, hq, hq0, hbound⟩ :=
    asymIsoFamilyGF_sub_norm_le Lt Ls ν D hD p hp hp0 hmom
  let j₁ : ℕ → ℤ := fun n => round (v.1 / a n)
  let j₂ : ℕ → ℤ := fun n => round (v.2 / a n)
  let w : ℕ → ℝ × ℝ := fun n => (a n * j₁ n, a n * j₂ n)
  have h_lattice_inv : ∀ n,
      asymTorusGeneratingFunctional Lt Ls (ν n)
          (asymTorusTranslation Lt Ls (w n) f) =
        asymTorusGeneratingFunctional Lt Ls (ν n) f := by
    intro n
    exact (htrans n (j₁ n) (j₂ n) f).symm
  have h_rewrite : ∀ n,
      asymTorusGeneratingFunctional Lt Ls (ν n) (asymTorusTranslation Lt Ls v f) -
          asymTorusGeneratingFunctional Lt Ls (ν n) f =
        asymTorusGeneratingFunctional Lt Ls (ν n) (asymTorusTranslation Lt Ls v f) -
          asymTorusGeneratingFunctional Lt Ls (ν n)
            (asymTorusTranslation Lt Ls (w n) f) := by
    intro n
    rw [h_lattice_inv n]
  simp_rw [h_rewrite]
  have h_norm_bound : ∀ n,
      ‖asymTorusGeneratingFunctional Lt Ls (ν n) (asymTorusTranslation Lt Ls v f) -
        asymTorusGeneratingFunctional Lt Ls (ν n)
          (asymTorusTranslation Lt Ls (w n) f)‖ ≤
      B * q (asymTorusTranslation Lt Ls v f - asymTorusTranslation Lt Ls (w n) f) :=
    fun n => hbound _ _ n
  have h_w_tendsto : Tendsto w atTop (nhds v) := by
    rw [Prod.tendsto_iff]
    have h_comp : ∀ (vi : ℝ) (ji : ℕ → ℤ),
        (∀ n, ji n = round (vi / a n)) →
        Tendsto (fun n => a n * (ji n : ℝ)) atTop (nhds vi) := by
      intro vi ji hji
      have h_a_half : Tendsto (fun n => a n / 2) atTop (nhds 0) := by
        simpa using ha0.div_const (2 : ℝ)
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le
        (g := fun n => vi - a n / 2) (h := fun n => vi + a n / 2)
      · simpa using tendsto_const_nhds.sub h_a_half
      · simpa using tendsto_const_nhds.add h_a_half
      · intro n
        simp only
        have h_bnd := abs_sub_round (vi / a n)
        rw [abs_le] at h_bnd
        have h1 : vi / a n - (1 : ℝ) / 2 ≤ ↑(ji n) := by
          rw [hji]
          linarith [h_bnd.1]
        have h2 : vi = a n * (vi / a n) :=
          (mul_div_cancel₀ vi (ne_of_gt (ha n))).symm
        linarith [mul_le_mul_of_nonneg_left h1 (ha n).le]
      · intro n
        simp only
        have h_bnd := abs_sub_round (vi / a n)
        rw [abs_le] at h_bnd
        have h1 : ↑(ji n) ≤ vi / a n + (1 : ℝ) / 2 := by
          rw [hji]
          linarith [h_bnd.2]
        have h2 : vi = a n * (vi / a n) :=
          (mul_div_cancel₀ vi (ne_of_gt (ha n))).symm
        linarith [mul_le_mul_of_nonneg_left h1 (ha n).le]
    constructor
    · change Tendsto (fun n => a n * (j₁ n : ℝ)) atTop (nhds v.1)
      exact h_comp v.1 j₁ (fun _ => rfl)
    · change Tendsto (fun n => a n * (j₂ n : ℝ)) atTop (nhds v.2)
      exact h_comp v.2 j₂ (fun _ => rfl)
  have h_Tw_tendsto : Tendsto
      (fun n => asymTorusTranslation Lt Ls (w n) f) atTop
      (nhds (asymTorusTranslation Lt Ls v f)) :=
    (asymTorusTranslation_continuous_in_v Lt Ls f).continuousAt.tendsto.comp h_w_tendsto
  have h_q_tendsto : Tendsto
      (fun n => q (asymTorusTranslation Lt Ls v f -
        asymTorusTranslation Lt Ls (w n) f)) atTop (nhds 0) := by
    have h_sub : Tendsto
        (fun n => asymTorusTranslation Lt Ls v f -
          asymTorusTranslation Lt Ls (w n) f) atTop
        (nhds (asymTorusTranslation Lt Ls v f -
          asymTorusTranslation Lt Ls v f)) :=
      Filter.Tendsto.const_sub _ h_Tw_tendsto
    rw [sub_self] at h_sub
    rw [← hq0]
    exact hq.continuousAt.tendsto.comp h_sub
  apply squeeze_zero_norm (fun n => h_norm_bound n)
  have h := h_q_tendsto.const_mul B
  simpa using h

/-- Translation invariance of the weak limit of a heterogeneous Iso cutoff
family. -/
theorem asymTorusIsoFamilyOS2_translation
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ]
    (ν : ℕ → Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [∀ n, IsProbabilityMeasure (ν n)]
    (D : ℝ) (hD : 0 < D)
    (p : AsymTorusTestFunction Lt Ls → ℝ) (hp : Continuous p) (hp0 : p 0 = 0)
    (hmom : ∀ (f : AsymTorusTestFunction Lt Ls) (n : ℕ),
      Integrable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) => (ω f) ^ 2) (ν n) ∧
      ∫ ω : Configuration (AsymTorusTestFunction Lt Ls), (ω f) ^ 2 ∂(ν n) ≤
        D * p f ^ 2)
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) (ha0 : Tendsto a atTop (nhds 0))
    (htrans : ∀ (n : ℕ) (j₁ j₂ : ℤ) (f : AsymTorusTestFunction Lt Ls),
      asymTorusGeneratingFunctional Lt Ls (ν n) f =
        asymTorusGeneratingFunctional Lt Ls (ν n)
          (asymTorusTranslation Lt Ls (a n * j₁, a n * j₂) f))
    (hconv : ∀ (g : Configuration (AsymTorusTestFunction Lt Ls) → ℝ),
      Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
        Tendsto (fun n => ∫ ω, g ω ∂(ν n)) atTop (nhds (∫ ω, g ω ∂μ))) :
    AsymTorusOS2_TranslationInvariance Lt Ls μ := by
  intro v f
  have hgf : ∀ g : AsymTorusTestFunction Lt Ls, Tendsto
      (fun n => asymTorusGeneratingFunctional Lt Ls (ν n) g) atTop
      (nhds (asymTorusGeneratingFunctional Lt Ls μ g)) := by
    intro g
    have hre : Tendsto (fun n => (asymTorusGeneratingFunctional Lt Ls (ν n) g).re)
        atTop (nhds (asymTorusGeneratingFunctional Lt Ls μ g).re) := by
      simp_rw [asymIsoGf_re_eq_cos_integral]
      exact hconv _ (asymIsoCosEval_continuous Lt Ls g) (asymIsoCosEval_bounded Lt Ls g)
    have him : Tendsto (fun n => (asymTorusGeneratingFunctional Lt Ls (ν n) g).im)
        atTop (nhds (asymTorusGeneratingFunctional Lt Ls μ g).im) := by
      simp_rw [asymIsoGf_im_eq_sin_integral]
      exact hconv _ (asymIsoSinEval_continuous Lt Ls g) (asymIsoSinEval_bounded Lt Ls g)
    rw [show asymTorusGeneratingFunctional Lt Ls μ g =
      ↑(asymTorusGeneratingFunctional Lt Ls μ g).re +
        ↑(asymTorusGeneratingFunctional Lt Ls μ g).im * Complex.I from (re_add_im _).symm]
    exact (hre.ofReal.add (him.ofReal.mul_const Complex.I)).congr (fun n => re_add_im _)
  have hsub := (hgf (asymTorusTranslation Lt Ls v f)).sub (hgf f)
  have hzero := asymIsoFamilyGF_latticeApproximation_error_vanishes Lt Ls
    ν D hD p hp hp0 hmom a ha ha0 htrans v f
  have heq : asymTorusGeneratingFunctional Lt Ls μ (asymTorusTranslation Lt Ls v f) -
      asymTorusGeneratingFunctional Lt Ls μ f = 0 := tendsto_nhds_unique hsub hzero
  exact (sub_eq_zero.mp heq).symm

/-- Time-reflection invariance of the weak limit of a heterogeneous Iso
cutoff family. -/
theorem asymTorusIsoFamilyOS2_timeReflection
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ]
    (ν : ℕ → Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [∀ n, IsProbabilityMeasure (ν n)]
    (hrefl : ∀ (n : ℕ) (f : AsymTorusTestFunction Lt Ls),
      asymTorusGeneratingFunctional Lt Ls (ν n) f =
        asymTorusGeneratingFunctional Lt Ls (ν n) (asymTorusTimeReflection Lt Ls f))
    (hconv : ∀ (g : Configuration (AsymTorusTestFunction Lt Ls) → ℝ),
      Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
        Tendsto (fun n => ∫ ω, g ω ∂(ν n)) atTop (nhds (∫ ω, g ω ∂μ))) :
    AsymTorusOS2_TimeReflectionInvariance Lt Ls μ := by
  intro f
  apply Complex.ext
  · rw [asymIsoGf_re_eq_cos_integral Lt Ls μ f,
      asymIsoGf_re_eq_cos_integral Lt Ls μ (asymTorusTimeReflection Lt Ls f)]
    have hΘ := hconv _ (asymIsoCosEval_continuous Lt Ls (asymTorusTimeReflection Lt Ls f))
      (asymIsoCosEval_bounded Lt Ls (asymTorusTimeReflection Lt Ls f))
    have hf := hconv _ (asymIsoCosEval_continuous Lt Ls f) (asymIsoCosEval_bounded Lt Ls f)
    have hcut : ∀ n, ∫ ω, Real.cos (ω (asymTorusTimeReflection Lt Ls f)) ∂(ν n) =
        ∫ ω, Real.cos (ω f) ∂(ν n) := by
      intro n
      have h := congrArg Complex.re (hrefl n f)
      rw [asymIsoGf_re_eq_cos_integral, asymIsoGf_re_eq_cos_integral] at h
      exact h.symm
    exact tendsto_nhds_unique hf (hΘ.congr hcut)
  · rw [asymIsoGf_im_eq_sin_integral Lt Ls μ f,
      asymIsoGf_im_eq_sin_integral Lt Ls μ (asymTorusTimeReflection Lt Ls f)]
    have hΘ := hconv _ (asymIsoSinEval_continuous Lt Ls (asymTorusTimeReflection Lt Ls f))
      (asymIsoSinEval_bounded Lt Ls (asymTorusTimeReflection Lt Ls f))
    have hf := hconv _ (asymIsoSinEval_continuous Lt Ls f) (asymIsoSinEval_bounded Lt Ls f)
    have hcut : ∀ n, ∫ ω, Real.sin (ω (asymTorusTimeReflection Lt Ls f)) ∂(ν n) =
        ∫ ω, Real.sin (ω f) ∂(ν n) := by
      intro n
      have h := congrArg Complex.im (hrefl n f)
      rw [asymIsoGf_im_eq_sin_integral, asymIsoGf_im_eq_sin_integral] at h
      exact h.symm
    exact tendsto_nhds_unique hf (hΘ.congr hcut)

end Pphi2

end
