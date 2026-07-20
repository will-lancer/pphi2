/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/

import Pphi2.AsymTorus.AsymLinkReflection
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

end Pphi2
