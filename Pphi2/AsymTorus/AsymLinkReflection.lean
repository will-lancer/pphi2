/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/

import Pphi2.IRLimit.CylinderEmbedding
import Pphi2.AsymTorus.AsymTorusOS

/-!
# Link Reflection on the Asymmetric Torus and Cylinder

Small scaffolding for the Phase-2 cylinder RP adapter. The link reflection is
the shifted reflection `t ↦ -t - a`, implemented as time reflection after time
translation by `a`.
-/

noncomputable section

namespace Pphi2

open GaussianField Filter

variable (Lt Ls : ℝ) [Fact (0 < Lt)] [Fact (0 < Ls)]

/-- Link reflection on asymmetric-torus tests: `t ↦ -t - a`.

The definition is time reflection after time translation by `a`, so on pure
temporal factors it sends `f(t)` to `f(-t - a)`. -/
def asymTorusLinkReflection (a : ℝ) :
    AsymTorusTestFunction Lt Ls →L[ℝ] AsymTorusTestFunction Lt Ls :=
  (asymTorusTimeReflection Lt Ls).comp (asymTorusTranslation Lt Ls (a, 0))

/-- Link reflection on cylinder tests: `t ↦ -t - a`.

The cylinder convention has time in the second tensor factor; this is time
reflection after time translation by `a`. -/
def cylinderLinkReflection (a : ℝ) :
    CylinderTestFunction Ls →L[ℝ] CylinderTestFunction Ls :=
  (cylinderTimeReflection Ls).comp (cylinderTranslation Ls 0 a)

/-- The cylinder-to-torus embedding intertwines the cylinder and torus link reflections. -/
theorem cylinderToTorusEmbed_comp_linkReflection
    (a : ℝ) (f : CylinderTestFunction Ls) :
    cylinderToTorusEmbed Lt Ls (cylinderLinkReflection Ls a f) =
    asymTorusLinkReflection Lt Ls a (cylinderToTorusEmbed Lt Ls f) := by
  simp only [cylinderLinkReflection, asymTorusLinkReflection,
    ContinuousLinearMap.comp_apply]
  rw [cylinderToTorusEmbed_comp_timeReflection]
  rw [cylinderToTorusEmbed_comp_timeTranslation]

/-- As the link spacing goes to zero, torus link reflection tends to site reflection. -/
theorem asymTorusLinkReflection_tendsto_timeReflection
    (f : AsymTorusTestFunction Lt Ls) :
    Tendsto (fun a : ℝ => asymTorusLinkReflection Lt Ls a f)
      (nhds 0) (nhds (asymTorusTimeReflection Lt Ls f)) := by
  have hpair :
      Tendsto (fun a : ℝ => (a, (0 : ℝ)))
        (nhds 0) (nhds ((0 : ℝ), (0 : ℝ))) := by
    exact (continuous_id.prodMk continuous_const).continuousAt.tendsto
  have htrans :
      Tendsto
        (fun a : ℝ => asymTorusTranslation Lt Ls (a, (0 : ℝ)) f)
        (nhds 0)
        (nhds (asymTorusTranslation Lt Ls ((0 : ℝ), (0 : ℝ)) f)) := by
    exact (asymTorusTranslation_continuous_in_v Lt Ls f).continuousAt.tendsto.comp hpair
  have hzero : asymTorusTranslation Lt Ls ((0 : ℝ), (0 : ℝ)) f = f := by
    simp [asymTorusTranslation, circleTranslation_zero, nuclearTensorProduct_mapCLM_id]
  have htrans' :
      Tendsto
        (fun a : ℝ => asymTorusTranslation Lt Ls (a, (0 : ℝ)) f)
        (nhds 0) (nhds f) := by
    simpa [hzero] using htrans
  have hΘ :
      Tendsto
        (fun a : ℝ =>
          asymTorusTimeReflection Lt Ls
            (asymTorusTranslation Lt Ls (a, (0 : ℝ)) f))
        (nhds 0) (nhds (asymTorusTimeReflection Lt Ls f)) := by
    exact (asymTorusTimeReflection Lt Ls).cont.continuousAt.tendsto.comp htrans'
  simpa [asymTorusLinkReflection, ContinuousLinearMap.comp_apply] using hΘ

end Pphi2
