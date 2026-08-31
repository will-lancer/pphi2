/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Continuous-spin configurations

The spin at every site is a real number.  The measurable space on
`Site → ℝ` is the product Borel space supplied by Mathlib.
-/

namespace Pphi2.ClusterExpansion

/-- An unbounded continuous-spin configuration. -/
abbrev ContinuousConfig (Site : Type*) := Site → ℝ

/-- A coordinate projection is measurable for the product Borel structure. -/
theorem continuousConfig_eval_measurable {Site : Type*} (i : Site) :
    Measurable (fun φ : ContinuousConfig Site => φ i) :=
  measurable_pi_apply i

/-- A coordinate projection is continuous for the product topology. -/
theorem continuousConfig_eval_continuous {Site : Type*} (i : Site) :
    Continuous (fun φ : ContinuousConfig Site => φ i) :=
  continuous_apply i

/-- Every real value occurs at each coordinate.  This records the unbounded
spin space used by K18-1. -/
theorem continuousConfig_eval_surjective {Site : Type*} (i : Site) :
    Function.Surjective (fun φ : ContinuousConfig Site => φ i) := by
  intro x
  classical
  refine ⟨fun j => if j = i then x else 0, ?_⟩
  simp

end Pphi2.ClusterExpansion
