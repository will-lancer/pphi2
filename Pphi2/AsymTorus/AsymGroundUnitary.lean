/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import ReflectionPositivity.GroundMeasure
import ReflectionPositivity.GroundSemigroup

/-!
# Unitarity of the ground-state transform (Layer-B2, GNS Piece A follow-up)

`ReflectionPositivity.GroundMeasure` builds the ground transform
`W : L²(μ_Ω) → L²(ν)`, `W f = f · Ω`, as a *linear isometry*, and its own
docstring defers the unitarity upgrade: *"When `Ω > 0` ν-a.e., this isometry is
unitary; that strengthening is in a follow-up."*  This file is that follow-up.

The content is one lemma — `groundIsometry_surjective`: when `Ω > 0` `ν`-a.e.
one can divide by `Ω`, so every `h ∈ L²(ν)` is `W (h/Ω)`.  Everything else is
formal:

* `GroundSemigroupData.W_apply_WAdjoint` — `W W† = 1` (the isometry already
  gives `W† W = 1`; surjectivity supplies the other side);
* `GroundSemigroupData.groundIsometry_groundSemigroup` — the **intertwining**
  `W ∘ U_t = T̂ᵗ ∘ W`, which for the asym cylinder supplies the formal core of
  `asymGroundSemigroup_intertwines` (`AsymBridgeInstance.lean`).

Nothing here is pphi2-specific; it is stated for a general
`GroundSemigroupData` and is an upstreaming candidate for
`reflection-positivity`.
-/

open MeasureTheory

namespace ReflectionPositivity

variable {S : Type*} [MeasurableSpace S]

/-! ## Surjectivity of the ground transform -/

/-- **W-unitarity (surjectivity).**  When the ground state is `ν`-a.e. strictly
positive, the ground transform `W : L²(μ_Ω) → L²(ν)`, `W f = f · Ω`, is
surjective: the preimage of `h` is `h / Ω`, which lies in `L²(μ_Ω)` precisely
because the `μ_Ω`-norm of `h / Ω` is the `ν`-norm of `h`.

Together with the isometry property this makes `W` unitary, so its Hilbert
adjoint is a two-sided inverse. -/
theorem groundIsometry_surjective {ν : Measure S} {Ω : S → ℝ}
    (hΩ_meas : Measurable Ω) (hΩ_pos : ∀ᵐ x ∂ν, 0 < Ω x) :
    Function.Surjective (groundIsometry (ν := ν) (Ω := Ω) hΩ_meas) := by
  classical
  intro h
  -- a measurable representative `H` of `h`
  set H : S → ℝ := (Lp.aestronglyMeasurable h).mk h with hH_def
  have hH_meas : Measurable H := (Lp.aestronglyMeasurable h).stronglyMeasurable_mk.measurable
  have hH_ae : (⇑h : S → ℝ) =ᵐ[ν] H := (Lp.aestronglyMeasurable h).ae_eq_mk
  -- the candidate preimage `g = H / Ω`
  set g : S → ℝ := fun x => H x / Ω x with hg_def
  have hg_meas : Measurable g := hH_meas.div hΩ_meas
  have hgΩ : (fun x => g x * Ω x) =ᵐ[ν] H := by
    filter_upwards [hΩ_pos] with x hx
    have hne : Ω x ≠ 0 := hx.ne'
    show H x / Ω x * Ω x = H x
    field_simp
  -- `g` is square integrable for the ground measure, by the `W`-norm identity
  have hg_memLp : MemLp g 2 (groundMeasure ν Ω) := by
    have hmsr : AEStronglyMeasurable g (groundMeasure ν Ω) := hg_meas.aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq hmsr]
    refine ⟨hmsr.pow 2, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun x => sq_nonneg _))]
    rw [lintegral_sq_groundMeasure_eq ν Ω hΩ_meas g]
    have hlt : ∫⁻ x, ENNReal.ofReal (H x ^ 2) ∂ν < ⊤ := by
      have hint : Integrable (fun x => (⇑h : S → ℝ) x ^ 2) ν := (Lp.memLp h).integrable_sq
      have hfin := hint.hasFiniteIntegral
      rw [hasFiniteIntegral_iff_ofReal
        (Filter.Eventually.of_forall (fun x => sq_nonneg _))] at hfin
      refine lt_of_le_of_lt (le_of_eq ?_) hfin
      exact lintegral_congr_ae (by filter_upwards [hH_ae] with x hx; rw [hx])
    refine lt_of_le_of_lt (le_of_eq ?_) hlt
    exact lintegral_congr_ae (by filter_upwards [hgΩ] with x hx; rw [hx])
  refine ⟨hg_memLp.toLp g, ?_⟩
  -- identify `W (h/Ω)` with `h`
  have hdens_meas : Measurable (fun x => ENNReal.ofReal (Ω x ^ 2)) :=
    ENNReal.measurable_ofReal.comp (hΩ_meas.pow_const 2)
  have hmk_ground : (fun x => (Lp.aestronglyMeasurable (hg_memLp.toLp g)).mk
        (hg_memLp.toLp g) x) =ᵐ[groundMeasure ν Ω] g := by
    filter_upwards [(Lp.aestronglyMeasurable (hg_memLp.toLp g)).ae_eq_mk.symm,
      hg_memLp.coeFn_toLp] with x hmk hco
    rw [hmk]
    exact hco
  have hmk_nu := (ae_withDensity_iff hdens_meas).1 hmk_ground
  refine Lp.ext ?_
  filter_upwards [groundIsometry_coeFn hΩ_meas (hg_memLp.toLp g), hmk_nu, hgΩ, hH_ae,
    hΩ_pos] with x hW hmk hgx hHx hpos
  have hΩne : ENNReal.ofReal (Ω x ^ 2) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (pow_pos hpos 2)).ne'
  rw [hW, hmk hΩne, hgx]
  exact hHx.symm

/-! ## Consequences for the ground semigroup -/

namespace GroundSemigroupData

variable {ν : Measure S} (D : GroundSemigroupData ν)

/-- `W` is surjective, because the packaged ground state is a.e. strictly
positive (`GroundSemigroupData.Ω_pos_ae`). -/
theorem W_surjective : Function.Surjective D.W :=
  groundIsometry_surjective D.Ω_meas D.Ω_pos_ae

/-- **`W W† = 1`.**  `W† W = 1` already holds for any isometry
(`WAdjoint_W`); with `Ω > 0` a.e. the isometry is onto, so the adjoint is a
two-sided inverse.  This is the "upgrade `W` to the usual unitary ground-state
transform" step of the GNS discharge plan. -/
theorem W_apply_WAdjoint (y : Lp ℝ 2 ν) : D.W (D.WAdjoint y) = y := by
  obtain ⟨x, rfl⟩ := D.W_surjective y
  rw [D.WAdjoint_W x]

/-- **Ground-semigroup intertwining** `W ∘ U_t = T̂ᵗ ∘ W`.

With `W` unitary this is immediate: `U_t = W† T̂ᵗ W`, so
`W U_t = (W W†) T̂ᵗ W = T̂ᵗ W`.  This is the abstract form of the former
pphi2-side analytic obligation `asymGroundSemigroup_intertwines`. -/
theorem groundIsometry_groundSemigroup (t : ℕ) (f : Lp ℝ 2 D.μΩ) :
    groundIsometry D.Ω_meas (D.groundSemigroup t f)
      = (D.normalizedTransfer ^ t) (groundIsometry D.Ω_meas f) :=
  D.W_apply_WAdjoint ((D.normalizedTransfer ^ t) (D.W f))

end GroundSemigroupData

end ReflectionPositivity
