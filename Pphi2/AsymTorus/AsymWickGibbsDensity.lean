/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.AsymTorus.AsymCoordinateDensity
import Pphi2.AsymTorus.AsymEnergyFactorization

/-!
# Ferromagnetic coordinate density for the asymmetric Wick lattice measure

This file rewrites the finite asymmetric lattice action as a nearest-neighbour
ferromagnetic Gibbs density. The bond sums retain their two direction labels,
including self-bonds and multiplicities on one-site periodic directions.
-/

noncomputable section

open MeasureTheory GaussianField
open scoped BigOperators ENNReal

namespace Pphi2

variable (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]

local notation "e1" => ((1 : ZMod Nt), (0 : ZMod Ns))
local notation "e2" => ((0 : ZMod Nt), (1 : ZMod Ns))

/-- The on-site part of the coordinate Gibbs exponent. -/
def asymWickSitePotential (P : InteractionPolynomial) (a mass τ : ℝ) : ℝ :=
  (2 + (a ^ 2 / 2) * mass ^ 2) * τ ^ 2 +
    a ^ 2 * wickPolynomial P (wickConstantAsym Nt Ns a mass) τ

/-- The two labeled positive nearest-neighbour pair couplings. -/
def asymWickBondEnergy (φ : AsymLatticeField Nt Ns) : ℝ :=
  (∑ x, φ x * φ (x + e1)) + ∑ x, φ x * φ (x + e2)

/-- Coordinate exponent in ferromagnetic bond-minus-site form. -/
def asymWickGibbsExponent (P : InteractionPolynomial) (a mass : ℝ)
    (φ : AsymLatticeField Nt Ns) : ℝ :=
  asymWickBondEnergy Nt Ns φ -
    ∑ x, asymWickSitePotential Nt Ns P a mass (φ x)

/-- Unnormalized ferromagnetic coordinate density. -/
def asymWickGibbsDensity (P : InteractionPolynomial) (a mass : ℝ)
    (φ : AsymLatticeField Nt Ns) : ℝ :=
  Real.exp (asymWickGibbsExponent Nt Ns P a mass φ)

/-- The one-site factor in the product form of the density. -/
def asymWickSiteWeight (P : InteractionPolynomial) (a mass τ : ℝ) : ℝ :=
  Real.exp (-(asymWickSitePotential Nt Ns P a mass τ))

theorem asymWickSitePotential_neg (P : InteractionPolynomial) (a mass τ : ℝ) :
    asymWickSitePotential Nt Ns P a mass (-τ) =
      asymWickSitePotential Nt Ns P a mass τ := by
  unfold asymWickSitePotential
  rw [wickPolynomial_neg]
  ring

/-- The bond-minus-site exponent is the negative Gaussian and Wick action. -/
theorem asymWickGibbsExponent_eq_neg_action
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a)
    (φ : AsymLatticeField Nt Ns) :
    asymWickGibbsExponent Nt Ns P a mass φ =
      -((a ^ 2 / 2) *
          ∑ x, φ x * (massOperatorAsym Nt Ns a mass φ) x +
        a ^ 2 * ∑ x,
          wickPolynomial P (wickConstantAsym Nt Ns a mass) (φ x)) := by
  classical
  have hcross : ∀ v : AsymLatticeSites Nt Ns,
      -(1 / 2 : ℝ) * ∑ x, (φ (x + v) - φ x) ^ 2 =
        ∑ x, φ x * φ (x + v) - ∑ x, φ x ^ 2 := by
    intro v
    have h := asym_sbp_direction φ v
    have hshift :
        ∑ x, φ x * φ (x - v) = ∑ x, φ (x + v) * φ x := by
      rw [← Equiv.sum_comp (Equiv.addRight v)
        (fun x => φ x * φ (x - v))]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      simp only [Equiv.coe_addRight, add_sub_cancel_right]
    have hback :
        ∑ x, φ x * φ (x - v) = ∑ x, φ x * φ (x + v) := by
      calc
        ∑ x, φ x * φ (x - v) = ∑ x, φ (x + v) * φ x := hshift
        _ = ∑ x, φ x * φ (x + v) :=
          Finset.sum_congr rfl (fun x _ => mul_comm _ _)
    have hexpand :
        ∑ x, φ x * (φ (x + v) + φ (x - v) - 2 * φ x) =
          (∑ x, φ x * φ (x + v)) +
          (∑ x, φ x * φ (x - v)) +
          (-2) * ∑ x, φ x ^ 2 := by
      have hx : ∀ x,
          φ x * (φ (x + v) + φ (x - v) - 2 * φ x) =
            φ x * φ (x + v) + φ x * φ (x - v) +
              (-2) * φ x ^ 2 := by
        intro x
        ring
      simp_rw [hx, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hexpand, hback] at h
    linear_combination (-1 / 2 : ℝ) * h
  have hcancel : a ^ 2 * a⁻¹ ^ 2 = 1 := by
    rw [inv_pow]
    exact mul_inv_cancel₀ (pow_ne_zero 2 (ne_of_gt ha))
  have hkin (v : AsymLatticeSites Nt Ns) :
      -(a ^ 2 / 2) *
          (a⁻¹ ^ 2 * ∑ x, (φ (x + v) - φ x) ^ 2) =
        ∑ x, φ x * φ (x + v) - ∑ x, φ x ^ 2 := by
    calc
      -(a ^ 2 / 2) *
            (a⁻¹ ^ 2 * ∑ x, (φ (x + v) - φ x) ^ 2) =
          (a ^ 2 * a⁻¹ ^ 2) *
            (-(1 / 2 : ℝ) * ∑ x, (φ (x + v) - φ x) ^ 2) := by
              ring
      _ = -(1 / 2 : ℝ) * ∑ x, (φ (x + v) - φ x) ^ 2 := by
        rw [hcancel, one_mul]
      _ = ∑ x, φ x * φ (x + v) - ∑ x, φ x ^ 2 := hcross v
  rw [asymWickGibbsExponent, asymWickBondEnergy,
    asymWickSitePotential, massOperatorAsym_quadratic_form_bonds,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  linear_combination (-1 : ℝ) * hkin e1 + (-1 : ℝ) * hkin e2

/-- The Gaussian coordinate density times the Wick factor is the Gibbs density. -/
theorem gaussianDensityAsym_mul_wickFactor_eq_asymWickGibbsDensity
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a)
    (φ : AsymLatticeField Nt Ns) :
    gaussianDensityAsym Nt Ns a mass φ *
        Real.exp (-(a ^ 2 * ∑ x,
          wickPolynomial P (wickConstantAsym Nt Ns a mass) (φ x))) =
      asymWickGibbsDensity Nt Ns P a mass φ := by
  unfold gaussianDensityAsym asymWickGibbsDensity
  rw [← Real.exp_add]
  congr 1
  rw [asymWickGibbsExponent_eq_neg_action Nt Ns P a mass ha φ]
  ring

theorem asymWickGibbsDensity_pos (P : InteractionPolynomial) (a mass : ℝ)
    (φ : AsymLatticeField Nt Ns) :
    0 < asymWickGibbsDensity Nt Ns P a mass φ :=
  Real.exp_pos _

theorem asymWickGibbsDensity_measurable (P : InteractionPolynomial) (a mass : ℝ) :
    Measurable (asymWickGibbsDensity Nt Ns P a mass) := by
  classical
  have hpot : Measurable
      (fun τ : ℝ => asymWickSitePotential Nt Ns P a mass τ) := by
    unfold asymWickSitePotential
    exact
      (measurable_const.mul (measurable_id.pow_const 2)).add
        (measurable_const.mul
          ((wickPolynomial_continuous₂ P).measurable.comp
            (measurable_const.prodMk measurable_id)))
  have hbond : Measurable (asymWickBondEnergy Nt Ns) := by
    unfold asymWickBondEnergy
    apply Measurable.add
    · exact Finset.measurable_sum _ (fun x _ =>
        (measurable_pi_apply x).mul (measurable_pi_apply (x + e1)))
    · exact Finset.measurable_sum _ (fun x _ =>
        (measurable_pi_apply x).mul (measurable_pi_apply (x + e2)))
  have hsite : Measurable (fun φ : AsymLatticeField Nt Ns =>
      ∑ x, asymWickSitePotential Nt Ns P a mass (φ x)) :=
    Finset.measurable_sum _ (fun x _ => hpot.comp (measurable_pi_apply x))
  unfold asymWickGibbsDensity asymWickGibbsExponent
  exact (hbond.sub hsite).exp

/-- Product form with positive pair factors and even one-site factors. -/
theorem asymWickGibbsDensity_eq_bond_site_product
    (P : InteractionPolynomial) (a mass : ℝ)
    (φ : AsymLatticeField Nt Ns) :
    asymWickGibbsDensity Nt Ns P a mass φ =
      (∏ x, Real.exp (φ x * φ (x + e1))) *
      (∏ x, Real.exp (φ x * φ (x + e2))) *
      ∏ x, asymWickSiteWeight Nt Ns P a mass (φ x) := by
  classical
  unfold asymWickGibbsDensity asymWickGibbsExponent
    asymWickBondEnergy asymWickSiteWeight
  have hsplit :
      ((∑ x, φ x * φ (x + e1)) + ∑ x, φ x * φ (x + e2)) -
          ∑ x, asymWickSitePotential Nt Ns P a mass (φ x) =
        (∑ x, φ x * φ (x + e1)) +
        (∑ x, φ x * φ (x + e2)) +
        ∑ x, -(asymWickSitePotential Nt Ns P a mass (φ x)) := by
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    ring
  rw [hsplit, Real.exp_add, Real.exp_add,
    Real.exp_sum, Real.exp_sum, Real.exp_sum]

/-- Lebesgue measure carrying the unnormalized Gibbs density. -/
noncomputable def asymWickGibbsDensityMeasure
    (P : InteractionPolynomial) (a mass : ℝ) :
    Measure (AsymLatticeField Nt Ns) :=
  volume.withDensity (fun φ =>
    ENNReal.ofReal (asymWickGibbsDensity Nt Ns P a mass φ))

/-- Coordinate pushforward of the interacting measure in ferromagnetic density form. -/
theorem interactingLatticeMeasureAsym_evalMapAsym_pushforward_eq_asymWickGibbsDensity
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    (interactingLatticeMeasureAsym Nt Ns P a mass ha hmass).map
        (evalMapAsym Nt Ns) =
      ((ENNReal.ofReal
          (partitionFunctionAsym Nt Ns P a mass ha hmass))⁻¹ *
        (gaussianDensityNormConstAsym Nt Ns a mass)⁻¹) •
      asymWickGibbsDensityMeasure Nt Ns P a mass := by
  rw [interactingLatticeMeasureAsym_evalMapAsym_pushforward_eq_coordinateDensity]
  unfold asymWickGibbsDensityMeasure
  congr 1
  apply withDensity_congr_ae
  filter_upwards with φ
  exact congrArg ENNReal.ofReal
    (gaussianDensityAsym_mul_wickFactor_eq_asymWickGibbsDensity
      Nt Ns P a mass ha φ)

end Pphi2

end
