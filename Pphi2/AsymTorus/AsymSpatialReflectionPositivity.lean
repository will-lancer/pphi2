/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Pphi2.AsymTorus.AsymReflectionPositivity

/-!
# Spatial link-reflection data on the asymmetric torus

This module supplies the action-level adapter for a reflection through spatial
bonds. The spatial period is written `2 * M`; the temporal period remains the
independent parameter `Nt`. The half-field is indexed by `ZMod Nt × Fin M` and
is transported to the existing temporal-link adapter by swapping coordinates.

The half action reuses `asymLinkEPos` after this coordinate swap. Its density
has the same `a² Q_mass` normalization as the temporal construction. The two
spatial crossing layers have coupling `J = 1` after the `a² · a⁻²` cancellation.
This file stops at the reflection-data and crossing-energy interface. The
generic reflection-positivity theorem can consume this data once the density
transport to the interacting coordinate measure is supplied.
-/

noncomputable section

open MeasureTheory GaussianField
open scoped BigOperators ENNReal

namespace Pphi2

variable (Nt M : ℕ) [NeZero Nt] [NeZero M]

/-- One spatial half of `ZMod Nt × ZMod (2 * M)`. -/
abbrev AsymSpatialHalfSites (Nt M : ℕ) := ZMod Nt × Fin M

/-- Spatial link reflection, acting trivially on the temporal coordinate. -/
def asymSpatialReflectionSite :
    AsymLatticeSites Nt (2 * M) → AsymLatticeSites Nt (2 * M)
  | (t, x) => (t, -1 - x)

/-- Positive spatial half, with spatial indices `0, ..., M - 1`. -/
def asymSpatialPositiveSite :
    AsymSpatialHalfSites Nt M → AsymLatticeSites Nt (2 * M)
  | (t, x) => (t, (x : ZMod (2 * M)))

/-- Negative spatial half paired with `asymSpatialPositiveSite`. -/
def asymSpatialNegativeSite :
    AsymSpatialHalfSites Nt M → AsymLatticeSites Nt (2 * M)
  | (t, x) => (t, -1 - (x : ZMod (2 * M)))

@[simp] theorem asymSpatialReflectionSite_involutive
    (x : AsymLatticeSites Nt (2 * M)) :
    asymSpatialReflectionSite Nt M (asymSpatialReflectionSite Nt M x) = x := by
  rcases x with ⟨t, s⟩
  ext <;> simp [asymSpatialReflectionSite]

@[simp] theorem asymSpatialPositiveSite_val (t : ZMod Nt) (x : Fin M) :
    (asymSpatialPositiveSite Nt M (t, x)).2.val = x := by
  have hlt : (x : ℕ) < 2 * M := by
    omega
  simpa [asymSpatialPositiveSite] using (ZMod.val_natCast_of_lt hlt :
    (((x : ℕ) : ZMod (2 * M))).val = x)

@[simp] theorem asymSpatialNegativeSite_val (t : ZMod Nt) (x : Fin M) :
    (asymSpatialNegativeSite Nt M (t, x)).2.val = 2 * M - 1 - x := by
  have hle : (x : ℕ) + 1 ≤ 2 * M := by
    omega
  have hcast :
      (((2 * M - 1 - (x : ℕ) : ℕ) : ZMod (2 * M))) =
        (-1 - (x : ZMod (2 * M))) := by
    have hEqNat : (2 * M - 1 - (x : ℕ) : ℕ) = 2 * M - ((x : ℕ) + 1) := by
      omega
    rw [hEqNat, Nat.cast_sub hle, ZMod.natCast_self, zero_sub]
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hlt : (2 * M - 1 - (x : ℕ) : ℕ) < 2 * M := by
    omega
  change (-1 - (x : ZMod (2 * M))).val = 2 * M - 1 - x
  rw [← hcast, ZMod.val_natCast_of_lt hlt]

@[simp] theorem asymSpatialReflectionSite_positive
    (i : AsymSpatialHalfSites Nt M) :
    asymSpatialReflectionSite Nt M (asymSpatialPositiveSite Nt M i) =
      asymSpatialNegativeSite Nt M i := by
  rcases i with ⟨t, x⟩
  ext <;> simp [asymSpatialReflectionSite, asymSpatialPositiveSite,
    asymSpatialNegativeSite]

@[simp] theorem asymSpatialReflectionSite_negative
    (i : AsymSpatialHalfSites Nt M) :
    asymSpatialReflectionSite Nt M (asymSpatialNegativeSite Nt M i) =
      asymSpatialPositiveSite Nt M i := by
  rcases i with ⟨t, x⟩
  ext <;> simp [asymSpatialReflectionSite, asymSpatialPositiveSite,
    asymSpatialNegativeSite]

/-! ## The block equivalence -/

/-- The spatial block map, obtained from the existing temporal block map by
swapping the two coordinates. -/
noncomputable def asymSpatialSiteEquiv :
    Sum (AsymSpatialHalfSites Nt M) (AsymSpatialHalfSites Nt M) ≃
      AsymLatticeSites Nt (2 * M) :=
  (Equiv.sumCongr (Equiv.prodComm (ZMod Nt) (Fin M))
      (Equiv.prodComm (ZMod Nt) (Fin M))).trans
    ((asymLinkSiteEquiv M Nt).trans
      (Equiv.prodComm (ZMod (2 * M)) (ZMod Nt)))

@[simp] theorem asymSpatialSiteEquiv_apply_inl
    (i : AsymSpatialHalfSites Nt M) :
    asymSpatialSiteEquiv Nt M (Sum.inl i) = asymSpatialPositiveSite Nt M i := by
  rcases i with ⟨t, x⟩
  simp [asymSpatialSiteEquiv, asymSpatialPositiveSite, asymLinkPositiveSite]

@[simp] theorem asymSpatialSiteEquiv_apply_inr
    (i : AsymSpatialHalfSites Nt M) :
    asymSpatialSiteEquiv Nt M (Sum.inr i) = asymSpatialNegativeSite Nt M i := by
  rcases i with ⟨t, x⟩
  simp [asymSpatialSiteEquiv, asymSpatialNegativeSite, asymLinkNegativeSite]

@[simp] theorem asymSpatialSiteEquiv_symm_apply_positive
    (i : AsymSpatialHalfSites Nt M) :
    (asymSpatialSiteEquiv Nt M).symm (asymSpatialPositiveSite Nt M i) = Sum.inl i := by
  simpa using (asymSpatialSiteEquiv Nt M).left_inv (Sum.inl i)

@[simp] theorem asymSpatialSiteEquiv_symm_apply_negative
    (i : AsymSpatialHalfSites Nt M) :
    (asymSpatialSiteEquiv Nt M).symm (asymSpatialNegativeSite Nt M i) = Sum.inr i := by
  simpa using (asymSpatialSiteEquiv Nt M).left_inv (Sum.inr i)

/-! ## Field and half-action transports -/

noncomputable def asymSpatialFieldMeasurableEquiv :
    MeasureTheory.Measure.EvenConfig (AsymSpatialHalfSites Nt M) ≃ᵐ
      AsymLatticeField Nt (2 * M) :=
  MeasurableEquiv.arrowCongr' (asymSpatialSiteEquiv Nt M)
    (MeasurableEquiv.refl ℝ)

@[simp] theorem asymSpatialFieldMeasurableEquiv_apply
    (φ : MeasureTheory.Measure.EvenConfig (AsymSpatialHalfSites Nt M))
    (x : AsymLatticeSites Nt (2 * M)) :
    asymSpatialFieldMeasurableEquiv Nt M φ x =
      φ ((asymSpatialSiteEquiv Nt M).symm x) := by
  rfl

@[simp] theorem asymSpatialFieldMeasurableEquiv_symm_apply
    (φ : AsymLatticeField Nt (2 * M))
    (x : Sum (AsymSpatialHalfSites Nt M) (AsymSpatialHalfSites Nt M)) :
    (asymSpatialFieldMeasurableEquiv Nt M).symm φ x =
      φ (asymSpatialSiteEquiv Nt M x) := by
  rfl

theorem measurePreserving_asymSpatialFieldMeasurableEquiv :
    MeasurePreserving (asymSpatialFieldMeasurableEquiv Nt M)
      (volume : Measure (MeasureTheory.Measure.EvenConfig (AsymSpatialHalfSites Nt M)))
      (volume : Measure (AsymLatticeField Nt (2 * M))) := by
  unfold asymSpatialFieldMeasurableEquiv
  simpa [MeasureTheory.Measure.EvenConfig] using
    (volume_preserving_arrowCongr' (asymSpatialSiteEquiv Nt M)
      (MeasurableEquiv.refl ℝ) (MeasurePreserving.id (volume : Measure ℝ)))

/-- Reflection of a coordinate field through spatial bonds. -/
def asymSpatialReflectionField :
    AsymLatticeField Nt (2 * M) → AsymLatticeField Nt (2 * M) :=
  fun φ => φ ∘ asymSpatialReflectionSite Nt M

@[simp] theorem asymSpatialReflectionField_eq_evenTheta
    (φ : MeasureTheory.Measure.EvenConfig (AsymSpatialHalfSites Nt M)) :
    asymSpatialReflectionField Nt M (asymSpatialFieldMeasurableEquiv Nt M φ) =
      asymSpatialFieldMeasurableEquiv Nt M (MeasureTheory.Measure.evenTheta φ) := by
  ext x
  cases h : (asymSpatialSiteEquiv Nt M).symm x with
  | inl i =>
    have hx : asymSpatialPositiveSite Nt M i = x := by
      simpa [h] using (asymSpatialSiteEquiv Nt M).apply_symm_apply x
    rw [← hx, asymSpatialFieldMeasurableEquiv_apply, asymSpatialReflectionField,
      Function.comp_apply, asymSpatialReflectionSite_positive,
      asymSpatialFieldMeasurableEquiv_apply,
      asymSpatialSiteEquiv_symm_apply_negative, MeasureTheory.Measure.evenTheta]
    simpa [MeasureTheory.Measure.evenReflection]
  | inr i =>
    have hx : asymSpatialNegativeSite Nt M i = x := by
      simpa [h] using (asymSpatialSiteEquiv Nt M).apply_symm_apply x
    rw [← hx, asymSpatialFieldMeasurableEquiv_apply, asymSpatialReflectionField,
      Function.comp_apply, asymSpatialReflectionSite_negative,
      asymSpatialFieldMeasurableEquiv_apply,
      asymSpatialSiteEquiv_symm_apply_positive, MeasureTheory.Measure.evenTheta]
    simpa [MeasureTheory.Measure.evenReflection]

/-! ## Configuration-level reflection -/

def asymSpatialReflectionConfig :
    Configuration (AsymLatticeField Nt (2 * M)) →
      Configuration (AsymLatticeField Nt (2 * M)) :=
  fun ω => evalMapAsymInv Nt (2 * M)
    (asymSpatialReflectionField Nt M (evalMapAsym Nt (2 * M) ω))

@[simp] theorem asymSpatialReflectionConfig_evalMap
    (ω : Configuration (AsymLatticeField Nt (2 * M))) :
    evalMapAsym Nt (2 * M) (asymSpatialReflectionConfig Nt M ω) =
      asymSpatialReflectionField Nt M (evalMapAsym Nt (2 * M) ω) := by
  simpa [asymSpatialReflectionConfig] using
    (evalMap_evalMapInvAsym Nt (2 * M)
      (asymSpatialReflectionField Nt M (evalMapAsym Nt (2 * M) ω)))

@[simp] theorem asymSpatialReflectionConfig_involutive
    (ω : Configuration (AsymLatticeField Nt (2 * M))) :
    asymSpatialReflectionConfig Nt M (asymSpatialReflectionConfig Nt M ω) = ω := by
  apply (evalMapAsymMeasurableEquiv Nt (2 * M)).injective
  change evalMapAsym Nt (2 * M)
      (asymSpatialReflectionConfig Nt M (asymSpatialReflectionConfig Nt M ω)) =
    evalMapAsym Nt (2 * M) ω
  rw [asymSpatialReflectionConfig_evalMap, asymSpatialReflectionConfig_evalMap]
  ext x
  simp [asymSpatialReflectionField, asymSpatialReflectionSite_involutive]

def asymSpatialPositivePart :
    AsymLatticeField Nt (2 * M) → AsymSpatialHalfSites Nt M → ℝ :=
  fun φ => MeasureTheory.Measure.positivePart
    ((asymSpatialFieldMeasurableEquiv Nt M).symm φ)

@[simp] theorem asymSpatialPositivePart_apply
    (φ : AsymLatticeField Nt (2 * M)) (i : AsymSpatialHalfSites Nt M) :
    asymSpatialPositivePart Nt M φ i = φ (asymSpatialPositiveSite Nt M i) := by
  simp [asymSpatialPositivePart, MeasureTheory.Measure.positivePart]

def asymSpatialPositivePartConfig :
    Configuration (AsymLatticeField Nt (2 * M)) →
      AsymSpatialHalfSites Nt M → ℝ :=
  asymSpatialPositivePart Nt M ∘ evalMapAsym Nt (2 * M)

@[reducible] def asymSpatialMPos :
    MeasurableSpace (Configuration (AsymLatticeField Nt (2 * M))) :=
  MeasurableSpace.comap (asymSpatialPositivePartConfig Nt M) inferInstance

/-- Swap a spatial-half field into the half-field orientation used by the
existing temporal adapter. -/
noncomputable def asymSpatialHalfSwapMeasurableEquiv :
    (AsymSpatialHalfSites Nt M → ℝ) ≃ᵐ (AsymHalfSites M Nt → ℝ) :=
  MeasurableEquiv.arrowCongr' (Equiv.prodComm (ZMod Nt) (Fin M))
    (MeasurableEquiv.refl ℝ)

@[simp] theorem asymSpatialHalfSwapMeasurableEquiv_apply
    (ψ : AsymSpatialHalfSites Nt M → ℝ) (i : AsymHalfSites M Nt) :
    asymSpatialHalfSwapMeasurableEquiv Nt M ψ i = ψ (i.2, i.1) := by
  rfl

/-- Half action for the spatial link reflection. The coordinate swap makes
the existing `a² Q_mass`-normalized temporal half action applicable. -/
def asymSpatialEPos (P : InteractionPolynomial) (a mass : ℝ)
    (ψ : AsymSpatialHalfSites Nt M → ℝ) : ℝ :=
  asymLinkEPos M Nt P a mass (asymSpatialHalfSwapMeasurableEquiv Nt M ψ)

theorem measurable_asymSpatialEPos
    (P : InteractionPolynomial) (a mass : ℝ) :
    Measurable (asymSpatialEPos Nt M P a mass) :=
  (measurable_asymLinkEPos (M := M) (Ns := Nt) P a mass).comp
    (asymSpatialHalfSwapMeasurableEquiv Nt M).measurable

theorem exp_neg_asymSpatialEPos
    (P : InteractionPolynomial) (a mass : ℝ)
    (ψ : AsymSpatialHalfSites Nt M → ℝ) :
    Real.exp (-(asymSpatialEPos Nt M P a mass ψ)) =
      asymHalfDensityFactor M Nt P a mass
        (asymSpatialHalfSwapMeasurableEquiv Nt M ψ) := by
  simpa [asymSpatialEPos] using
    (exp_neg_asymLinkEPos (M := M) (Ns := Nt) P a mass
      (asymSpatialHalfSwapMeasurableEquiv Nt M ψ))

/-! ## Crossing layers and the focused PF-028 target -/

/-- The spatial crossing coupling. -/
def asymSpatialJ (i : AsymSpatialHalfSites Nt M) : ℝ :=
  (if i.2 = 0 then 1 else 0) +
    (if i.2 = asymHalfLastTime M then 1 else 0)

/-- Spatial crossing layers, one at each bond-reflection boundary. -/
def asymSpatialEdges : Finset (AsymSpatialHalfSites Nt M) :=
  Finset.univ.filter (fun i => asymSpatialJ (Nt := Nt) (M := M) i ≠ 0)

/-- Generic two-block reflection data for the spatial link reflection. -/
def asymSpatialReflectionData (P : InteractionPolynomial) (a mass : ℝ) :
    MeasureTheory.Measure.EvenFerroReflectionData (AsymSpatialHalfSites Nt M) where
  EPos := asymSpatialEPos Nt M P a mass
  measurable_EPos := measurable_asymSpatialEPos Nt M P a mass
  edges := asymSpatialEdges Nt M
  J := asymSpatialJ (Nt := Nt) (M := M)
  hJ := by
    intro i hi
    unfold asymSpatialJ
    split_ifs <;> norm_num

/-- The generic Hubbard--Stratonovich theorem applies to the spatial block
data. Transport to `interactingLatticeMeasureAsym` remains a separate density
bridge. -/
theorem asymSpatialReflectionData_isReflectionPositive
    (P : InteractionPolynomial) (a mass : ℝ) :
    MeasureTheory.Measure.IsReflectionPositive
      (asymSpatialReflectionData (Nt := Nt) (M := M) P a mass).μ
      (asymSpatialReflectionData (Nt := Nt) (M := M) P a mass).θ
      (asymSpatialReflectionData (Nt := Nt) (M := M) P a mass).mPos := by
  exact MeasureTheory.Measure.isReflectionPositive_of_evenNearestNeighbour_unconditional
    (asymSpatialReflectionData (Nt := Nt) (M := M) P a mass)

/-- The spatial crossing energy has coefficient one at both boundary layers.
This is the action-level PF-028 normalization target. -/
theorem asymSpatial_crossingEnergy_eq
    (P : InteractionPolynomial) (a mass : ℝ)
    (φ ψ : AsymSpatialHalfSites Nt M → ℝ) :
    MeasureTheory.Measure.EvenFerroReflectionData.crossingEnergy
      (asymSpatialReflectionData (Nt := Nt) (M := M) P a mass) φ ψ =
      (∑ t : ZMod Nt, φ (t, (0 : Fin M)) * ψ (t, (0 : Fin M))) +
        ∑ t : ZMod Nt,
          φ (t, asymHalfLastTime M) * ψ (t, asymHalfLastTime M) := by
  classical
  unfold MeasureTheory.Measure.EvenFerroReflectionData.crossingEnergy
    asymSpatialReflectionData asymSpatialEdges
  rw [Finset.sum_filter]
  change
    (∑ i : AsymSpatialHalfSites Nt M,
      if asymSpatialJ (Nt := Nt) (M := M) i ≠ 0 then
        asymSpatialJ (Nt := Nt) (M := M) i * φ i * ψ i
      else 0) = _
  have hterm :
      ∀ i : AsymSpatialHalfSites Nt M,
        (if asymSpatialJ (Nt := Nt) (M := M) i ≠ 0 then
            asymSpatialJ (Nt := Nt) (M := M) i * φ i * ψ i
          else 0) =
          (if i.2 = 0 then φ i * ψ i else 0) +
            (if i.2 = asymHalfLastTime M then φ i * ψ i else 0) := by
    intro i
    rcases i with ⟨t, s⟩
    by_cases h0 : s = 0 <;>
      by_cases hlast : s = asymHalfLastTime M <;>
        simp [asymSpatialJ, h0, hlast] <;>
        split_ifs at * <;> norm_num at * <;> ring_nf
  simp_rw [hterm, Finset.sum_add_distrib]
  rw [Fintype.sum_prod_type]
  have hzero :
      (∑ t : ZMod Nt, ∑ s : Fin M,
        (if s = 0 then φ (t, s) * ψ (t, s) else (0 : ℝ))) =
        ∑ t : ZMod Nt, φ (t, (0 : Fin M)) * ψ (t, (0 : Fin M)) := by
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [Finset.sum_eq_single 0]
    · simp
    · intro s hs hne
      simp [hne]
    · intro hmem
      simpa using hmem
  have hlast :
      (∑ t : ZMod Nt, ∑ s : Fin M,
        (if s = asymHalfLastTime M then φ (t, s) * ψ (t, s) else (0 : ℝ))) =
        ∑ t : ZMod Nt,
          φ (t, asymHalfLastTime M) * ψ (t, asymHalfLastTime M) := by
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [Finset.sum_eq_single (asymHalfLastTime M)]
    · simp
    · intro s hs hne
      simp [hne]
    · intro hmem
      simpa using hmem
  rw [hzero, hlast]

end Pphi2
