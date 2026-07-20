/- 
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.AsymTorus.AsymMeasureFactorization
import Pphi2.AsymTorus.AsymWickVariance
import ReflectionPositivity.LatticeInstance

/-!
# Link-reflection positivity on the asymmetric lattice

This file packages the even-time half-lattice geometry for the bond reflection
`(t, x) ↦ (Nt - 1 - t, x)` on `ZMod Nt × ZMod Ns`.
-/

noncomputable section

open MeasureTheory GaussianField
open scoped BigOperators ENNReal

namespace Pphi2

variable (M Ns : ℕ) [NeZero M] [NeZero Ns]

abbrev AsymHalfSites (M Ns : ℕ) := Fin M × ZMod Ns

def asymLinkReflectionSite :
    AsymLatticeSites (2 * M) Ns → AsymLatticeSites (2 * M) Ns
  | (t, x) => (-1 - t, x)

def asymLinkReflectionField :
    AsymLatticeField (2 * M) Ns → AsymLatticeField (2 * M) Ns :=
  fun φ => φ ∘ asymLinkReflectionSite M Ns

def asymLinkPositiveSite :
    AsymHalfSites M Ns → AsymLatticeSites (2 * M) Ns
  | (t, x) => ((t : ZMod (2 * M)), x)

def asymLinkNegativeSite :
    AsymHalfSites M Ns → AsymLatticeSites (2 * M) Ns
  | (t, x) => (-1 - (t : ZMod (2 * M)), x)

@[simp] theorem asymLinkReflectionSite_involutive
    (x : AsymLatticeSites (2 * M) Ns) :
    asymLinkReflectionSite M Ns (asymLinkReflectionSite M Ns x) = x := by
  rcases x with ⟨t, s⟩
  ext <;> simp [asymLinkReflectionSite]

@[simp] theorem asymLinkPositiveSite_val (t : Fin M) (x : ZMod Ns) :
    (asymLinkPositiveSite M Ns (t, x)).1.val = t := by
  have hlt : (t : ℕ) < 2 * M := by
    omega
  simpa [asymLinkPositiveSite] using (ZMod.val_natCast_of_lt hlt :
    (((t : ℕ) : ZMod (2 * M))).val = t)

@[simp] theorem asymLinkNegativeSite_val (t : Fin M) (x : ZMod Ns) :
    (asymLinkNegativeSite M Ns (t, x)).1.val = 2 * M - 1 - t := by
  have hle : (t : ℕ) + 1 ≤ 2 * M := by
    omega
  have hcast :
      (((2 * M - 1 - (t : ℕ) : ℕ) : ZMod (2 * M))) = (-1 - (t : ZMod (2 * M))) := by
    have hEqNat : (2 * M - 1 - (t : ℕ) : ℕ) = 2 * M - ((t : ℕ) + 1) := by
      omega
    rw [hEqNat, Nat.cast_sub hle, ZMod.natCast_self, zero_sub]
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hlt : (2 * M - 1 - (t : ℕ) : ℕ) < 2 * M := by
    omega
  change (-1 - (t : ZMod (2 * M))).val = 2 * M - 1 - t
  rw [← hcast, ZMod.val_natCast_of_lt hlt]

def asymLinkSiteInv :
    AsymLatticeSites (2 * M) Ns → Sum (AsymHalfSites M Ns) (AsymHalfSites M Ns)
  | (t, x) =>
      if ht : t.val < M then
        Sum.inl (⟨⟨t.val, ht⟩, x⟩)
      else
        Sum.inr (⟨⟨2 * M - 1 - t.val, by
          have ht' : M ≤ t.val := le_of_not_gt ht
          have hlt : t.val < 2 * M := ZMod.val_lt t
          omega⟩, x⟩)

noncomputable def asymLinkSiteEquiv :
    Sum (AsymHalfSites M Ns) (AsymHalfSites M Ns) ≃ AsymLatticeSites (2 * M) Ns where
  toFun
    | Sum.inl i => asymLinkPositiveSite M Ns i
    | Sum.inr i => asymLinkNegativeSite M Ns i
  invFun := asymLinkSiteInv M Ns
  left_inv := by
    intro x
    cases x with
    | inl i =>
        rcases i with ⟨t, s⟩
        have ht : (asymLinkPositiveSite M Ns (t, s)).1.val < M := by
          simpa using t.2
        rw [asymLinkSiteInv, dif_pos ht]
        apply congrArg Sum.inl
        ext
        · simpa [asymLinkPositiveSite_val]
        · rfl
    | inr i =>
        rcases i with ⟨t, s⟩
        have hnot : ¬ (asymLinkNegativeSite M Ns (t, s)).1.val < M := by
          rw [asymLinkNegativeSite_val]
          omega
        rw [asymLinkSiteInv, dif_neg hnot]
        apply congrArg Sum.inr
        congr
        · rw [asymLinkNegativeSite_val]
          omega
  right_inv := by
    intro y
    rcases y with ⟨t, s⟩
    by_cases ht : t.val < M
    · simp [asymLinkSiteInv, ht, asymLinkPositiveSite]
    · have hhalf : 2 * M - 1 - t.val < M := by
        have hlt : t.val < 2 * M := ZMod.val_lt t
        omega
      have hneg :
          (-1 - ((2 * M - 1 - t.val : ℕ) : ZMod (2 * M)) : ZMod (2 * M)) = t := by
        have hrew : ((2 * M - 1 - t.val : ℕ) : ZMod (2 * M)) = -1 - t := by
          have hle : t.val + 1 ≤ 2 * M := by
            have hlt : t.val < 2 * M := ZMod.val_lt t
            omega
          have hEqNat : (2 * M - 1 - t.val : ℕ) = 2 * M - (t.val + 1) := by
            omega
          rw [hEqNat, Nat.cast_sub hle, ZMod.natCast_self, zero_sub]
          calc
            (-((t.val + 1 : ℕ) : ZMod (2 * M))) = -((((t.val : ℕ) : ZMod (2 * M)) + 1)) := by
              simp
            _ = -1 - t := by
              rw [ZMod.natCast_zmod_val t]
              ring
        calc
          (-1 - ((2 * M - 1 - t.val : ℕ) : ZMod (2 * M)) : ZMod (2 * M))
              = -1 - (-1 - t) := by rw [hrew]
          _ = t := by simp
      simp [asymLinkSiteInv, ht, asymLinkNegativeSite, hneg]

@[simp] theorem asymLinkSiteEquiv_apply_inl (i : AsymHalfSites M Ns) :
    asymLinkSiteEquiv M Ns (Sum.inl i) = asymLinkPositiveSite M Ns i := rfl

@[simp] theorem asymLinkSiteEquiv_apply_inr (i : AsymHalfSites M Ns) :
    asymLinkSiteEquiv M Ns (Sum.inr i) = asymLinkNegativeSite M Ns i := rfl

@[simp] theorem asymLinkSiteEquiv_symm_apply_positive (i : AsymHalfSites M Ns) :
    (asymLinkSiteEquiv M Ns).symm (asymLinkPositiveSite M Ns i) = Sum.inl i := by
  simpa using (asymLinkSiteEquiv M Ns).left_inv (Sum.inl i)

@[simp] theorem asymLinkSiteEquiv_symm_apply_negative (i : AsymHalfSites M Ns) :
    (asymLinkSiteEquiv M Ns).symm (asymLinkNegativeSite M Ns i) = Sum.inr i := by
  simpa using (asymLinkSiteEquiv M Ns).left_inv (Sum.inr i)

@[simp] theorem asymLinkReflectionSite_positive (i : AsymHalfSites M Ns) :
    asymLinkReflectionSite M Ns (asymLinkPositiveSite M Ns i) = asymLinkNegativeSite M Ns i := by
  rcases i with ⟨t, x⟩
  ext <;> simp [asymLinkReflectionSite, asymLinkPositiveSite, asymLinkNegativeSite]

@[simp] theorem asymLinkReflectionSite_negative (i : AsymHalfSites M Ns) :
    asymLinkReflectionSite M Ns (asymLinkNegativeSite M Ns i) = asymLinkPositiveSite M Ns i := by
  rcases i with ⟨t, x⟩
  ext <;> simp [asymLinkReflectionSite, asymLinkPositiveSite, asymLinkNegativeSite]

noncomputable def asymLinkFieldMeasurableEquiv :
    MeasureTheory.Measure.EvenConfig (AsymHalfSites M Ns) ≃ᵐ AsymLatticeField (2 * M) Ns :=
  MeasurableEquiv.arrowCongr' (asymLinkSiteEquiv M Ns) (MeasurableEquiv.refl ℝ)

@[simp] theorem asymLinkFieldMeasurableEquiv_apply
    (φ : MeasureTheory.Measure.EvenConfig (AsymHalfSites M Ns))
    (x : AsymLatticeSites (2 * M) Ns) :
    asymLinkFieldMeasurableEquiv M Ns φ x = φ ((asymLinkSiteEquiv M Ns).symm x) := by
  rfl

@[simp] theorem asymLinkFieldMeasurableEquiv_symm_apply
    (φ : AsymLatticeField (2 * M) Ns)
    (x : Sum (AsymHalfSites M Ns) (AsymHalfSites M Ns)) :
    (asymLinkFieldMeasurableEquiv M Ns).symm φ x = φ (asymLinkSiteEquiv M Ns x) := by
  rfl

def asymLinkPositivePart :
    AsymLatticeField (2 * M) Ns → AsymHalfSites M Ns → ℝ :=
  fun φ => MeasureTheory.Measure.positivePart ((asymLinkFieldMeasurableEquiv M Ns).symm φ)

@[simp] theorem asymLinkPositivePart_apply
    (φ : AsymLatticeField (2 * M) Ns) (i : AsymHalfSites M Ns) :
    asymLinkPositivePart M Ns φ i = φ (asymLinkPositiveSite M Ns i) := by
  simp [asymLinkPositivePart, MeasureTheory.Measure.positivePart]

def asymLinkPositivePartConfig :
    Configuration (AsymLatticeField (2 * M) Ns) → AsymHalfSites M Ns → ℝ :=
  asymLinkPositivePart M Ns ∘ evalMapAsym (2 * M) Ns

@[reducible] def asymLinkMPosField :
    MeasurableSpace (AsymLatticeField (2 * M) Ns) :=
  MeasurableSpace.comap (asymLinkPositivePart M Ns) inferInstance

@[reducible] def asymLinkMPos :
    MeasurableSpace (Configuration (AsymLatticeField (2 * M) Ns)) :=
  MeasurableSpace.comap (asymLinkPositivePartConfig M Ns) inferInstance

def asymLinkReflectionConfig :
    Configuration (AsymLatticeField (2 * M) Ns) → Configuration (AsymLatticeField (2 * M) Ns) :=
  fun ω => evalMapAsymInv (2 * M) Ns (asymLinkReflectionField M Ns (evalMapAsym (2 * M) Ns ω))

@[simp] theorem asymLinkReflectionConfig_evalMap
    (ω : Configuration (AsymLatticeField (2 * M) Ns)) :
    evalMapAsym (2 * M) Ns (asymLinkReflectionConfig M Ns ω) =
      asymLinkReflectionField M Ns (evalMapAsym (2 * M) Ns ω) := by
  simpa [asymLinkReflectionConfig] using
    (evalMap_evalMapInvAsym (2 * M) Ns
      (asymLinkReflectionField M Ns (evalMapAsym (2 * M) Ns ω)))

@[simp] theorem asymLinkReflectionConfig_involutive
    (ω : Configuration (AsymLatticeField (2 * M) Ns)) :
    asymLinkReflectionConfig M Ns (asymLinkReflectionConfig M Ns ω) = ω := by
  apply (evalMapAsymMeasurableEquiv (2 * M) Ns).injective
  change evalMapAsym (2 * M) Ns
      (asymLinkReflectionConfig M Ns (asymLinkReflectionConfig M Ns ω)) =
    evalMapAsym (2 * M) Ns ω
  rw [asymLinkReflectionConfig_evalMap, asymLinkReflectionConfig_evalMap]
  ext x
  simp [asymLinkReflectionField, asymLinkReflectionSite_involutive]

@[simp] theorem asymLinkReflectionField_eq_evenTheta
    (φ : MeasureTheory.Measure.EvenConfig (AsymHalfSites M Ns)) :
    asymLinkReflectionField M Ns (asymLinkFieldMeasurableEquiv M Ns φ) =
      asymLinkFieldMeasurableEquiv M Ns (MeasureTheory.Measure.evenTheta φ) := by
  ext x
  cases h : (asymLinkSiteEquiv M Ns).symm x with
  | inl i =>
    have hx : asymLinkPositiveSite M Ns i = x := by
      simpa [h] using (asymLinkSiteEquiv M Ns).apply_symm_apply x
    rw [← hx, asymLinkFieldMeasurableEquiv_apply, asymLinkReflectionField, Function.comp_apply,
      asymLinkReflectionSite_positive, asymLinkFieldMeasurableEquiv_apply,
      asymLinkSiteEquiv_symm_apply_negative, MeasureTheory.Measure.evenTheta]
    simpa [MeasureTheory.Measure.evenReflection]
  | inr i =>
    have hx : asymLinkNegativeSite M Ns i = x := by
      simpa [h] using (asymLinkSiteEquiv M Ns).apply_symm_apply x
    rw [← hx, asymLinkFieldMeasurableEquiv_apply, asymLinkReflectionField, Function.comp_apply,
      asymLinkReflectionSite_negative, asymLinkFieldMeasurableEquiv_apply,
      asymLinkSiteEquiv_symm_apply_positive, MeasureTheory.Measure.evenTheta]
    simpa [MeasureTheory.Measure.evenReflection]

theorem measurePreserving_asymLinkFieldMeasurableEquiv :
    MeasurePreserving (asymLinkFieldMeasurableEquiv M Ns)
      (volume : Measure (MeasureTheory.Measure.EvenConfig (AsymHalfSites M Ns)))
      (volume : Measure (AsymLatticeField (2 * M) Ns)) := by
  unfold asymLinkFieldMeasurableEquiv
  simpa [MeasureTheory.Measure.EvenConfig] using
    (volume_preserving_arrowCongr' (asymLinkSiteEquiv M Ns) (MeasurableEquiv.refl ℝ)
      (MeasurePreserving.id (volume : Measure ℝ)))

noncomputable def halfSliceReindexMeasurableEquiv :
    (Fin M → ZMod Ns → ℝ) ≃ᵐ (Fin M → SpatialField Ns) :=
  MeasurableEquiv.arrowCongr' (Equiv.refl (Fin M))
    (MeasurableEquiv.arrowCongr' (ZMod.finEquiv Ns).toEquiv.symm (MeasurableEquiv.refl ℝ))

theorem measurePreserving_halfSliceReindex :
    MeasurePreserving (halfSliceReindexMeasurableEquiv M Ns)
      (volume : Measure (Fin M → ZMod Ns → ℝ))
      (volume : Measure (Fin M → SpatialField Ns)) := by
  unfold halfSliceReindexMeasurableEquiv
  refine volume_preserving_arrowCongr' (Equiv.refl (Fin M)) _ ?_
  exact volume_preserving_arrowCongr' (ZMod.finEquiv Ns).toEquiv.symm
    (MeasurableEquiv.refl ℝ) (MeasurePreserving.id _)

noncomputable def halfSliceMeasurableEquiv :
    (AsymHalfSites M Ns → ℝ) ≃ᵐ (Fin M → SpatialField Ns) :=
  (MeasurableEquiv.curry (Fin M) (ZMod Ns) ℝ).trans
    (halfSliceReindexMeasurableEquiv M Ns)

theorem measurePreserving_halfSliceMeasurableEquiv :
    MeasurePreserving (halfSliceMeasurableEquiv M Ns)
      (volume : Measure (AsymHalfSites M Ns → ℝ))
      (volume : Measure (Fin M → SpatialField Ns)) := by
  unfold halfSliceMeasurableEquiv
  exact (measurePreserving_curry (Fin M) (ZMod Ns)).trans
    (measurePreserving_halfSliceReindex M Ns)

noncomputable def asymLinkPathMeasurableEquiv :
    MeasureTheory.Measure.EvenConfig (AsymHalfSites M Ns) ≃ᵐ
      (ZMod (2 * M) → SpatialField Ns) :=
  (asymLinkFieldMeasurableEquiv M Ns).trans (asymSliceMeasurableEquiv (2 * M) Ns)

theorem measurePreserving_asymLinkPathMeasurableEquiv :
    MeasurePreserving (asymLinkPathMeasurableEquiv M Ns)
      (volume : Measure (MeasureTheory.Measure.EvenConfig (AsymHalfSites M Ns)))
      (volume : Measure (ZMod (2 * M) → SpatialField Ns)) := by
  unfold asymLinkPathMeasurableEquiv
  exact (measurePreserving_asymLinkFieldMeasurableEquiv M Ns).trans
    (measurePreserving_asymSliceEquiv (2 * M) Ns)

def asymLinkPathReflection :
    (ZMod (2 * M) → SpatialField Ns) → (ZMod (2 * M) → SpatialField Ns) :=
  fun ψ t => ψ (-1 - t)

@[simp] theorem asymLinkPathReflection_eq_evenTheta
    (φ : MeasureTheory.Measure.EvenConfig (AsymHalfSites M Ns)) :
    asymLinkPathReflection M Ns (asymLinkPathMeasurableEquiv M Ns φ) =
      asymLinkPathMeasurableEquiv M Ns (MeasureTheory.Measure.evenTheta φ) := by
  ext t x
  have h :=
    congrArg
      (fun ψ : AsymLatticeField (2 * M) Ns => asymSliceEquiv (2 * M) Ns ψ t x)
      (asymLinkReflectionField_eq_evenTheta (M := M) (Ns := Ns) φ)
  simpa [asymLinkPathReflection, asymLinkPathMeasurableEquiv, asymLinkReflectionField,
    asymLinkReflectionSite, asymSliceEquiv_apply] using h

def asymHalfLastTime : Fin M :=
  ⟨M - 1, by
    have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
    exact Nat.sub_lt hM (by decide : 0 < 1)⟩

def asymHalfSlice :
    (AsymHalfSites M Ns → ℝ) → Fin M → SpatialField Ns :=
  halfSliceMeasurableEquiv M Ns

@[simp] theorem asymHalfSlice_apply
    (ψ : AsymHalfSites M Ns → ℝ) (t : Fin M) (x : Fin Ns) :
    asymHalfSlice M Ns ψ t x = ψ (t, (ZMod.finEquiv Ns) x) := by
  rfl

theorem measurable_asymHalfSlice :
    Measurable (asymHalfSlice M Ns) :=
  (halfSliceMeasurableEquiv M Ns).measurable

theorem measurable_asymHalfSlice_time (t : Fin M) :
    Measurable (fun ψ : AsymHalfSites M Ns → ℝ => asymHalfSlice M Ns ψ t) :=
  (measurable_pi_apply t).comp (measurable_asymHalfSlice M Ns)

theorem measurable_asymHalfSlice_apply' (t : Fin M) (x : Fin Ns) :
    Measurable (fun ψ : AsymHalfSites M Ns → ℝ => asymHalfSlice M Ns ψ t x) :=
  (measurable_pi_apply x).comp (measurable_asymHalfSlice_time (M := M) (Ns := Ns) t)

def asymLinkPositiveTime (t : Fin M) : ZMod (2 * M) := t

def asymLinkNegativeTime (t : Fin M) : ZMod (2 * M) := -1 - (t : ZMod (2 * M))

@[simp] theorem asymLinkPositiveTime_val (t : Fin M) :
    (asymLinkPositiveTime M t).val = t.1 := by
  simpa [asymLinkPositiveTime, asymLinkPositiveSite] using
    (asymLinkPositiveSite_val (M := M) (Ns := 1) t (0 : ZMod 1))

@[simp] theorem asymLinkNegativeTime_val (t : Fin M) :
    (asymLinkNegativeTime M t).val = 2 * M - 1 - t.1 := by
  simpa [asymLinkNegativeTime, asymLinkNegativeSite] using
    (asymLinkNegativeSite_val (M := M) (Ns := 1) t (0 : ZMod 1))

def asymLinkTimeInv : ZMod (2 * M) → Sum (Fin M) (Fin M)
  | t =>
      if ht : t.val < M then
        Sum.inl ⟨t.val, ht⟩
      else
        Sum.inr ⟨2 * M - 1 - t.val, by
          have hlt : t.val < 2 * M := ZMod.val_lt t
          omega⟩

noncomputable def asymLinkTimeEquiv : Sum (Fin M) (Fin M) ≃ ZMod (2 * M) where
  toFun
    | Sum.inl t => asymLinkPositiveTime M t
    | Sum.inr t => asymLinkNegativeTime M t
  invFun := asymLinkTimeInv M
  left_inv := by
    intro x
    cases x with
    | inl t =>
        have ht : (asymLinkPositiveTime M t).val < M := by
          simpa using t.2
        rw [asymLinkTimeInv, dif_pos ht]
        apply congrArg Sum.inl
        apply Fin.ext
        change (asymLinkPositiveTime M t).val = t.1
        simp [asymLinkPositiveTime_val]
    | inr t =>
        have hnot : ¬ (asymLinkNegativeTime M t).val < M := by
          rw [asymLinkNegativeTime_val]
          omega
        rw [asymLinkTimeInv, dif_neg hnot]
        apply congrArg Sum.inr
        apply Fin.ext
        change 2 * M - 1 - (asymLinkNegativeTime M t).val = t.1
        rw [asymLinkNegativeTime_val]
        omega
  right_inv := by
    intro t
    by_cases ht : t.val < M
    · simp [asymLinkTimeInv, ht, asymLinkPositiveTime]
    · have hhalf : 2 * M - 1 - t.val < M := by
        have hlt : t.val < 2 * M := ZMod.val_lt t
        omega
      have hneg :
          asymLinkNegativeTime M ⟨2 * M - 1 - t.val, hhalf⟩ = t := by
        have hrew : ((2 * M - 1 - t.val : ℕ) : ZMod (2 * M)) = -1 - t := by
          have hle : t.val + 1 ≤ 2 * M := by
            have hlt : t.val < 2 * M := ZMod.val_lt t
            omega
          have hEqNat : (2 * M - 1 - t.val : ℕ) = 2 * M - (t.val + 1) := by
            omega
          rw [hEqNat, Nat.cast_sub hle, ZMod.natCast_self, zero_sub]
          calc
            (-((t.val + 1 : ℕ) : ZMod (2 * M))) = -((((t.val : ℕ) : ZMod (2 * M)) + 1)) := by
              simp
            _ = -1 - t := by
              rw [ZMod.natCast_zmod_val t]
              ring
        change (-1 - (((⟨2 * M - 1 - t.val, hhalf⟩ : Fin M) : ℕ) : ZMod (2 * M)) : ZMod (2 * M)) = t
        rw [hrew]
        simp
      simp [asymLinkTimeInv, ht, hneg]

@[simp] theorem asymLinkPathMeasurableEquiv_apply_positive
    (φ : MeasureTheory.Measure.EvenConfig (AsymHalfSites M Ns)) (t : Fin M) :
    asymLinkPathMeasurableEquiv M Ns φ (asymLinkPositiveTime M t) =
      asymHalfSlice M Ns (MeasureTheory.Measure.positivePart φ) t := by
  ext x
  rw [show asymLinkPathMeasurableEquiv M Ns φ =
      asymSliceEquiv (2 * M) Ns (asymLinkFieldMeasurableEquiv M Ns φ) by rfl]
  rw [asymSliceEquiv_apply, asymLinkFieldMeasurableEquiv_apply]
  change
    φ ((asymLinkSiteEquiv M Ns).symm
      (asymLinkPositiveSite M Ns (t, (ZMod.finEquiv Ns).toEquiv x))) =
    asymHalfSlice M Ns (MeasureTheory.Measure.positivePart φ) t x
  simp [asymHalfSlice_apply, MeasureTheory.Measure.positivePart,
    asymLinkSiteEquiv_symm_apply_positive]

@[simp] theorem asymLinkPathMeasurableEquiv_apply_negative
    (φ : MeasureTheory.Measure.EvenConfig (AsymHalfSites M Ns)) (t : Fin M) :
    asymLinkPathMeasurableEquiv M Ns φ (asymLinkNegativeTime M t) =
      asymHalfSlice M Ns (MeasureTheory.Measure.negativePart φ) t := by
  ext x
  rw [show asymLinkPathMeasurableEquiv M Ns φ =
      asymSliceEquiv (2 * M) Ns (asymLinkFieldMeasurableEquiv M Ns φ) by rfl]
  rw [asymSliceEquiv_apply, asymLinkFieldMeasurableEquiv_apply]
  change
    φ ((asymLinkSiteEquiv M Ns).symm
      (asymLinkNegativeSite M Ns (t, (ZMod.finEquiv Ns).toEquiv x))) =
    asymHalfSlice M Ns (MeasureTheory.Measure.negativePart φ) t x
  simp [asymHalfSlice_apply, MeasureTheory.Measure.negativePart,
    asymLinkSiteEquiv_symm_apply_negative]

def asymLinkPathPositivePart :
    (ZMod (2 * M) → SpatialField Ns) → AsymHalfSites M Ns → ℝ :=
  MeasureTheory.Measure.positivePart ∘ (asymLinkPathMeasurableEquiv M Ns).symm

@[simp] theorem asymLinkPathPositivePart_apply
    (ψ : ZMod (2 * M) → SpatialField Ns) (i : AsymHalfSites M Ns) :
    asymLinkPathPositivePart M Ns ψ i =
      ψ (asymLinkPositiveTime M i.1) ((ZMod.finEquiv Ns).symm i.2) := by
  rfl

@[reducible] def asymLinkPathMPos :
    MeasurableSpace (ZMod (2 * M) → SpatialField Ns) :=
  MeasurableSpace.comap (asymLinkPathPositivePart M Ns) inferInstance

noncomputable def asymLinkConfigPathMeasurableEquiv :
    Configuration (AsymLatticeField (2 * M) Ns) ≃ᵐ
      (ZMod (2 * M) → SpatialField Ns) :=
  (evalMapAsymMeasurableEquiv (2 * M) Ns).trans (asymSliceMeasurableEquiv (2 * M) Ns)

@[simp] theorem asymLinkConfigPathMeasurableEquiv_apply
    (ω : Configuration (AsymLatticeField (2 * M) Ns)) :
    asymLinkConfigPathMeasurableEquiv M Ns ω =
      asymSliceEquiv (2 * M) Ns (evalMapAsym (2 * M) Ns ω) := by
  rfl

@[simp] theorem asymLinkPathPositivePart_config
    (ω : Configuration (AsymLatticeField (2 * M) Ns)) :
    asymLinkPathPositivePart M Ns (asymLinkConfigPathMeasurableEquiv M Ns ω) =
      asymLinkPositivePartConfig M Ns ω := by
  ext i
  rcases i with ⟨t, x⟩
  simp [asymLinkPositivePartConfig, asymLinkPositivePart_apply,
    asymSliceEquiv_apply, asymLinkPositiveTime, asymLinkPositiveSite]

@[simp] theorem asymLinkConfigPathMeasurableEquiv_reflection
    (ω : Configuration (AsymLatticeField (2 * M) Ns)) :
    asymLinkConfigPathMeasurableEquiv M Ns (asymLinkReflectionConfig M Ns ω) =
      asymLinkPathReflection M Ns (asymLinkConfigPathMeasurableEquiv M Ns ω) := by
  ext t x
  rw [asymLinkConfigPathMeasurableEquiv_apply, asymLinkConfigPathMeasurableEquiv_apply,
    asymLinkReflectionConfig_evalMap]
  simp [asymLinkPathReflection, asymLinkReflectionField, asymLinkReflectionSite,
    asymSliceEquiv_apply]

def asymHalfNormSq (ψ : AsymHalfSites M Ns → ℝ) (t : Fin M) : ℝ :=
  ∑ x : Fin Ns, (asymHalfSlice M Ns ψ t x) ^ 2

theorem measurable_asymHalfNormSq (t : Fin M) :
    Measurable (fun ψ : AsymHalfSites M Ns → ℝ => asymHalfNormSq M Ns ψ t) := by
  unfold asymHalfNormSq
  refine Finset.measurable_sum _ (fun x _ => ?_)
  exact (measurable_asymHalfSlice_apply' (M := M) (Ns := Ns) t x).pow_const 2

def asymHalfInternalLeft (t : Fin (M - 1)) : Fin M :=
  ⟨t.1, lt_of_lt_of_le t.2 (Nat.sub_le M 1)⟩

def asymHalfInternalRight (t : Fin (M - 1)) : Fin M :=
  ⟨t.1 + 1, by
    have ht : t.1 < M - 1 := t.2
    omega⟩

private noncomputable def predSuccFinEquiv : Fin ((M - 1) + 1) ≃ Fin M :=
  finCongr (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne M)))

@[simp] private theorem predSuccFinEquiv_zero :
    predSuccFinEquiv (M := M) 0 = (0 : Fin M) := by
  rfl

@[simp] private theorem predSuccFinEquiv_castSucc (t : Fin (M - 1)) :
    predSuccFinEquiv (M := M) t.castSucc = asymHalfInternalLeft M t := by
  apply Fin.ext
  simp [predSuccFinEquiv, asymHalfInternalLeft]

@[simp] private theorem predSuccFinEquiv_succ (t : Fin (M - 1)) :
    predSuccFinEquiv (M := M) t.succ = asymHalfInternalRight M t := by
  apply Fin.ext
  simp [predSuccFinEquiv, asymHalfInternalRight]

@[simp] private theorem predSuccFinEquiv_last :
    predSuccFinEquiv (M := M) (Fin.last (M - 1)) = asymHalfLastTime M := by
  apply Fin.ext
  simp [predSuccFinEquiv, asymHalfLastTime]

private theorem prod_univ_asymHalfInternalLeft_last {β : Type*} [CommMonoid β]
    (f : Fin M → β) :
    (∏ t : Fin M, f t) =
      (∏ t : Fin (M - 1), f (asymHalfInternalLeft M t)) * f (asymHalfLastTime M) := by
  let e : Fin ((M - 1) + 1) ≃ Fin M := predSuccFinEquiv (M := M)
  calc
    (∏ t : Fin M, f t) = ∏ t : Fin ((M - 1) + 1), f (e t) := by
      exact Fintype.prod_equiv e.symm (fun t : Fin M => f t) (fun t => f (e t))
        (by intro t; simp [e])
    _ = (∏ t : Fin (M - 1), f (e t.castSucc)) * f (e (Fin.last (M - 1))) := by
      simpa using (Fin.prod_univ_castSucc (f := fun t : Fin ((M - 1) + 1) => f (e t))
        (n := M - 1))
    _ = (∏ t : Fin (M - 1), f (asymHalfInternalLeft M t)) * f (asymHalfLastTime M) := by
      simp [e]

private theorem prod_univ_zero_asymHalfInternalRight {β : Type*} [CommMonoid β]
    (f : Fin M → β) :
    (∏ t : Fin M, f t) = f 0 * ∏ t : Fin (M - 1), f (asymHalfInternalRight M t) := by
  let e : Fin ((M - 1) + 1) ≃ Fin M := predSuccFinEquiv (M := M)
  calc
    (∏ t : Fin M, f t) = ∏ t : Fin ((M - 1) + 1), f (e t) := by
      exact Fintype.prod_equiv e.symm (fun t : Fin M => f t) (fun t => f (e t))
        (by intro t; simp [e])
    _ = f (e 0) * ∏ t : Fin (M - 1), f (e t.succ) := by
      simpa using (Fin.prod_univ_succ (f := fun t : Fin ((M - 1) + 1) => f (e t))
        (n := M - 1))
    _ = f 0 * ∏ t : Fin (M - 1), f (asymHalfInternalRight M t) := by
      simp [e]

@[simp] theorem asymLinkPositiveTime_internal_succ (t : Fin (M - 1)) :
    asymLinkPositiveTime M (asymHalfInternalLeft M t) + 1 =
      asymLinkPositiveTime M (asymHalfInternalRight M t) := by
  simp [asymLinkPositiveTime, asymHalfInternalLeft, asymHalfInternalRight]

@[simp] theorem asymLinkNegativeTime_internal_succ (t : Fin (M - 1)) :
    asymLinkNegativeTime M (asymHalfInternalRight M t) + 1 =
      asymLinkNegativeTime M (asymHalfInternalLeft M t) := by
  unfold asymLinkNegativeTime asymHalfInternalLeft asymHalfInternalRight
  simp
  ring

@[simp] theorem asymLinkPositiveTime_last_succ :
    asymLinkPositiveTime M (asymHalfLastTime M) + 1 =
      asymLinkNegativeTime M (asymHalfLastTime M) := by
  change (((M - 1 : ℕ) : ZMod (2 * M)) + 1 =
    asymLinkNegativeTime M (asymHalfLastTime M))
  have hneg :
      asymLinkNegativeTime M (asymHalfLastTime M) = ((M : ℕ) : ZMod (2 * M)) := by
    rw [← ZMod.natCast_zmod_val (asymLinkNegativeTime M (asymHalfLastTime M))]
    rw [asymLinkNegativeTime_val]
    change (((2 * M - 1 - (M - 1) : ℕ) : ZMod (2 * M)) = ((M : ℕ) : ZMod (2 * M)))
    congr
    omega
  rw [hneg]
  have hM : M - 1 + 1 = M := Nat.sub_add_cancel
    (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne M)))
  simpa [Nat.cast_add] using
    congrArg (fun n : ℕ => ((n : ℕ) : ZMod (2 * M))) hM

@[simp] theorem asymLinkNegativeTime_zero_succ :
    asymLinkNegativeTime M (0 : Fin M) + 1 =
      asymLinkPositiveTime M (0 : Fin M) := by
  unfold asymLinkNegativeTime asymLinkPositiveTime
  simp

theorem transferGaussian_sub_split (u v : SpatialField Ns) :
    transferGaussian Ns (u - v) =
      Real.exp (-(1 / 2) * ∑ x : Fin Ns, u x ^ 2) *
        Real.exp (-(1 / 2) * ∑ x : Fin Ns, v x ^ 2) *
          Real.exp (∑ x : Fin Ns, u x * v x) := by
  unfold transferGaussian timeCoupling
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  have hsq :
      ∑ x : Fin Ns, (((0 : SpatialField Ns) x) - (u - v) x) ^ 2 =
        ∑ x : Fin Ns, (u x ^ 2 - 2 * (u x * v x) + v x ^ 2) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    simp
    ring
  rw [hsq]
  set A : ℝ := ∑ x : Fin Ns, u x ^ 2
  set B : ℝ := ∑ x : Fin Ns, u x * v x
  set C : ℝ := ∑ x : Fin Ns, v x ^ 2
  have hsum :
      ∑ x : Fin Ns, (u x ^ 2 - 2 * (u x * v x) + v x ^ 2) = A - 2 * B + C := by
    unfold A B C
    have hpoint :
        (fun x : Fin Ns => u x ^ 2 - 2 * (u x * v x) + v x ^ 2) =
          fun x : Fin Ns => u x ^ 2 + (-2) * (u x * v x) + v x ^ 2 := by
      funext x
      ring
    rw [hpoint]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hpoint2 :
        (fun x : Fin Ns => (-2) * (u x * v x)) = fun x : Fin Ns => -(u x * v x * 2) := by
      funext x
      ring
    rw [hpoint2]
    have hneg :
        ∑ x : Fin Ns, -(u x * v x * 2) = -∑ x : Fin Ns, u x * v x * 2 := by
      simp
    have hmul :
        ∑ x : Fin Ns, u x * v x * 2 = (∑ x : Fin Ns, u x * v x) * 2 := by
      rw [Finset.sum_mul]
    rw [hneg, hmul]
    ring
  rw [hsum]
  ring

def asymHalfInternalPair
    (ψ : AsymHalfSites M Ns → ℝ) (t : Fin (M - 1)) : SpatialField Ns × SpatialField Ns :=
  (asymHalfSlice M Ns ψ (asymHalfInternalLeft M t),
    asymHalfSlice M Ns ψ (asymHalfInternalRight M t))

theorem measurable_asymHalfInternalPair (t : Fin (M - 1)) :
    Measurable (fun ψ : AsymHalfSites M Ns → ℝ =>
      asymHalfInternalPair M Ns ψ t) := by
  have ht :
      Measurable (fun ψ : AsymHalfSites M Ns → ℝ =>
        asymHalfSlice M Ns ψ (asymHalfInternalLeft M t)) :=
    measurable_asymHalfSlice_time (M := M) (Ns := Ns) (asymHalfInternalLeft M t)
  have hs :
      Measurable (fun ψ : AsymHalfSites M Ns → ℝ =>
        asymHalfSlice M Ns ψ (asymHalfInternalRight M t)) :=
    measurable_asymHalfSlice_time (M := M) (Ns := Ns) (asymHalfInternalRight M t)
  exact Measurable.prodMk ht hs

def asymHalfInternalKernelFactor (P : InteractionPolynomial) (a mass : ℝ)
    (ψ : AsymHalfSites M Ns → ℝ) (t : Fin (M - 1)) : ℝ :=
  Function.uncurry (asymTransferKernel (Nt := 2 * M) (Ns := Ns) P a mass)
    (asymHalfInternalPair M Ns ψ t)

theorem measurable_asymHalfInternalKernelFactor
    (P : InteractionPolynomial) (a mass : ℝ) (t : Fin (M - 1)) :
    Measurable (fun ψ : AsymHalfSites M Ns → ℝ =>
      asymHalfInternalKernelFactor M Ns P a mass ψ t) := by
  exact (asymTransferKernel_measurable (Nt := 2 * M) (Ns := Ns) P a mass).comp
    (measurable_asymHalfInternalPair (M := M) (Ns := Ns) t)

theorem asymHalfInternalKernelFactor_pos
    (P : InteractionPolynomial) (a mass : ℝ) (ψ : AsymHalfSites M Ns → ℝ)
    (t : Fin (M - 1)) :
    0 < asymHalfInternalKernelFactor M Ns P a mass ψ t := by
  rw [asymHalfInternalKernelFactor, Function.uncurry, asymTransferKernel]
  exact mul_pos
    (mul_pos
      (asymTransferWeight_pos (Nt := 2 * M) (Ns := Ns) P a mass
        (asymHalfSlice M Ns ψ (asymHalfInternalLeft M t)))
      (transferGaussian_pos Ns
        (asymHalfSlice M Ns ψ (asymHalfInternalLeft M t) -
          asymHalfSlice M Ns ψ (asymHalfInternalRight M t))))
    (asymTransferWeight_pos (Nt := 2 * M) (Ns := Ns) P a mass
      (asymHalfSlice M Ns ψ (asymHalfInternalRight M t)))

def asymHalfDensityFactor (P : InteractionPolynomial) (a mass : ℝ)
    (ψ : AsymHalfSites M Ns → ℝ) : ℝ :=
  asymTransferWeight (Nt := 2 * M) (Ns := Ns) P a mass
      (asymHalfSlice M Ns ψ 0) *
    (∏ t : Fin (M - 1), asymHalfInternalKernelFactor M Ns P a mass ψ t) *
    asymTransferWeight (Nt := 2 * M) (Ns := Ns) P a mass
      (asymHalfSlice M Ns ψ (asymHalfLastTime M)) *
    Real.exp (-(1 / 2) * asymHalfNormSq M Ns ψ 0) *
    Real.exp (-(1 / 2) * asymHalfNormSq M Ns ψ (asymHalfLastTime M))

theorem measurable_asymHalfDensityFactor
    (P : InteractionPolynomial) (a mass : ℝ) :
    Measurable (asymHalfDensityFactor M Ns P a mass) := by
  unfold asymHalfDensityFactor
  have hfirst :
      Measurable (fun ψ : AsymHalfSites M Ns → ℝ =>
        asymTransferWeight (Nt := 2 * M) (Ns := Ns) P a mass (asymHalfSlice M Ns ψ 0)) :=
    (asymTransferWeight_measurable (Nt := 2 * M) (Ns := Ns) P a mass).comp
      (measurable_asymHalfSlice_time (M := M) (Ns := Ns) 0)
  have hlast :
      Measurable (fun ψ : AsymHalfSites M Ns → ℝ =>
        asymTransferWeight (Nt := 2 * M) (Ns := Ns) P a mass
          (asymHalfSlice M Ns ψ (asymHalfLastTime M))) :=
    (asymTransferWeight_measurable (Nt := 2 * M) (Ns := Ns) P a mass).comp
      (measurable_asymHalfSlice_time (M := M) (Ns := Ns) (asymHalfLastTime M))
  have hprod :
      Measurable (fun ψ : AsymHalfSites M Ns → ℝ =>
        ∏ t : Fin (M - 1), asymHalfInternalKernelFactor M Ns P a mass ψ t) := by
    refine Finset.measurable_prod _ (fun t _ => ?_)
    exact measurable_asymHalfInternalKernelFactor (M := M) (Ns := Ns) P a mass t
  have hdiag0 :
      Measurable (fun ψ : AsymHalfSites M Ns → ℝ =>
        Real.exp (-(1 / 2) * asymHalfNormSq M Ns ψ 0)) :=
    (Real.measurable_exp.comp
      (measurable_const.mul (measurable_asymHalfNormSq (M := M) (Ns := Ns) 0)))
  have hdiagl :
      Measurable (fun ψ : AsymHalfSites M Ns → ℝ =>
        Real.exp (-(1 / 2) * asymHalfNormSq M Ns ψ (asymHalfLastTime M))) :=
    (Real.measurable_exp.comp
      (measurable_const.mul
        (measurable_asymHalfNormSq (M := M) (Ns := Ns) (asymHalfLastTime M))))
  exact (((hfirst.mul hprod).mul hlast).mul hdiag0).mul hdiagl

theorem asymHalfDensityFactor_pos
    (P : InteractionPolynomial) (a mass : ℝ) (ψ : AsymHalfSites M Ns → ℝ) :
    0 < asymHalfDensityFactor M Ns P a mass ψ := by
  unfold asymHalfDensityFactor
  refine mul_pos ?_ (Real.exp_pos _)
  refine mul_pos ?_ (Real.exp_pos _)
  refine mul_pos ?_ (asymTransferWeight_pos (Nt := 2 * M) (Ns := Ns) P a mass
    (asymHalfSlice M Ns ψ (asymHalfLastTime M)))
  exact mul_pos
    (asymTransferWeight_pos (Nt := 2 * M) (Ns := Ns) P a mass (asymHalfSlice M Ns ψ 0))
    (Finset.prod_pos fun t _ =>
      asymHalfInternalKernelFactor_pos (M := M) (Ns := Ns) P a mass ψ t)

def asymLinkEPos (P : InteractionPolynomial) (a mass : ℝ)
    (ψ : AsymHalfSites M Ns → ℝ) : ℝ :=
  -Real.log (asymHalfDensityFactor M Ns P a mass ψ)

theorem measurable_asymLinkEPos
    (P : InteractionPolynomial) (a mass : ℝ) :
    Measurable (asymLinkEPos M Ns P a mass) :=
  (Real.measurable_log.comp
    (measurable_asymHalfDensityFactor (M := M) (Ns := Ns) P a mass)).neg

theorem exp_neg_asymLinkEPos
    (P : InteractionPolynomial) (a mass : ℝ) (ψ : AsymHalfSites M Ns → ℝ) :
    Real.exp (-(asymLinkEPos M Ns P a mass ψ)) =
      asymHalfDensityFactor M Ns P a mass ψ := by
  unfold asymLinkEPos
  rw [neg_neg, Real.exp_log (asymHalfDensityFactor_pos (M := M) (Ns := Ns) P a mass ψ)]

def asymLinkJ (i : AsymHalfSites M Ns) : ℝ :=
  (if i.1 = 0 then 1 else 0) + (if i.1 = asymHalfLastTime M then 1 else 0)

def asymLinkEdges : Finset (AsymHalfSites M Ns) :=
  Finset.univ.filter (fun i => asymLinkJ (M := M) (Ns := Ns) i ≠ 0)

def asymLinkReflectionData (P : InteractionPolynomial) (a mass : ℝ) :
    MeasureTheory.Measure.EvenFerroReflectionData (AsymHalfSites M Ns) where
  EPos := asymLinkEPos M Ns P a mass
  measurable_EPos := measurable_asymLinkEPos (M := M) (Ns := Ns) P a mass
  edges := asymLinkEdges M Ns
  J := asymLinkJ (M := M) (Ns := Ns)
  hJ := by
    intro i hi
    unfold asymLinkJ
    split_ifs <;> norm_num

theorem asymLink_crossingEnergy_eq
    (P : InteractionPolynomial) (a mass : ℝ)
    (φ ψ : AsymHalfSites M Ns → ℝ) :
    MeasureTheory.Measure.EvenFerroReflectionData.crossingEnergy
      (asymLinkReflectionData (M := M) (Ns := Ns) P a mass) φ ψ =
      (∑ x : Fin Ns, asymHalfSlice M Ns φ 0 x * asymHalfSlice M Ns ψ 0 x) +
        ∑ x : Fin Ns,
          asymHalfSlice M Ns φ (asymHalfLastTime M) x *
            asymHalfSlice M Ns ψ (asymHalfLastTime M) x := by
  classical
  unfold MeasureTheory.Measure.EvenFerroReflectionData.crossingEnergy asymLinkReflectionData
    asymLinkEdges
  rw [Finset.sum_filter]
  change
    (∑ a_1 : AsymHalfSites M Ns,
      if asymLinkJ (M := M) (Ns := Ns) a_1 ≠ 0 then
        asymLinkJ (M := M) (Ns := Ns) a_1 * φ a_1 * ψ a_1
      else 0) =
      (∑ x : Fin Ns, asymHalfSlice M Ns φ 0 x * asymHalfSlice M Ns ψ 0 x) +
        ∑ x : Fin Ns,
          asymHalfSlice M Ns φ (asymHalfLastTime M) x *
            asymHalfSlice M Ns ψ (asymHalfLastTime M) x
  have hterm :
      ∀ i : AsymHalfSites M Ns,
        (if asymLinkJ (M := M) (Ns := Ns) i ≠ 0 then
            asymLinkJ (M := M) (Ns := Ns) i * φ i * ψ i
          else 0) =
          (if i.1 = 0 then φ i * ψ i else 0) +
            (if i.1 = asymHalfLastTime M then φ i * ψ i else 0) := by
    intro i
    rcases i with ⟨t, s⟩
    by_cases h0 : t = 0 <;> by_cases hlast : t = asymHalfLastTime M <;>
      simp [asymLinkJ, h0, hlast] <;>
      split_ifs at * <;> norm_num at * <;> ring_nf
  simp_rw [hterm]
  rw [Fintype.sum_prod_type]
  have hzero :
      ∑ t : Fin M, ∑ s : ZMod Ns, (if t = 0 then φ (t, s) * ψ (t, s) else (0 : ℝ)) =
        ∑ s : ZMod Ns, φ (0, s) * ψ (0, s) := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro t ht hne
      simp [hne]
    · intro hmem
      simpa using hmem
  have hlast :
      ∑ t : Fin M, ∑ s : ZMod Ns,
          (if t = asymHalfLastTime M then φ (t, s) * ψ (t, s) else (0 : ℝ)) =
        ∑ s : ZMod Ns, φ (asymHalfLastTime M, s) * ψ (asymHalfLastTime M, s) := by
    rw [Finset.sum_eq_single (asymHalfLastTime M)]
    · simp
    · intro t ht hne
      simp [hne]
    · intro hmem
      simpa using hmem
  simp_rw [Finset.sum_add_distrib]
  rw [hzero, hlast]
  rw [← Equiv.sum_comp (ZMod.finEquiv Ns).toEquiv
    (fun s : ZMod Ns => φ (0, s) * ψ (0, s))]
  rw [← Equiv.sum_comp (ZMod.finEquiv Ns).toEquiv
    (fun s : ZMod Ns => φ (asymHalfLastTime M, s) * ψ (asymHalfLastTime M, s))]
  simp [asymHalfSlice_apply]

private theorem asymLink_pathDensity_factorization
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (φ : MeasureTheory.Measure.EvenConfig (AsymHalfSites M Ns)) :
    (asymTransferSystem (Nt := 2 * M) (Ns := Ns) P a mass ha hmass).pathDensity (2 * M)
        (asymLinkPathMeasurableEquiv M Ns φ) =
      (∏ t : Fin (M - 1),
          asymHalfInternalKernelFactor M Ns P a mass
            (MeasureTheory.Measure.positivePart φ) t) *
        asymTransferKernel (Nt := 2 * M) (Ns := Ns) P a mass
          (asymHalfSlice M Ns (MeasureTheory.Measure.positivePart φ) (asymHalfLastTime M))
          (asymHalfSlice M Ns (MeasureTheory.Measure.negativePart φ) (asymHalfLastTime M)) *
        (asymTransferKernel (Nt := 2 * M) (Ns := Ns) P a mass
            (asymHalfSlice M Ns (MeasureTheory.Measure.negativePart φ) 0)
            (asymHalfSlice M Ns (MeasureTheory.Measure.positivePart φ) 0) *
          ∏ t : Fin (M - 1),
            asymHalfInternalKernelFactor M Ns P a mass
              (MeasureTheory.Measure.negativePart φ) t) := by
  let ψ := asymLinkPathMeasurableEquiv M Ns φ
  let fpos : Fin M → ℝ := fun t =>
    asymTransferKernel (Nt := 2 * M) (Ns := Ns) P a mass
      (ψ (asymLinkPositiveTime M t)) (ψ (asymLinkPositiveTime M t + 1))
  let fneg : Fin M → ℝ := fun t =>
    asymTransferKernel (Nt := 2 * M) (Ns := Ns) P a mass
      (ψ (asymLinkNegativeTime M t)) (ψ (asymLinkNegativeTime M t + 1))
  have hsplit :
      (asymTransferSystem (Nt := 2 * M) (Ns := Ns) P a mass ha hmass).pathDensity (2 * M) ψ =
        (∏ s : Sum (Fin M) (Fin M),
          asymTransferKernel (Nt := 2 * M) (Ns := Ns) P a mass
            (ψ (asymLinkTimeEquiv M s)) (ψ (asymLinkTimeEquiv M s + 1))) := by
    change
      (∏ t : ZMod (2 * M),
        asymTransferKernel (Nt := 2 * M) (Ns := Ns) P a mass (ψ t) (ψ (t + 1))) =
      ∏ s : Sum (Fin M) (Fin M),
        asymTransferKernel (Nt := 2 * M) (Ns := Ns) P a mass
          (ψ (asymLinkTimeEquiv M s)) (ψ (asymLinkTimeEquiv M s + 1))
    exact Fintype.prod_equiv (asymLinkTimeEquiv M).symm
      (fun t : ZMod (2 * M) =>
        asymTransferKernel (Nt := 2 * M) (Ns := Ns) P a mass (ψ t) (ψ (t + 1)))
      (fun s : Sum (Fin M) (Fin M) =>
        asymTransferKernel (Nt := 2 * M) (Ns := Ns) P a mass
          (ψ (asymLinkTimeEquiv M s)) (ψ (asymLinkTimeEquiv M s + 1)))
      (by intro t; simp)
  have hpos :
      (∏ t : Fin M, fpos t) =
        (∏ t : Fin (M - 1),
            asymHalfInternalKernelFactor M Ns P a mass
              (MeasureTheory.Measure.positivePart φ) t) *
          asymTransferKernel (Nt := 2 * M) (Ns := Ns) P a mass
            (asymHalfSlice M Ns (MeasureTheory.Measure.positivePart φ) (asymHalfLastTime M))
            (asymHalfSlice M Ns (MeasureTheory.Measure.negativePart φ) (asymHalfLastTime M)) := by
    rw [prod_univ_asymHalfInternalLeft_last (M := M) (f := fpos)]
    dsimp [fpos, ψ]
    congr 1
    · apply Finset.prod_congr rfl
      intro t ht
      simp [asymHalfInternalKernelFactor, asymHalfInternalPair, Function.uncurry,
        asymLinkPositiveTime_internal_succ]
    · simp [asymLinkPositiveTime_last_succ]
  have hneg :
      (∏ t : Fin M, fneg t) =
        asymTransferKernel (Nt := 2 * M) (Ns := Ns) P a mass
          (asymHalfSlice M Ns (MeasureTheory.Measure.negativePart φ) 0)
          (asymHalfSlice M Ns (MeasureTheory.Measure.positivePart φ) 0) *
          ∏ t : Fin (M - 1),
            asymHalfInternalKernelFactor M Ns P a mass
              (MeasureTheory.Measure.negativePart φ) t := by
    rw [prod_univ_zero_asymHalfInternalRight (M := M) (f := fneg)]
    dsimp [fneg, ψ]
    congr 1
    · simp [asymLinkNegativeTime_zero_succ]
    · apply Finset.prod_congr rfl
      intro t ht
      rw [asymTransferKernel_symm (Nt := 2 * M) (Ns := Ns) P a mass]
      simp [asymHalfInternalKernelFactor, asymHalfInternalPair, Function.uncurry,
        asymLinkNegativeTime_internal_succ]
  rw [hsplit, Fintype.prod_sum_type]
  simpa [fpos, fneg] using congrArg₂ (fun x y => x * y) hpos hneg

theorem asymLinkReflectionData_density_eq_pathDensity
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (φ : MeasureTheory.Measure.EvenConfig (AsymHalfSites M Ns)) :
    (asymLinkReflectionData (M := M) (Ns := Ns) P a mass).density φ =
      (asymTransferSystem (Nt := 2 * M) (Ns := Ns) P a mass ha hmass).pathDensity (2 * M)
        (asymLinkPathMeasurableEquiv M Ns φ) := by
  symm
  rw [asymLink_pathDensity_factorization (M := M) (Ns := Ns) P a mass ha hmass φ]
  set φp := MeasureTheory.Measure.positivePart φ
  set φn := MeasureTheory.Measure.negativePart φ
  have hfactor :
      (∏ t : Fin (M - 1), asymHalfInternalKernelFactor M Ns P a mass φp t) *
          asymTransferKernel (Nt := 2 * M) (Ns := Ns) P a mass
            (asymHalfSlice M Ns φp (asymHalfLastTime M))
            (asymHalfSlice M Ns φn (asymHalfLastTime M)) *
          (asymTransferKernel (Nt := 2 * M) (Ns := Ns) P a mass
              (asymHalfSlice M Ns φn 0) (asymHalfSlice M Ns φp 0) *
            ∏ t : Fin (M - 1), asymHalfInternalKernelFactor M Ns P a mass φn t) =
        asymHalfDensityFactor M Ns P a mass φp *
          asymHalfDensityFactor M Ns P a mass φn *
          Real.exp
            (∑ x : Fin Ns,
              asymHalfSlice M Ns φp (asymHalfLastTime M) x *
                asymHalfSlice M Ns φn (asymHalfLastTime M) x) *
          Real.exp
            (∑ x : Fin Ns, asymHalfSlice M Ns φp 0 x * asymHalfSlice M Ns φn 0 x) := by
    have hinner0 :
        (∑ x : Fin Ns, asymHalfSlice M Ns φn 0 x * asymHalfSlice M Ns φp 0 x) =
          ∑ x : Fin Ns, asymHalfSlice M Ns φp 0 x * asymHalfSlice M Ns φn 0 x := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      ring
    rw [asymTransferKernel, asymTransferKernel]
    rw [transferGaussian_sub_split (Ns := Ns)
      (asymHalfSlice M Ns φp (asymHalfLastTime M))
      (asymHalfSlice M Ns φn (asymHalfLastTime M))]
    rw [transferGaussian_sub_split (Ns := Ns) (asymHalfSlice M Ns φn 0)
      (asymHalfSlice M Ns φp 0)]
    rw [hinner0]
    unfold asymHalfDensityFactor asymHalfNormSq
    ac_rfl
  rw [hfactor, ← exp_neg_asymLinkEPos (M := M) (Ns := Ns) P a mass φp,
    ← exp_neg_asymLinkEPos (M := M) (Ns := Ns) P a mass φn]
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  have hcross :
      MeasureTheory.Measure.EvenFerroReflectionData.crossingEnergy
        (asymLinkReflectionData (M := M) (Ns := Ns) P a mass)
        (MeasureTheory.Measure.positivePart φ) (MeasureTheory.Measure.negativePart φ) =
      (∑ x : Fin Ns, asymHalfSlice M Ns φp 0 x * asymHalfSlice M Ns φn 0 x) +
        ∑ x : Fin Ns,
          asymHalfSlice M Ns φp (asymHalfLastTime M) x *
            asymHalfSlice M Ns φn (asymHalfLastTime M) x := by
    simpa [φp, φn] using
      (asymLink_crossingEnergy_eq (M := M) (Ns := Ns) P a mass φp φn)
  rw [MeasureTheory.Measure.EvenFerroReflectionData.density, hcross]
  congr 1
  simp [asymLinkReflectionData, φp, φn]
  ring

private theorem hsHalfFactor_nonneg {ι : Type*} [DecidableEq ι]
    (edges : Finset ι) (J : ι → ℝ) (i : ι) (a : ι → ℝ) (z : ℝ) :
    0 ≤ MeasureTheory.Measure.hsHalfFactor edges J i a z := by
  by_cases hi : i ∈ edges
  · simp [MeasureTheory.Measure.hsHalfFactor, hi, (Real.exp_pos _).le]
  · simp [MeasureTheory.Measure.hsHalfFactor, hi]

private theorem posPartIntegrand_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : MeasureTheory.Measure.EvenFerroReflectionData ι)
    (a z : ι → ℝ) :
    0 ≤ d.posPartIntegrand a z := by
  unfold MeasureTheory.Measure.EvenFerroReflectionData.posPartIntegrand
  refine mul_nonneg (Real.exp_pos _).le ?_
  exact Finset.prod_nonneg fun i _ => hsHalfFactor_nonneg d.edges d.J i a (z i)

private theorem measurable_posPartIntegrand {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : MeasureTheory.Measure.EvenFerroReflectionData ι)
    : Measurable (fun az : (ι → ℝ) × (ι → ℝ) => d.posPartIntegrand az.1 az.2) := by
  unfold MeasureTheory.Measure.EvenFerroReflectionData.posPartIntegrand
  refine ((Real.measurable_exp.comp (d.measurable_EPos.comp measurable_fst).neg).mul ?_)
  refine Finset.measurable_prod _ (fun i _ => ?_)
  by_cases hi : i ∈ d.edges
  · have h :
        Measurable (fun az : (ι → ℝ) × (ι → ℝ) =>
          Real.exp (-(d.J i / 2 * az.1 i ^ 2) + Real.sqrt (d.J i) * az.2 i * az.1 i)) := by
        fun_prop
    simpa [MeasureTheory.Measure.hsHalfFactor, hi] using h
  · simpa [MeasureTheory.Measure.hsHalfFactor, hi] using measurable_const

private theorem measurable_posPartIntegrand_right {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : MeasureTheory.Measure.EvenFerroReflectionData ι)
    (a : ι → ℝ) :
    Measurable (fun z : ι → ℝ => d.posPartIntegrand a z) := by
  have hpair : Measurable (fun z : ι → ℝ => (a, z)) := by
    fun_prop
  simpa using (measurable_posPartIntegrand d).comp hpair

private theorem measurable_hsSquareIntegrand {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : MeasureTheory.Measure.EvenFerroReflectionData ι)
    {G : (ι → ℝ) → ℝ} (hG : Measurable G) :
    Measurable (MeasureTheory.Measure.hsSquareIntegrand d G) := by
  unfold MeasureTheory.Measure.hsSquareIntegrand
  have hpos₁ :
      Measurable
        (fun x : ((ι → ℝ) × (ι → ℝ)) × (ι → ℝ) =>
          d.posPartIntegrand x.1.1 x.2) := by
    have hpair :
        Measurable
          (fun x : ((ι → ℝ) × (ι → ℝ)) × (ι → ℝ) => (x.1.1, x.2)) := by
      fun_prop
    simpa using (measurable_posPartIntegrand d).comp hpair
  have hpos₂ :
      Measurable
        (fun x : ((ι → ℝ) × (ι → ℝ)) × (ι → ℝ) =>
          d.posPartIntegrand x.1.2 x.2) := by
    have hpair :
        Measurable
          (fun x : ((ι → ℝ) × (ι → ℝ)) × (ι → ℝ) => (x.1.2, x.2)) := by
      fun_prop
    simpa using (measurable_posPartIntegrand d).comp hpair
  exact ((hG.comp (measurable_fst.comp measurable_fst)).mul hpos₁).mul
    ((hG.comp (measurable_snd.comp measurable_fst)).mul hpos₂)

private theorem evenNearestNeighbour_hFubini {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : MeasureTheory.Measure.EvenFerroReflectionData ι)
    {G : (ι → ℝ) → ℝ} (hG : Measurable G)
    (hInt : Integrable (fun φ : MeasureTheory.Measure.EvenConfig ι =>
      G (MeasureTheory.Measure.positivePart φ) *
        G (MeasureTheory.Measure.negativePart φ)) d.μ) :
    Integrable (MeasureTheory.Measure.hsSquareIntegrand d G)
      (((MeasureTheory.Measure.halfBaseMeasure ι).prod
          (MeasureTheory.Measure.halfBaseMeasure ι)).prod
        (MeasureTheory.Measure.stdGaussianPi ι)) := by
  let ν : Measure (ι → ℝ) := MeasureTheory.Measure.halfBaseMeasure ι
  let γ : Measure (ι → ℝ) := MeasureTheory.Measure.stdGaussianPi ι
  let pairν : Measure ((ι → ℝ) × (ι → ℝ)) := ν.prod ν
  let e : MeasureTheory.Measure.EvenConfig ι ≃ᵐ ((ι → ℝ) × (ι → ℝ)) :=
    MeasurableEquiv.sumPiEquivProdPi (fun _ : Sum ι ι => ℝ)
  let merge : ((ι → ℝ) × (ι → ℝ)) → MeasureTheory.Measure.EvenConfig ι :=
    fun p s => Sum.elim p.1 p.2 s
  let Hpair : ((ι → ℝ) × (ι → ℝ)) → ℝ :=
    fun p => |G p.1 * G p.2| * d.density (merge p)
  haveI : SFinite ν := by
    dsimp [ν, MeasureTheory.Measure.halfBaseMeasure]
    infer_instance
  haveI : SFinite γ := by
    dsimp [γ, MeasureTheory.Measure.stdGaussianPi]
    infer_instance
  haveI : SFinite pairν := by
    dsimp [pairν]
    infer_instance
  have hdensMeas :
      Measurable (fun φ : MeasureTheory.Measure.EvenConfig ι =>
        ENNReal.ofReal (d.density φ)) :=
    ENNReal.measurable_ofReal.comp d.measurable_density
  have hdensTop : ∀ᵐ φ ∂d.baseMeasure, ENNReal.ofReal (d.density φ) < ∞ := by
    simp
  have hnorm :
      Integrable (fun φ : MeasureTheory.Measure.EvenConfig ι =>
        |G (MeasureTheory.Measure.positivePart φ) *
          G (MeasureTheory.Measure.negativePart φ)|) d.μ := by
    simpa [Real.norm_eq_abs] using hInt.norm
  have hbase :
      Integrable (fun φ : MeasureTheory.Measure.EvenConfig ι =>
        |G (MeasureTheory.Measure.positivePart φ)| *
          |G (MeasureTheory.Measure.negativePart φ)| * d.density φ)
        d.baseMeasure := by
    refine ((integrable_withDensity_iff hdensMeas hdensTop).mp hnorm).congr ?_
    refine Filter.Eventually.of_forall (fun φ => ?_)
    change
      |G (MeasureTheory.Measure.positivePart φ) * G (MeasureTheory.Measure.negativePart φ)| *
          (ENNReal.ofReal (d.density φ)).toReal =
        |G (MeasureTheory.Measure.positivePart φ)| *
          |G (MeasureTheory.Measure.negativePart φ)| * d.density φ
    rw [ENNReal.toReal_ofReal (d.density_nonneg φ)]
    rw [abs_mul]
  have hsplit :
      MeasurePreserving e d.baseMeasure pairν := by
    simpa [e, pairν, ν, MeasureTheory.Measure.EvenFerroReflectionData.baseMeasure] using
      (measurePreserving_sumPiEquivProdPi
        (fun _ : Sum ι ι => (volume : Measure ℝ)) :
          MeasurePreserving
            (MeasurableEquiv.sumPiEquivProdPi (fun _ : Sum ι ι => ℝ))
            (Measure.pi (fun _ : Sum ι ι => (volume : Measure ℝ)))
            ((Measure.pi (fun _ : ι => (volume : Measure ℝ))).prod
              (Measure.pi (fun _ : ι => (volume : Measure ℝ)))))
  have hpair_int : Integrable Hpair pairν := by
    have hcomp :
        Integrable (fun φ : MeasureTheory.Measure.EvenConfig ι => Hpair (e φ)) d.baseMeasure := by
      refine hbase.congr ?_
      refine Filter.Eventually.of_forall (fun φ => ?_)
      dsimp [Hpair]
      have hfst : (e φ).1 = MeasureTheory.Measure.positivePart φ := by
        rfl
      have hsnd : (e φ).2 = MeasureTheory.Measure.negativePart φ := by
        rfl
      have hmerge : merge (e φ) = φ := by
        funext s
        cases s <;> rfl
      rw [hfst, hsnd, hmerge, abs_mul]
    have hmap : Integrable Hpair (Measure.map e d.baseMeasure) :=
      (integrable_map_equiv e Hpair).2 hcomp
    rw [hsplit.map_eq] at hmap
    simpa [pairν] using hmap
  have hHpair_nonneg : 0 ≤ᵐ[pairν] Hpair := by
    refine Filter.Eventually.of_forall (fun p => ?_)
    exact mul_nonneg (abs_nonneg _) (d.density_nonneg (merge p))
  have hHpair_lint :
      ∫⁻ p, ENNReal.ofReal (Hpair p) ∂pairν < ∞ := by
    simpa [hasFiniteIntegral_iff_ofReal hHpair_nonneg]
      using hpair_int.hasFiniteIntegral
  have hslice_norm :
      ∀ p : (ι → ℝ) × (ι → ℝ),
        ∫⁻ z, ENNReal.ofReal
            ‖MeasureTheory.Measure.hsSquareIntegrand d G (p, z)‖ ∂γ =
          ENNReal.ofReal (Hpair p) := by
    intro p
    let q : (ι → ℝ) → ℝ := fun z => d.posPartIntegrand p.1 z * d.posPartIntegrand p.2 z
    have hq_meas : Measurable q :=
      (measurable_posPartIntegrand_right d p.1).mul (measurable_posPartIntegrand_right d p.2)
    have hq_nonneg : 0 ≤ᵐ[γ] q := by
      refine Filter.Eventually.of_forall (fun z => ?_)
      exact mul_nonneg (posPartIntegrand_nonneg d p.1 z) (posPartIntegrand_nonneg d p.2 z)
    have hq_density :
        d.density (merge p) = ∫ z, q z ∂γ := by
      simpa [q, merge, MeasureTheory.Measure.positivePart,
        MeasureTheory.Measure.negativePart] using
        (MeasureTheory.Measure.density_hs_factor d (merge p))
    have hq_lint_fin :
        ∫⁻ z, ENNReal.ofReal (q z) ∂γ < ∞ := by
      have hq_toReal :
          ENNReal.toReal (∫⁻ z, ENNReal.ofReal (q z) ∂γ) = d.density (merge p) := by
        calc
          ENNReal.toReal (∫⁻ z, ENNReal.ofReal (q z) ∂γ)
              = ∫ z, q z ∂γ := by
                  symm
                  exact integral_eq_lintegral_of_nonneg_ae hq_nonneg hq_meas.aestronglyMeasurable
          _ = d.density (merge p) := hq_density.symm
      by_contra hq_top
      have hq_eq_top : ∫⁻ z, ENNReal.ofReal (q z) ∂γ = ∞ := by
        exact le_antisymm le_top (le_of_not_gt hq_top)
      have : d.density (merge p) = 0 := by
        rw [← hq_toReal, hq_eq_top]
        simp
      exact (ne_of_gt (Real.exp_pos _)) this
    have hq_int : Integrable q γ := by
      refine ⟨hq_meas.aestronglyMeasurable, ?_⟩
      simpa [hasFiniteIntegral_iff_ofReal hq_nonneg] using hq_lint_fin
    have hq_lint_eq :
        ∫⁻ z, ENNReal.ofReal (q z) ∂γ = ENNReal.ofReal (d.density (merge p)) := by
      rw [← ofReal_integral_eq_lintegral_ofReal hq_int hq_nonneg, hq_density]
    have habs :
        (fun z => ENNReal.ofReal
          ‖MeasureTheory.Measure.hsSquareIntegrand d G (p, z)‖) =
        fun z => ENNReal.ofReal |G p.1 * G p.2| * ENNReal.ofReal (q z) := by
      funext z
      dsimp [MeasureTheory.Measure.hsSquareIntegrand, q]
      have h₁ := posPartIntegrand_nonneg d p.1 z
      have h₂ := posPartIntegrand_nonneg d p.2 z
      have hmul :
          |G p.1 * d.posPartIntegrand p.1 z * (G p.2 * d.posPartIntegrand p.2 z)| =
            |G p.1 * G p.2| * (d.posPartIntegrand p.1 z * d.posPartIntegrand p.2 z) := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg h₁, abs_of_nonneg h₂, abs_mul]
        ring
      rw [hmul, ENNReal.ofReal_mul (abs_nonneg _)]
    calc
      ∫⁻ z, ENNReal.ofReal ‖MeasureTheory.Measure.hsSquareIntegrand d G (p, z)‖ ∂γ
          = ∫⁻ z, ENNReal.ofReal |G p.1 * G p.2| * ENNReal.ofReal (q z) ∂γ := by
              rw [habs]
      _ = ENNReal.ofReal |G p.1 * G p.2| * ∫⁻ z, ENNReal.ofReal (q z) ∂γ := by
            change ∫⁻ z, ENNReal.ofReal |G p.1 * G p.2| * (ENNReal.ofReal ∘ q) z ∂γ =
              ENNReal.ofReal |G p.1 * G p.2| * ∫⁻ z, (ENNReal.ofReal ∘ q) z ∂γ
            rw [lintegral_const_mul'' _ (ENNReal.measurable_ofReal.comp hq_meas).aemeasurable]
      _ = ENNReal.ofReal |G p.1 * G p.2| * ENNReal.ofReal (d.density (merge p)) := by
            rw [hq_lint_eq]
      _ = ENNReal.ofReal (Hpair p) := by
            rw [← ENNReal.ofReal_mul (abs_nonneg _)]
  have hnormMeas :
      AEMeasurable
        (fun x => ENNReal.ofReal ‖MeasureTheory.Measure.hsSquareIntegrand d G x‖)
        (pairν.prod γ) :=
    (ENNReal.measurable_ofReal.comp (measurable_hsSquareIntegrand d hG).norm).aemeasurable
  refine ⟨(measurable_hsSquareIntegrand d hG).aestronglyMeasurable, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_norm]
  rw [MeasureTheory.lintegral_prod _ hnormMeas]
  calc
    ∫⁻ x, ∫⁻ y, ENNReal.ofReal ‖MeasureTheory.Measure.hsSquareIntegrand d G (x, y)‖ ∂γ ∂pairν
        = ∫⁻ p, ENNReal.ofReal (Hpair p) ∂pairν := by
            refine lintegral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
            exact hslice_norm p
    _ < ∞ := hHpair_lint

theorem _root_.MeasureTheory.Measure.isReflectionPositive_of_evenNearestNeighbour_unconditional
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : MeasureTheory.Measure.EvenFerroReflectionData ι) :
    MeasureTheory.Measure.IsReflectionPositive d.μ d.θ d.mPos := by
  exact MeasureTheory.Measure.isReflectionPositive_of_evenNearestNeighbour d
    (by
      intro G hG hInt
      exact Pphi2.evenNearestNeighbour_hFubini (d := d) (G := G) hG hInt)

theorem _root_.MeasureTheory.Measure.IsReflectionPositive.smul
    {Ω : Type*} [m0 : MeasurableSpace Ω]
    {μ : Measure Ω} {θ : Ω → Ω} {mPos : MeasurableSpace Ω}
    (hRP : @MeasureTheory.Measure.IsReflectionPositive Ω m0 μ θ mPos)
    {c : ℝ≥0∞} (hc_top : c ≠ ∞) :
    @MeasureTheory.Measure.IsReflectionPositive Ω m0 (c • μ) θ mPos := by
  by_cases hc0 : c = 0
  · intro F hF hInt
    change 0 ≤ ∫ x, F x * F (θ x) ∂(c • μ)
    simp [hc0]
  · intro F hF hInt
    have hIntμ : Integrable (fun x => F x * F (θ x)) μ := by
      rw [integrable_smul_measure hc0 hc_top] at hInt
      exact hInt
    change 0 ≤ ∫ x, F x * F (θ x) ∂(c • μ)
    rw [integral_smul_measure]
    simpa [smul_eq_mul] using
      mul_nonneg ENNReal.toReal_nonneg (hRP F hF hIntμ)

theorem _root_.MeasureTheory.Measure.IsReflectionPositive.map_measurableEquiv_comap
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {μ : Measure α} {θα : α → α} {θβ : β → β}
    {pα : α → γ} {pβ : β → γ}
    (hRP : MeasureTheory.Measure.IsReflectionPositive μ θα
      (MeasurableSpace.comap pα inferInstance))
    (e : α ≃ᵐ β)
    (hp : pβ ∘ e = pα)
    (hθ : ∀ x, e (θα x) = θβ (e x)) :
    MeasureTheory.Measure.IsReflectionPositive (Measure.map e μ) θβ
      (MeasurableSpace.comap pβ inferInstance) := by
  intro F hF hInt
  have hF' :
      Measurable[(inferInstance : MeasurableSpace γ).comap pβ] F := by
    simpa using hF
  rcases hF'.exists_eq_measurable_comp (f := pβ) with ⟨G, hG, hFG⟩
  have hsource_meas : Measurable[(inferInstance : MeasurableSpace γ).comap pα] (F ∘ e) := by
    rw [hFG, Function.comp_assoc, hp]
    exact hG.comp (comap_measurable pα)
  have hsourceInt :
      Integrable (fun x => (F ∘ e) x * (F ∘ e) (θα x)) μ := by
    have hcomp :
        Integrable (fun x => F (e x) * F (θβ (e x))) μ :=
      (MeasureTheory.integrable_map_equiv e
        (fun y : β => F y * F (θβ y))).mp hInt
    refine hcomp.congr ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    simp [Function.comp_apply, hθ x]
  change 0 ≤ ∫ y, F y * F (θβ y) ∂(Measure.map e μ)
  rw [MeasureTheory.integral_map_equiv e]
  have hcomp :
      (fun x => F (e x) * F (θβ (e x))) = fun x => (F ∘ e) x * (F ∘ e) (θα x) := by
    funext x
    simp [Function.comp_apply, hθ x]
  rw [hcomp]
  exact hRP (F ∘ e) hsource_meas hsourceInt

private theorem map_asymLinkReflectionData_mu_eq_pathDensityMeasure
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    Measure.map (asymLinkPathMeasurableEquiv M Ns)
      ((asymLinkReflectionData (M := M) (Ns := Ns) P a mass).μ) =
      (volume : Measure (ZMod (2 * M) → SpatialField Ns)).withDensity
        (fun ψ => ENNReal.ofReal
          ((asymTransferSystem (Nt := 2 * M) (Ns := Ns) P a mass ha hmass).pathDensity
            (2 * M) ψ)) := by
  let Ts := asymTransferSystem (Nt := 2 * M) (Ns := Ns) P a mass ha hmass
  let g : (ZMod (2 * M) → SpatialField Ns) → ℝ≥0∞ := fun ψ =>
    ENNReal.ofReal (Ts.pathDensity (2 * M) ψ)
  have hdens :
      (fun φ =>
        ENNReal.ofReal
          ((asymLinkReflectionData (M := M) (Ns := Ns) P a mass).density φ)) =
        fun φ => g (asymLinkPathMeasurableEquiv M Ns φ) := by
    funext φ
    rw [asymLinkReflectionData_density_eq_pathDensity (M := M) (Ns := Ns) P a mass ha hmass φ]
  unfold MeasureTheory.Measure.EvenFerroReflectionData.μ
  rw [hdens, withDensity_comp_map_measurableEquiv]
  change
    (Measure.map (asymLinkPathMeasurableEquiv M Ns)
        (Measure.pi
          (fun _ : Sum (AsymHalfSites M Ns) (AsymHalfSites M Ns) => (volume : Measure ℝ)))).withDensity g =
      (volume : Measure (ZMod (2 * M) → SpatialField Ns)).withDensity g
  congr 1
  change Measure.map (asymLinkPathMeasurableEquiv M Ns)
      (Measure.pi
        (fun _ : Sum (AsymHalfSites M Ns) (AsymHalfSites M Ns) => (volume : Measure ℝ))) =
    (volume : Measure (ZMod (2 * M) → SpatialField Ns))
  exact (measurePreserving_asymLinkPathMeasurableEquiv M Ns).map_eq

private theorem asymTransferPathMeasure_partition_inv_ne_top
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    (ENNReal.ofReal
      ((asymTransferSystem (Nt := 2 * M) (Ns := Ns) P a mass ha hmass).partition
        (2 * M)))⁻¹ ≠ ∞ := by
  let Ts := asymTransferSystem (Nt := 2 * M) (Ns := Ns) P a mass ha hmass
  let ρ : Measure (ZMod (2 * M) → SpatialField Ns) :=
    (Measure.pi (fun _ : ZMod (2 * M) => (volume : Measure (SpatialField Ns)))).withDensity
      (fun ψ => ENNReal.ofReal (Ts.pathDensity (2 * M) ψ))
  have hpath :
      (((interactingLatticeMeasureAsym (2 * M) Ns P a mass ha hmass).map
          (evalMapAsym (2 * M) Ns)).map (asymSliceEquiv (2 * M) Ns)) =
        Ts.pathMeasure (2 * M) := by
    simpa [Ts] using interactingLatticeMeasureAsym_slice_pushforward_eq_pathMeasure
      (Nt := 2 * M) (Ns := Ns) P a mass ha hmass
  haveI : IsProbabilityMeasure (interactingLatticeMeasureAsym (2 * M) Ns P a mass ha hmass) :=
    interactingLatticeMeasureAsym_isProbability (2 * M) Ns P a mass ha hmass
  haveI : IsProbabilityMeasure
      ((interactingLatticeMeasureAsym (2 * M) Ns P a mass ha hmass).map
        (evalMapAsym (2 * M) Ns)) :=
    Measure.isProbabilityMeasure_map (measurable_evalMapAsym (2 * M) Ns).aemeasurable
  haveI hprob : IsProbabilityMeasure
      (((interactingLatticeMeasureAsym (2 * M) Ns P a mass ha hmass).map
          (evalMapAsym (2 * M) Ns)).map (asymSliceEquiv (2 * M) Ns)) :=
    Measure.isProbabilityMeasure_map
      (measurePreserving_asymSliceEquiv (2 * M) Ns).measurable.aemeasurable
  have hpm_univ : Ts.pathMeasure (2 * M) Set.univ = 1 := by
    rw [← hpath]
    exact hprob.measure_univ
  have hmass_one :
      (ENNReal.ofReal (Ts.partition (2 * M)))⁻¹ * ρ Set.univ = 1 := by
    simpa [Ts, ρ, ReflectionPositivity.TransferSystem.pathMeasure, Measure.smul_apply,
      smul_eq_mul] using hpm_univ
  have hρuniv_lt : ρ Set.univ ≠ ⊤ := by
    intro htop
    rw [htop] at hmass_one
    rcases eq_or_ne (ENNReal.ofReal (Ts.partition (2 * M)))⁻¹ 0 with hc | hc
    · rw [hc, zero_mul] at hmass_one
      exact zero_ne_one hmass_one
    · rw [ENNReal.mul_top hc] at hmass_one
      exact ENNReal.top_ne_one hmass_one
  have hρuniv_ne : ρ Set.univ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hmass_one
    exact one_ne_zero hmass_one.symm
  have hpd_nonneg :
      0 ≤ᵐ[Measure.pi (fun _ : ZMod (2 * M) => (volume : Measure (SpatialField Ns)))]
        Ts.pathDensity (2 * M) :=
    ae_of_all _ (fun ψ => Ts.pathDensity_nonneg (2 * M) ψ)
  have hlint :
      ∫⁻ ψ, ENNReal.ofReal (Ts.pathDensity (2 * M) ψ)
        ∂(Measure.pi (fun _ : ZMod (2 * M) => (volume : Measure (SpatialField Ns)))) =
      ρ Set.univ := by
    simp [ρ]
  have hpd_integrable :
      Integrable (Ts.pathDensity (2 * M))
        (Measure.pi (fun _ : ZMod (2 * M) => (volume : Measure (SpatialField Ns)))) := by
    refine ⟨(Ts.pathDensity_measurable (2 * M)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hpd_nonneg, hlint]
    exact lt_of_le_of_ne le_top hρuniv_lt
  have hpartition : ENNReal.ofReal (Ts.partition (2 * M)) = ρ Set.univ := by
    have hpart_eq : Ts.partition (2 * M) =
        ∫ ψ, Ts.pathDensity (2 * M) ψ
          ∂(Measure.pi (fun _ : ZMod (2 * M) => (volume : Measure (SpatialField Ns)))) := rfl
    rw [hpart_eq, ofReal_integral_eq_lintegral_ofReal hpd_integrable hpd_nonneg, hlint]
  have hpart_ne : ENNReal.ofReal (Ts.partition (2 * M)) ≠ 0 := by
    simpa [hpartition] using hρuniv_ne
  rw [ENNReal.inv_ne_top]
  simpa [ENNReal.ofReal_eq_zero, Ts.partition_nonneg (2 * M)] using hpart_ne

theorem asymTransferPathMeasure_isReflectionPositive_link
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    MeasureTheory.Measure.IsReflectionPositive
      ((asymTransferSystem (Nt := 2 * M) (Ns := Ns) P a mass ha hmass).pathMeasure (2 * M))
      (asymLinkPathReflection M Ns) (asymLinkPathMPos M Ns) := by
  let d := asymLinkReflectionData (M := M) (Ns := Ns) P a mass
  let Ts := asymTransferSystem (Nt := 2 * M) (Ns := Ns) P a mass ha hmass
  have hRPd :
      MeasureTheory.Measure.IsReflectionPositive d.μ d.θ d.mPos :=
    MeasureTheory.Measure.isReflectionPositive_of_evenNearestNeighbour_unconditional d
  have hRPpath :
      MeasureTheory.Measure.IsReflectionPositive
        (Measure.map (asymLinkPathMeasurableEquiv M Ns) d.μ)
        (asymLinkPathReflection M Ns) (asymLinkPathMPos M Ns) := by
    exact MeasureTheory.Measure.IsReflectionPositive.map_measurableEquiv_comap hRPd
      (asymLinkPathMeasurableEquiv M Ns)
      (by
        funext φ
        ext i
        simp [asymLinkPathPositivePart, MeasureTheory.Measure.positivePart])
      (by
        intro φ
        simpa [d, MeasureTheory.Measure.EvenFerroReflectionData.θ] using
          (asymLinkPathReflection_eq_evenTheta (M := M) (Ns := Ns) φ).symm)
  rw [map_asymLinkReflectionData_mu_eq_pathDensityMeasure (M := M) (Ns := Ns) P a mass ha hmass]
    at hRPpath
  have hc_top := asymTransferPathMeasure_partition_inv_ne_top
    (M := M) (Ns := Ns) P a mass ha hmass
  simpa [Ts, ReflectionPositivity.TransferSystem.pathMeasure] using
    (MeasureTheory.Measure.IsReflectionPositive.smul
      (μ := (volume : Measure (ZMod (2 * M) → SpatialField Ns)).withDensity
        (fun ψ => ENNReal.ofReal (Ts.pathDensity (2 * M) ψ)))
      (θ := asymLinkPathReflection M Ns) (mPos := asymLinkPathMPos M Ns)
      hRPpath (c := (ENNReal.ofReal (Ts.partition (2 * M)))⁻¹) hc_top)

theorem interactingLatticeMeasureAsym_isReflectionPositive_link
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    MeasureTheory.Measure.IsReflectionPositive
      (interactingLatticeMeasureAsym (2 * M) Ns P a mass ha hmass)
      (asymLinkReflectionConfig M Ns) (asymLinkMPos M Ns) := by
  let Ts := asymTransferSystem (Nt := 2 * M) (Ns := Ns) P a mass ha hmass
  have hRPpath := asymTransferPathMeasure_isReflectionPositive_link
    (M := M) (Ns := Ns) P a mass ha hmass
  have hRPcfg :
      MeasureTheory.Measure.IsReflectionPositive
        (Measure.map (asymLinkConfigPathMeasurableEquiv M Ns).symm (Ts.pathMeasure (2 * M)))
        (asymLinkReflectionConfig M Ns) (asymLinkMPos M Ns) := by
    exact MeasureTheory.Measure.IsReflectionPositive.map_measurableEquiv_comap hRPpath
      (asymLinkConfigPathMeasurableEquiv M Ns).symm
      (by
        funext ψ
        simpa using
          (asymLinkPathPositivePart_config (M := M) (Ns := Ns)
            ((asymLinkConfigPathMeasurableEquiv M Ns).symm ψ)).symm)
      (by
        intro ψ
        apply (asymLinkConfigPathMeasurableEquiv M Ns).injective
        calc
          asymLinkConfigPathMeasurableEquiv M Ns
              ((asymLinkConfigPathMeasurableEquiv M Ns).symm
                (asymLinkPathReflection M Ns ψ))
              = asymLinkPathReflection M Ns ψ := by simp
          _ = asymLinkConfigPathMeasurableEquiv M Ns
              (asymLinkReflectionConfig M Ns
                ((asymLinkConfigPathMeasurableEquiv M Ns).symm ψ)) := by
                symm
                simpa using
                  (asymLinkConfigPathMeasurableEquiv_reflection (M := M) (Ns := Ns)
                    ((asymLinkConfigPathMeasurableEquiv M Ns).symm ψ)))
  have hmap_cfg :
      Measure.map (asymLinkConfigPathMeasurableEquiv M Ns)
        (interactingLatticeMeasureAsym (2 * M) Ns P a mass ha hmass) =
      Ts.pathMeasure (2 * M) := by
    change Measure.map
        ((asymSliceEquiv (2 * M) Ns) ∘ (evalMapAsym (2 * M) Ns))
        (interactingLatticeMeasureAsym (2 * M) Ns P a mass ha hmass) =
      Ts.pathMeasure (2 * M)
    rw [← MeasureTheory.Measure.map_map
      (measurePreserving_asymSliceEquiv (2 * M) Ns).measurable
      (measurable_evalMapAsym (2 * M) Ns)]
    simpa [Ts] using interactingLatticeMeasureAsym_slice_pushforward_eq_pathMeasure
      (Nt := 2 * M) (Ns := Ns) P a mass ha hmass
  have hmap_back :
      Measure.map (asymLinkConfigPathMeasurableEquiv M Ns).symm (Ts.pathMeasure (2 * M)) =
        interactingLatticeMeasureAsym (2 * M) Ns P a mass ha hmass := by
    rw [← hmap_cfg]
    simpa using (MeasurableEquiv.map_symm_map
      (μ := interactingLatticeMeasureAsym (2 * M) Ns P a mass ha hmass)
      (asymLinkConfigPathMeasurableEquiv M Ns))
  rw [hmap_back] at hRPcfg
  simpa [Ts] using hRPcfg

end Pphi2
