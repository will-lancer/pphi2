/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Pphi2.AsymTorus.AsymNormalizedKernelSemigroup
import Pphi2.AsymTorus.AsymNormalizedKernelRemainderOrthogonality

/-!
# Semigroup composition for normalized kernel remainders

Subtracting the rank-one ground kernel from the normalized transfer kernel
turns kernel composition into composition of the ground-orthogonal
remainders.  The cross terms vanish through the proved ground-convolution
identities.  Product-space `L2` membership supplies almost-everywhere row
integrability for the expansion.
-/

noncomputable section

open MeasureTheory

namespace Pphi2

variable {Nt Ns : ℕ} [NeZero Nt] [NeZero Ns]

/-- Every finite-lattice normalized remainder has almost-everywhere `L2`
rows. -/
theorem asymNormalizedTransferKernelRemainder_row_memLp_two
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (m : ℕ) :
    ∀ᵐ x : SpatialField Ns ∂volume,
      MemLp
        (asymNormalizedTransferKernelRemainder
          (Nt := Nt) (Ns := Ns) P a mass ha hmass m x)
        2 (volume : Measure (SpatialField Ns)) := by
  let R := asymNormalizedTransferKernelRemainder
    (Nt := Nt) (Ns := Ns) P a mass ha hmass m
  have hR := asymNormalizedTransferKernelRemainder_memLp_two
    (Nt := Nt) (Ns := Ns) P a mass ha hmass m
  have hR_sq : Integrable
      (fun p : SpatialField Ns × SpatialField Ns => Function.uncurry R p ^ 2)
      ((volume : Measure (SpatialField Ns)).prod volume) := by
    simpa only [R] using hR.integrable_sq
  have hR_meas : AEStronglyMeasurable (Function.uncurry R)
      ((volume : Measure (SpatialField Ns)).prod volume) := by
    simpa only [R] using hR.aestronglyMeasurable
  filter_upwards [hR_sq.prod_right_ae, hR_meas.prodMk_left]
      with x hsq hmeas
  exact (memLp_two_iff_integrable_sq hmeas).2 hsq

/-- Remainder kernels compose with the same shifted index as the normalized
transfer kernels.  The row conditions for the two endpoints hold on a
product of full-measure sets, which gives a product-measure conclusion. -/
theorem asymNormalizedTransferKernelRemainder_add_one_comp
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (m n : ℕ) :
    ∀ᵐ p : SpatialField Ns × SpatialField Ns
        ∂((volume : Measure (SpatialField Ns)).prod volume),
      asymNormalizedTransferKernelRemainder
          (Nt := Nt) (Ns := Ns) P a mass ha hmass (m + n + 1) p.1 p.2 =
        ∫ z, asymNormalizedTransferKernelRemainder
            (Nt := Nt) (Ns := Ns) P a mass ha hmass m p.1 z *
          asymNormalizedTransferKernelRemainder
            (Nt := Nt) (Ns := Ns) P a mass ha hmass n z p.2 ∂volume := by
  let Omega := asymGroundVector Nt Ns P a mass ha hmass
  let Km := asymNormalizedTransferKernelPower
    (Nt := Nt) (Ns := Ns) P a mass ha hmass m
  let Kn := asymNormalizedTransferKernelPower
    (Nt := Nt) (Ns := Ns) P a mass ha hmass n
  let Rm := asymNormalizedTransferKernelRemainder
    (Nt := Nt) (Ns := Ns) P a mass ha hmass m
  let Rn := asymNormalizedTransferKernelRemainder
    (Nt := Nt) (Ns := Ns) P a mass ha hmass n
  have hRm_rows := asymNormalizedTransferKernelRemainder_row_memLp_two
    (Nt := Nt) (Ns := Ns) P a mass ha hmass m
  have hRn_rows := asymNormalizedTransferKernelRemainder_row_memLp_two
    (Nt := Nt) (Ns := Ns) P a mass ha hmass n
  have hRm_orth := asymNormalizedTransferKernelRemainder_row_ground_orthogonal
    (Nt := Nt) (Ns := Ns) P a mass ha hmass m
  have hRn_orth := asymNormalizedTransferKernelRemainder_row_ground_orthogonal
    (Nt := Nt) (Ns := Ns) P a mass ha hmass n
  have hOmega : MemLp Omega 2 (volume : Measure (SpatialField Ns)) :=
    Lp.memLp Omega
  have hOmega_sq : Integrable (fun z => Omega z ^ 2) volume :=
    hOmega.integrable_sq
  have hOmega_sq_int : ∫ z, Omega z ^ 2 ∂volume = 1 := by
    simpa only [Omega] using
      integral_asymGroundVector_sq_eq_one
        (Nt := Nt) (Ns := Ns) P a mass ha hmass
  have hx : ∀ᵐ x : SpatialField Ns ∂volume,
      MemLp (Rm x) 2 (volume : Measure (SpatialField Ns)) ∧
        ∫ z, Rm x z * Omega z ∂volume = 0 := by
    filter_upwards [hRm_rows, hRm_orth] with x hRm_x hRm_zero
    exact ⟨hRm_x, hRm_zero⟩
  have hy : ∀ᵐ y : SpatialField Ns ∂volume,
      MemLp (Rn y) 2 (volume : Measure (SpatialField Ns)) ∧
        ∫ z, Rn y z * Omega z ∂volume = 0 := by
    filter_upwards [hRn_rows, hRn_orth] with y hRn_y hRn_zero
    exact ⟨hRn_y, hRn_zero⟩
  have hx_prod := Measure.quasiMeasurePreserving_fst.ae hx
  have hy_prod := Measure.quasiMeasurePreserving_snd.ae hy
  filter_upwards [hx_prod, hy_prod] with p hp_x hp_y
  obtain ⟨x, y⟩ := p
  rcases hp_x with ⟨hRm_x, hRm_zero⟩
  rcases hp_y with ⟨hRn_y, hRn_zero⟩
  have hRn_col : MemLp (fun z => Rn z y) 2
      (volume : Measure (SpatialField Ns)) := by
    refine MemLp.ae_eq (.of_forall fun z => ?_) hRn_y
    exact asymNormalizedTransferKernelRemainder_symm
      (Nt := Nt) (Ns := Ns) P a mass ha hmass n y z
  have hRR : Integrable (fun z => Rm x z * Rn z y) volume :=
    hRm_x.integrable_mul hRn_col
  have hRmOmega : Integrable (fun z => Rm x z * Omega z) volume :=
    hRm_x.integrable_mul hOmega
  have hOmegaRn : Integrable (fun z => Omega z * Rn z y) volume :=
    hOmega.integrable_mul hRn_col
  have hB : Integrable (fun z => (Rm x z * Omega z) * Omega y) volume :=
    hRmOmega.mul_const _
  have hC : Integrable (fun z => Omega x * (Omega z * Rn z y)) volume :=
    hOmegaRn.const_mul _
  have hD : Integrable (fun z => (Omega x * Omega y) * Omega z ^ 2) volume :=
    hOmega_sq.const_mul _
  have hB_zero : ∫ z, (Rm x z * Omega z) * Omega y ∂volume = 0 := by
    rw [integral_mul_const, hRm_zero, zero_mul]
  have hC_zero : ∫ z, Omega x * (Omega z * Rn z y) ∂volume = 0 := by
    rw [integral_const_mul]
    have hcol_zero : ∫ z, Omega z * Rn z y ∂volume = 0 := by
      calc
        (∫ z, Omega z * Rn z y ∂volume) =
            ∫ z, Rn y z * Omega z ∂volume := by
          refine integral_congr_ae (.of_forall fun z => ?_)
          rw [asymNormalizedTransferKernelRemainder_symm
            (Nt := Nt) (Ns := Ns) P a mass ha hmass n]
          ring
        _ = 0 := hRn_zero
    rw [hcol_zero, mul_zero]
  have hD_ground : ∫ z, (Omega x * Omega y) * Omega z ^ 2 ∂volume =
      Omega x * Omega y := by
    rw [integral_const_mul, hOmega_sq_int, mul_one]
  have hexpand :
      (∫ z, Km x z * Kn z y ∂volume) =
        (∫ z, Rm x z * Rn z y ∂volume) +
          (∫ z, (Rm x z * Omega z) * Omega y ∂volume) +
          (∫ z, Omega x * (Omega z * Rn z y) ∂volume) +
          ∫ z, (Omega x * Omega y) * Omega z ^ 2 ∂volume := by
    calc
      (∫ z, Km x z * Kn z y ∂volume) =
          ∫ z,
            ((Rm x z * Rn z y) + (Rm x z * Omega z) * Omega y) +
            (Omega x * (Omega z * Rn z y) +
              (Omega x * Omega y) * Omega z ^ 2) ∂volume := by
        refine integral_congr_ae (.of_forall fun z => ?_)
        simp only [Km, Kn, Rm, Rn,
          asymNormalizedTransferKernelRemainder]
        ring
      _ = _ := by
        rw [integral_add (hRR.add hB) (hC.add hD),
          integral_add hRR hB, integral_add hC hD]
  calc
    asymNormalizedTransferKernelRemainder
        (Nt := Nt) (Ns := Ns) P a mass ha hmass (m + n + 1) x y =
        asymNormalizedTransferKernelPower
            (Nt := Nt) (Ns := Ns) P a mass ha hmass (m + n + 1) x y -
          Omega x * Omega y := rfl
    _ = (∫ z, Km x z * Kn z y ∂volume) - Omega x * Omega y := by
      rw [asymNormalizedTransferKernelPower_add_one_comp
        (Nt := Nt) (Ns := Ns) P a mass ha hmass m n x y]
    _ = (∫ z, Rm x z * Rn z y ∂volume) := by
      rw [hexpand, hB_zero, hC_zero, hD_ground]
      ring

/-- The nested almost-everywhere form of remainder composition. -/
theorem asymNormalizedTransferKernelRemainder_add_one_comp_ae_ae
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (m n : ℕ) :
    ∀ᵐ x : SpatialField Ns ∂volume,
      ∀ᵐ y : SpatialField Ns ∂volume,
        asymNormalizedTransferKernelRemainder
            (Nt := Nt) (Ns := Ns) P a mass ha hmass (m + n + 1) x y =
          ∫ z, asymNormalizedTransferKernelRemainder
              (Nt := Nt) (Ns := Ns) P a mass ha hmass m x z *
            asymNormalizedTransferKernelRemainder
              (Nt := Nt) (Ns := Ns) P a mass ha hmass n z y ∂volume := by
  exact Measure.ae_ae_of_ae_prod
    (asymNormalizedTransferKernelRemainder_add_one_comp
      (Nt := Nt) (Ns := Ns) P a mass ha hmass m n)

/-- The diagonal composition identity is proved separately from the
product-measure statement.  Both row conditions are imposed at the same
endpoint, so the result holds almost everywhere for `volume`. -/
theorem asymNormalizedTransferKernelRemainder_add_one_comp_diag
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (m n : ℕ) :
    ∀ᵐ x : SpatialField Ns ∂volume,
      asymNormalizedTransferKernelRemainder
          (Nt := Nt) (Ns := Ns) P a mass ha hmass (m + n + 1) x x =
        ∫ z, asymNormalizedTransferKernelRemainder
            (Nt := Nt) (Ns := Ns) P a mass ha hmass m x z *
          asymNormalizedTransferKernelRemainder
            (Nt := Nt) (Ns := Ns) P a mass ha hmass n z x ∂volume := by
  let Omega := asymGroundVector Nt Ns P a mass ha hmass
  let Km := asymNormalizedTransferKernelPower
    (Nt := Nt) (Ns := Ns) P a mass ha hmass m
  let Kn := asymNormalizedTransferKernelPower
    (Nt := Nt) (Ns := Ns) P a mass ha hmass n
  let Rm := asymNormalizedTransferKernelRemainder
    (Nt := Nt) (Ns := Ns) P a mass ha hmass m
  let Rn := asymNormalizedTransferKernelRemainder
    (Nt := Nt) (Ns := Ns) P a mass ha hmass n
  have hRm_rows := asymNormalizedTransferKernelRemainder_row_memLp_two
    (Nt := Nt) (Ns := Ns) P a mass ha hmass m
  have hRn_rows := asymNormalizedTransferKernelRemainder_row_memLp_two
    (Nt := Nt) (Ns := Ns) P a mass ha hmass n
  have hRm_orth := asymNormalizedTransferKernelRemainder_row_ground_orthogonal
    (Nt := Nt) (Ns := Ns) P a mass ha hmass m
  have hRn_orth := asymNormalizedTransferKernelRemainder_row_ground_orthogonal
    (Nt := Nt) (Ns := Ns) P a mass ha hmass n
  have hOmega : MemLp Omega 2 (volume : Measure (SpatialField Ns)) :=
    Lp.memLp Omega
  have hOmega_sq : Integrable (fun z => Omega z ^ 2) volume :=
    hOmega.integrable_sq
  have hOmega_sq_int : ∫ z, Omega z ^ 2 ∂volume = 1 := by
    simpa only [Omega] using
      integral_asymGroundVector_sq_eq_one
        (Nt := Nt) (Ns := Ns) P a mass ha hmass
  filter_upwards [hRm_rows, hRn_rows, hRm_orth, hRn_orth]
      with x hRm_x hRn_x hRm_zero hRn_zero
  have hRn_col : MemLp (fun z => Rn z x) 2
      (volume : Measure (SpatialField Ns)) := by
    refine MemLp.ae_eq (.of_forall fun z => ?_) hRn_x
    exact asymNormalizedTransferKernelRemainder_symm
      (Nt := Nt) (Ns := Ns) P a mass ha hmass n x z
  have hRR : Integrable (fun z => Rm x z * Rn z x) volume :=
    hRm_x.integrable_mul hRn_col
  have hRmOmega : Integrable (fun z => Rm x z * Omega z) volume :=
    hRm_x.integrable_mul hOmega
  have hOmegaRn : Integrable (fun z => Omega z * Rn z x) volume :=
    hOmega.integrable_mul hRn_col
  have hB : Integrable (fun z => (Rm x z * Omega z) * Omega x) volume :=
    hRmOmega.mul_const _
  have hC : Integrable (fun z => Omega x * (Omega z * Rn z x)) volume :=
    hOmegaRn.const_mul _
  have hD : Integrable (fun z => (Omega x * Omega x) * Omega z ^ 2) volume :=
    hOmega_sq.const_mul _
  have hB_zero : ∫ z, (Rm x z * Omega z) * Omega x ∂volume = 0 := by
    rw [integral_mul_const, hRm_zero, zero_mul]
  have hC_zero : ∫ z, Omega x * (Omega z * Rn z x) ∂volume = 0 := by
    rw [integral_const_mul]
    have hcol_zero : ∫ z, Omega z * Rn z x ∂volume = 0 := by
      calc
        (∫ z, Omega z * Rn z x ∂volume) =
            ∫ z, Rn x z * Omega z ∂volume := by
          refine integral_congr_ae (.of_forall fun z => ?_)
          rw [asymNormalizedTransferKernelRemainder_symm
            (Nt := Nt) (Ns := Ns) P a mass ha hmass n]
          ring
        _ = 0 := hRn_zero
    rw [hcol_zero, mul_zero]
  have hD_ground : ∫ z, (Omega x * Omega x) * Omega z ^ 2 ∂volume =
      Omega x * Omega x := by
    rw [integral_const_mul, hOmega_sq_int, mul_one]
  have hexpand :
      (∫ z, Km x z * Kn z x ∂volume) =
        (∫ z, Rm x z * Rn z x ∂volume) +
          (∫ z, (Rm x z * Omega z) * Omega x ∂volume) +
          (∫ z, Omega x * (Omega z * Rn z x) ∂volume) +
          ∫ z, (Omega x * Omega x) * Omega z ^ 2 ∂volume := by
    calc
      (∫ z, Km x z * Kn z x ∂volume) =
          ∫ z,
            ((Rm x z * Rn z x) + (Rm x z * Omega z) * Omega x) +
            (Omega x * (Omega z * Rn z x) +
              (Omega x * Omega x) * Omega z ^ 2) ∂volume := by
        refine integral_congr_ae (.of_forall fun z => ?_)
        simp only [Km, Kn, Rm, Rn,
          asymNormalizedTransferKernelRemainder]
        ring
      _ = _ := by
        rw [integral_add (hRR.add hB) (hC.add hD),
          integral_add hRR hB, integral_add hC hD]
  calc
    asymNormalizedTransferKernelRemainder
        (Nt := Nt) (Ns := Ns) P a mass ha hmass (m + n + 1) x x =
        asymNormalizedTransferKernelPower
            (Nt := Nt) (Ns := Ns) P a mass ha hmass (m + n + 1) x x -
          Omega x * Omega x := rfl
    _ = (∫ z, Km x z * Kn z x ∂volume) - Omega x * Omega x := by
      rw [asymNormalizedTransferKernelPower_add_one_comp
        (Nt := Nt) (Ns := Ns) P a mass ha hmass m n x x]
    _ = (∫ z, Rm x z * Rn z x ∂volume) := by
      rw [hexpand, hB_zero, hC_zero, hD_ground]
      ring

end Pphi2
