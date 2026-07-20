/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Mathlib.Analysis.PSeries
import Pphi2.AsymTorus.AsymSpatialConstant
import Pphi2.AsymTorus.AsymB5bSingleSlice
import Pphi2.AsymTorus.AsymFreeSpectral

/-!
# Band-limited free-side comparison (B2 Stage B, hole B-II)

For slice-constant, temporally band-limited lattice fields `G`, the sum of one-slice free
covariances is dominated by the full spacetime free variance with a constant depending only
on the spatial circumference `Ls = Ns·a`, the mass, and the band threshold `κ` — uniformly
in the lattice spacing `a` and the number of time slices `Nt`.  This discharges the
`hFreeAssemble` hypothesis of `interacting_second_moment_bound_to_lattice_free_covariance`
on the band (the all-`G` version is false; the band restriction is what makes it close).

Design (`planning/b2-stageB-holes-spec.md`, §"Hole B-II"): never touch the abstract 2D
eigenbasis.  A slice-constant field has a temporal profile `c : ZMod Nt → ℝ`; through the
2D product-DFT form of the free covariance (`abstract_spectral_eq_dft_spectral_2d_asym`)
the spatial factor collapses onto the spatial zero mode, reducing every statement to the 1D
temporal DFT toolkit at size `Nt`.

## Main definitions

- `sliceConstant` — a lattice field is constant along each time slice.
- `temporalProfile`, `temporalCoeff` — the temporal profile of a field and its 1D DFT
  coefficients at size `Nt`.
- `temporalBandLimited` — **T3 predicate**: the temporal DFT coefficients vanish on modes
  with `latticeEigenvalue1d Nt a m₁ > κ²`.
- `bandFreeComparisonConstant` — the final constant `(κ² + mass²)·(4/mass² + 2·Ls/mass)`.

## Main results

- `asymFreeVariance_ge_temporal_spectral_sum` — **T1**: for slice-constant `G` the free
  variance dominates the temporal spectral sum `(a²)⁻¹·Ns·Σ_{m₁} ĉ(m₁)²/((λ_{m₁}+m²)·‖φ_{m₁}‖²)`.
- `freeSingleSliceCovariance_spatialOne_eq` — **T2**: exact evaluation of the one-slice free
  covariance at the constant spatial vector via the temporal DFT.
- `sum_sq_temporalProfile_le_of_band` — **T3**: temporal Parseval plus the band restriction:
  `Σ_t c_t² ≤ (κ²+m²)·(temporal spectral sum)`.
- `sum_inv_latticeEigenvalue1d_add_sq_le` — **T4**: the discrete temporal Green's function
  bound `Σ_{m₁}(λ_{m₁}+m²)⁻¹ ≤ 2/m² + a·Nt/m` (coarse split of the mode sum at `k ≈ m·a·Nt/2`,
  with the temporal zero mode contributing the `2/m²`).
- `freeSingleSliceCovarianceSum_le_freeVariance_of_band` — the **target**:
  `freeSingleSliceCovarianceSum ≤ bandFreeComparisonConstant Ls mass κ · Var_free(G)`.
-/

noncomputable section

open MeasureTheory GaussianField Real
open scoped BigOperators

namespace Pphi2

/-! ## Slice-constant fields and temporal profiles -/

/-- A lattice field is slice-constant when it is constant along each time slice
(Stage A predicate, via `sliceAvgProj_eq_self_iff`). -/
def sliceConstant (Nt Ns : ℕ) (G : AsymLatticeField Nt Ns) : Prop :=
  ∀ (t : ZMod Nt) (s s' : ZMod Ns), G (t, s) = G (t, s')

/-- Slice-constancy is being fixed by the slice-average projector. -/
theorem sliceConstant_iff_sliceAvgProj_eq_self (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (G : AsymLatticeField Nt Ns) :
    sliceConstant Nt Ns G ↔ sliceAvgProj Nt Ns G = G :=
  (sliceAvgProj_eq_self_iff Nt Ns G).symm

/-- The temporal profile of a lattice field: its values along the spatial base point.
For slice-constant fields this is the full data of the field. -/
def temporalProfile (Nt Ns : ℕ) (G : AsymLatticeField Nt Ns) : ZMod Nt → ℝ :=
  fun t => G (t, 0)

theorem sliceConstant_apply (Nt Ns : ℕ) {G : AsymLatticeField Nt Ns}
    (hsc : sliceConstant Nt Ns G) (t : ZMod Nt) (s : ZMod Ns) :
    G (t, s) = temporalProfile Nt Ns G t :=
  hsc t s 0

/-- The `m₁`-th temporal DFT coefficient of (the temporal profile of) a lattice field,
against the 1D lattice Fourier basis at size `Nt`. -/
def temporalCoeff (Nt Ns : ℕ) [NeZero Nt] (m₁ : ℕ) (G : AsymLatticeField Nt Ns) : ℝ :=
  ∑ t : ZMod Nt, temporalProfile Nt Ns G t * latticeFourierBasisFun Nt m₁ t

/-- **T3 band predicate**: the temporal DFT coefficients of `G` vanish on all temporal
modes whose 1D lattice eigenvalue exceeds the threshold `κ²`. -/
def temporalBandLimited (Nt Ns : ℕ) [NeZero Nt] (a κ : ℝ)
    (G : AsymLatticeField Nt Ns) : Prop :=
  ∀ m₁ : Fin Nt, κ ^ 2 < latticeEigenvalue1d Nt a (m₁ : ℕ) →
    temporalCoeff Nt Ns (m₁ : ℕ) G = 0

/-- The constant spatial test vector `𝟙`. -/
def spatialOneField (Ns : ℕ) : SpatialField Ns := fun _ => 1

/-- Applying the inverse slice equivalence pointwise. -/
theorem asymSliceEquiv_symm_apply (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (F : ZMod Nt → SpatialField Ns) (t : ZMod Nt) (s : ZMod Ns) :
    (asymSliceEquiv Nt Ns).symm F (t, s) = F t ((ZMod.finEquiv Ns).toEquiv.symm s) := by
  have h := asymSliceEquiv_apply Nt Ns ((asymSliceEquiv Nt Ns).symm F) t
    ((ZMod.finEquiv Ns).toEquiv.symm s)
  rw [(asymSliceEquiv Nt Ns).apply_symm_apply, Equiv.apply_symm_apply] at h
  exact h.symm

/-- A slice-constant field slices into scalar multiples of the constant spatial vector. -/
theorem asymSliceEquiv_apply_of_sliceConstant (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    {G : AsymLatticeField Nt Ns} (hsc : sliceConstant Nt Ns G) (t : ZMod Nt) :
    (asymSliceEquiv Nt Ns) G t = temporalProfile Nt Ns G t • spatialOneField Ns := by
  funext x
  rw [asymSliceEquiv_apply]
  simp only [Pi.smul_apply, smul_eq_mul, spatialOneField, mul_one]
  exact sliceConstant_apply Nt Ns hsc t _

/-- The one-slice lift of the constant spatial vector is the temporal indicator field. -/
theorem singleSliceLatticeField_spatialOne_apply (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (t : ZMod Nt) (x : AsymLatticeSites Nt Ns) :
    singleSliceLatticeField (Nt := Nt) (Ns := Ns) t (spatialOneField Ns) x =
      if x.1 = t then 1 else 0 := by
  obtain ⟨t', s⟩ := x
  unfold singleSliceLatticeField
  rw [asymSliceEquiv_symm_apply]
  unfold singleSliceFamily spatialOneField
  by_cases h : t' = t <;> simp [h]

/-! ## 1D DFT toolkit additions (temporal direction) -/

/-- The zero-mode 1D lattice Fourier basis function sums to `√N`. -/
theorem sum_latticeFourierBasisFun_zero (N : ℕ) [NeZero N] :
    ∑ z : ZMod N, latticeFourierBasisFun N 0 z = Real.sqrt N := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have h : ∀ z : ZMod N, latticeFourierBasisFun N 0 z = 1 / Real.sqrt N := fun _ => rfl
  simp_rw [h]
  rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one_div,
    Real.div_sqrt]

/-- Nonzero 1D lattice Fourier basis functions sum to zero over the group (orthogonality
against constants): pairing the vanishing stencil of the constant function against `φ_m`
gives `0 = λ_m·Σ_z φ_m(z)` with `λ_m > 0`. -/
theorem sum_latticeFourierBasisFun_eq_zero (N : ℕ) [NeZero N] (m : ℕ)
    (hm1 : 1 ≤ m) (hmN : m < N) :
    ∑ z : ZMod N, latticeFourierBasisFun N m z = 0 := by
  have h := oneDim_stencil_coeff N 1 one_ne_zero (fun _ => (1 : ℝ)) m hmN
  norm_num at h
  -- h : 0 = latticeEigenvalue1d N 1 m * ∑ z, latticeFourierBasisFun N m z
  have hN2 : 2 ≤ N := by omega
  have hgap : 0 < spatialGap N 1 := by
    unfold spatialGap
    have hNr : (0 : ℝ) < N := by positivity
    have h2N : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    have hsin : 0 < Real.sin (π / N) := by
      refine Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_
      calc π / N ≤ π / 2 := by
            apply div_le_div_of_nonneg_left Real.pi_pos.le two_pos h2N
        _ < π := by linarith [Real.pi_pos]
    positivity
  have hev : 0 < latticeEigenvalue1d N 1 m :=
    lt_of_lt_of_le hgap (latticeEigenvalue1d_ge_spatialGap N 1 m hm1 hmN)
  rcases h with h0 | h0
  · exact absurd h0 hev.ne'
  · exact h0

/-- Pointwise square bound on the 1D lattice Fourier basis: `φ_m(z)² ≤ 2/N`. -/
theorem latticeFourierBasisFun_sq_le_two_div (N : ℕ) [NeZero N] (m : ℕ) (z : ZMod N) :
    latticeFourierBasisFun N m z ^ 2 ≤ 2 / N := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  cases m with
  | zero =>
    have h : latticeFourierBasisFun N 0 z = 1 / Real.sqrt N := rfl
    rw [h, div_pow, one_pow, Real.sq_sqrt hN.le]
    gcongr
    norm_num
  | succ n =>
    have h2N : (0 : ℝ) ≤ 2 / N := by positivity
    simp only [latticeFourierBasisFun]
    split
    · rw [mul_pow, Real.sq_sqrt h2N]
      exact mul_le_of_le_one_right h2N (Real.cos_sq_le_one _)
    · rw [mul_pow, Real.sq_sqrt h2N]
      exact mul_le_of_le_one_right h2N (Real.sin_sq_le_one _)

/-! ## T1 — slice-constant reduction of the free variance -/

/-- The 2D DFT coefficient of a slice-constant field against a temporal mode and the
spatial zero mode: the spatial sum contributes `√Ns` and the temporal sum is the temporal
DFT coefficient. -/
theorem asym_dftCoeff_sliceConstant_spatial_zero (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    {G : AsymLatticeField Nt Ns} (hsc : sliceConstant Nt Ns G) (m₁ : ℕ) :
    ∑ x : AsymLatticeSites Nt Ns,
        G x * (latticeFourierBasisFun Nt m₁ x.1 * latticeFourierBasisFun Ns 0 x.2) =
      Real.sqrt Ns * temporalCoeff Nt Ns m₁ G := by
  have hNs : (0 : ℝ) < Ns := Nat.cast_pos.mpr (NeZero.pos Ns)
  have hsqrt_ne : Real.sqrt Ns ≠ 0 := (Real.sqrt_pos.mpr hNs).ne'
  have hφ0 : ∀ s : ZMod Ns, latticeFourierBasisFun Ns 0 s = 1 / Real.sqrt Ns := fun _ => rfl
  rw [sum_factor_asym]
  calc
    ∑ t : ZMod Nt, ∑ s : ZMod Ns,
        G (t, s) * (latticeFourierBasisFun Nt m₁ t * latticeFourierBasisFun Ns 0 s)
      = ∑ t : ZMod Nt, ∑ _s : ZMod Ns,
          temporalProfile Nt Ns G t * latticeFourierBasisFun Nt m₁ t * (1 / Real.sqrt Ns) := by
        refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => ?_
        rw [hφ0 s, sliceConstant_apply Nt Ns hsc t s]
        ring
    _ = ∑ t : ZMod Nt, (Ns : ℝ) *
          (temporalProfile Nt Ns G t * latticeFourierBasisFun Nt m₁ t * (1 / Real.sqrt Ns)) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    _ = Real.sqrt Ns * temporalCoeff Nt Ns m₁ G := by
        unfold temporalCoeff
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        have key : (Ns : ℝ) * (1 / Real.sqrt Ns) = Real.sqrt Ns := by
          rw [mul_one_div, Real.div_sqrt]
        calc
          (Ns : ℝ) * (temporalProfile Nt Ns G t * latticeFourierBasisFun Nt m₁ t *
              (1 / Real.sqrt Ns))
            = ((Ns : ℝ) * (1 / Real.sqrt Ns)) *
                (temporalProfile Nt Ns G t * latticeFourierBasisFun Nt m₁ t) := by ring
          _ = Real.sqrt Ns *
                (temporalProfile Nt Ns G t * latticeFourierBasisFun Nt m₁ t) := by rw [key]

/-- **T1: slice-constant lower bound on the free variance.** For a slice-constant field
`G` with temporal profile `c`, the free variance dominates the spatial-zero-mode block of
the 2D DFT spectral sum, which is the temporal 1D spectral sum with multiplicity `Ns`:
`Var_free(G) ≥ (a²)⁻¹·Ns·Σ_{m₁} ĉ(m₁)²/((λ_{m₁}+mass²)·‖φ_{m₁}‖²)`. -/
theorem asymFreeVariance_ge_temporal_spectral_sum (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    {G : AsymLatticeField Nt Ns} (hsc : sliceConstant Nt Ns G) :
    (a ^ 2 : ℝ)⁻¹ * ((Ns : ℝ) * ∑ m₁ : Fin Nt,
        (temporalCoeff Nt Ns (m₁ : ℕ) G) ^ 2 /
          ((latticeEigenvalue1d Nt a (m₁ : ℕ) + mass ^ 2) *
            latticeFourierNormSq Nt (m₁ : ℕ))) ≤
      ∫ ω : Configuration (AsymLatticeField Nt Ns),
        (ω G) ^ 2 ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) := by
  have hNs : (0 : ℝ) < Ns := Nat.cast_pos.mpr (NeZero.pos Ns)
  have hVar : ∫ ω : Configuration (AsymLatticeField Nt Ns),
      (ω G) ^ 2 ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) =
      (a ^ 2 : ℝ)⁻¹ *
        covariance (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass) G G := by
    calc
      ∫ ω : Configuration (AsymLatticeField Nt Ns),
          (ω G) ^ 2 ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass)
        = ∫ ω : Configuration (AsymLatticeField Nt Ns),
            (ω G) * (ω G) ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) := by
          simp_rw [sq]
      _ = covariance (latticeCovarianceAsymGJ Nt Ns a mass ha hmass) G G :=
          latticeGaussianMeasureAsym_cross_moment Nt Ns a mass ha hmass G G
      _ = (a ^ 2 : ℝ)⁻¹ *
            covariance (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass) G G := by
          unfold GaussianField.covariance
          exact latticeCovarianceAsymGJ_inner_eq_inv_a_sq_spectral Nt Ns a mass ha hmass G
  rw [hVar, abstract_spectral_eq_dft_spectral_2d_asym Nt Ns a mass ha hmass G G]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun m₁ _ => ?_
  have hv0 : ((0 : Fin Ns) : ℕ) = 0 := rfl
  have hterm0 :
      (∑ x : AsymLatticeSites Nt Ns, G x *
          (latticeFourierBasisFun Nt (m₁ : ℕ) x.1 *
            latticeFourierBasisFun Ns ((0 : Fin Ns) : ℕ) x.2)) *
        (∑ x : AsymLatticeSites Nt Ns, G x *
          (latticeFourierBasisFun Nt (m₁ : ℕ) x.1 *
            latticeFourierBasisFun Ns ((0 : Fin Ns) : ℕ) x.2)) /
        ((latticeEigenvalue1d Nt a (m₁ : ℕ) + latticeEigenvalue1d Ns a ((0 : Fin Ns) : ℕ) +
            mass ^ 2) *
          latticeFourierNormSq Nt (m₁ : ℕ) * latticeFourierNormSq Ns ((0 : Fin Ns) : ℕ)) =
      (Ns : ℝ) * ((temporalCoeff Nt Ns (m₁ : ℕ) G) ^ 2 /
        ((latticeEigenvalue1d Nt a (m₁ : ℕ) + mass ^ 2) *
          latticeFourierNormSq Nt (m₁ : ℕ))) := by
    rw [hv0, asym_dftCoeff_sliceConstant_spatial_zero Nt Ns hsc (m₁ : ℕ),
      latticeEigenvalue1d_zero, latticeFourierNormSq_zero, add_zero, mul_one]
    have h : Real.sqrt Ns * temporalCoeff Nt Ns (m₁ : ℕ) G *
        (Real.sqrt Ns * temporalCoeff Nt Ns (m₁ : ℕ) G) =
        (Ns : ℝ) * (temporalCoeff Nt Ns (m₁ : ℕ) G) ^ 2 := by
      rw [show Real.sqrt Ns * temporalCoeff Nt Ns (m₁ : ℕ) G *
          (Real.sqrt Ns * temporalCoeff Nt Ns (m₁ : ℕ) G) =
          (Real.sqrt Ns * Real.sqrt Ns) *
            (temporalCoeff Nt Ns (m₁ : ℕ) G * temporalCoeff Nt Ns (m₁ : ℕ) G) from by ring,
        Real.mul_self_sqrt hNs.le, ← sq]
    rw [h, mul_div_assoc]
  rw [← hterm0]
  have hnonneg : ∀ m₂ : Fin Ns, (0 : ℝ) ≤
      (∑ x : AsymLatticeSites Nt Ns, G x *
          (latticeFourierBasisFun Nt (m₁ : ℕ) x.1 *
            latticeFourierBasisFun Ns (m₂ : ℕ) x.2)) *
        (∑ x : AsymLatticeSites Nt Ns, G x *
          (latticeFourierBasisFun Nt (m₁ : ℕ) x.1 *
            latticeFourierBasisFun Ns (m₂ : ℕ) x.2)) /
        ((latticeEigenvalue1d Nt a (m₁ : ℕ) + latticeEigenvalue1d Ns a (m₂ : ℕ) +
            mass ^ 2) *
          latticeFourierNormSq Nt (m₁ : ℕ) * latticeFourierNormSq Ns (m₂ : ℕ)) := by
    intro m₂
    refine div_nonneg (mul_self_nonneg _) ?_
    have h1 : 0 ≤ latticeEigenvalue1d Nt a (m₁ : ℕ) + latticeEigenvalue1d Ns a (m₂ : ℕ) +
        mass ^ 2 := by
      have := latticeEigenvalue1d_nonneg Nt a (m₁ : ℕ)
      have := latticeEigenvalue1d_nonneg Ns a (m₂ : ℕ)
      positivity
    have h2 := latticeFourierNormSq_pos Nt (m₁ : ℕ) m₁.isLt
    have h3 := latticeFourierNormSq_pos Ns (m₂ : ℕ) m₂.isLt
    positivity
  exact Finset.single_le_sum (f := fun m₂ : Fin Ns =>
      (∑ x : AsymLatticeSites Nt Ns, G x *
          (latticeFourierBasisFun Nt (m₁ : ℕ) x.1 *
            latticeFourierBasisFun Ns (m₂ : ℕ) x.2)) *
        (∑ x : AsymLatticeSites Nt Ns, G x *
          (latticeFourierBasisFun Nt (m₁ : ℕ) x.1 *
            latticeFourierBasisFun Ns (m₂ : ℕ) x.2)) /
        ((latticeEigenvalue1d Nt a (m₁ : ℕ) + latticeEigenvalue1d Ns a (m₂ : ℕ) +
            mass ^ 2) *
          latticeFourierNormSq Nt (m₁ : ℕ) * latticeFourierNormSq Ns (m₂ : ℕ)))
    (fun m₂ _ => hnonneg m₂) (Finset.mem_univ (0 : Fin Ns))

/-! ## T2 — one-slice free covariance at the constant spatial vector -/

/-- 2D DFT coefficient of the one-slice indicator field: the temporal factor localizes at
`t` and the spatial factor is the full basis sum. -/
theorem singleSlice_dftCoeff (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (t : ZMod Nt) (m₁ m₂ : ℕ) :
    ∑ x : AsymLatticeSites Nt Ns,
        singleSliceLatticeField (Nt := Nt) (Ns := Ns) t (spatialOneField Ns) x *
          (latticeFourierBasisFun Nt m₁ x.1 * latticeFourierBasisFun Ns m₂ x.2) =
      latticeFourierBasisFun Nt m₁ t * ∑ s : ZMod Ns, latticeFourierBasisFun Ns m₂ s := by
  rw [sum_factor_asym]
  calc
    ∑ t' : ZMod Nt, ∑ s : ZMod Ns,
        singleSliceLatticeField (Nt := Nt) (Ns := Ns) t (spatialOneField Ns) (t', s) *
          (latticeFourierBasisFun Nt m₁ t' * latticeFourierBasisFun Ns m₂ s)
      = ∑ t' : ZMod Nt, (if t' = t then
          latticeFourierBasisFun Nt m₁ t' * ∑ s : ZMod Ns, latticeFourierBasisFun Ns m₂ s
        else 0) := by
        refine Finset.sum_congr rfl fun t' _ => ?_
        simp_rw [singleSliceLatticeField_spatialOne_apply]
        by_cases h : t' = t
        · simp only [h, if_true, one_mul]
          rw [Finset.mul_sum]
        · simp [h]
    _ = latticeFourierBasisFun Nt m₁ t * ∑ s : ZMod Ns, latticeFourierBasisFun Ns m₂ s := by
        rw [Finset.sum_ite_eq' Finset.univ t]
        simp

/-- **T2: exact evaluation of the one-slice free covariance at the constant spatial
vector.** The spatial DFT collapses onto the zero mode (multiplicity `Ns`), leaving the
temporal 1D spectral sum weighted by `φ_{m₁}(t)²`. -/
theorem freeSingleSliceCovariance_spatialOne_eq (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) (t : ZMod Nt) :
    freeSingleSliceCovariance (Nt := Nt) (Ns := Ns) a mass ha hmass t (spatialOneField Ns) =
      (a ^ 2 : ℝ)⁻¹ * ((Ns : ℝ) * ∑ m₁ : Fin Nt,
        (latticeFourierBasisFun Nt (m₁ : ℕ) t) ^ 2 /
          ((latticeEigenvalue1d Nt a (m₁ : ℕ) + mass ^ 2) *
            latticeFourierNormSq Nt (m₁ : ℕ))) := by
  have hNs : (0 : ℝ) < Ns := Nat.cast_pos.mpr (NeZero.pos Ns)
  have hcov : freeSingleSliceCovariance (Nt := Nt) (Ns := Ns) a mass ha hmass t
      (spatialOneField Ns) =
      (a ^ 2 : ℝ)⁻¹ * covariance (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass)
        (singleSliceLatticeField (Nt := Nt) (Ns := Ns) t (spatialOneField Ns))
        (singleSliceLatticeField (Nt := Nt) (Ns := Ns) t (spatialOneField Ns)) := by
    unfold freeSingleSliceCovariance GaussianField.covariance
    exact latticeCovarianceAsymGJ_inner_eq_inv_a_sq_spectral Nt Ns a mass ha hmass _
  rw [hcov, abstract_spectral_eq_dft_spectral_2d_asym Nt Ns a mass ha hmass]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m₁ _ => ?_
  rw [Finset.sum_eq_single (0 : Fin Ns)]
  · -- the spatial zero-mode term
    have hv0 : ((0 : Fin Ns) : ℕ) = 0 := rfl
    rw [hv0, singleSlice_dftCoeff Nt Ns t (m₁ : ℕ) 0, sum_latticeFourierBasisFun_zero,
      latticeEigenvalue1d_zero, latticeFourierNormSq_zero, add_zero, mul_one]
    have h : latticeFourierBasisFun Nt (m₁ : ℕ) t * Real.sqrt Ns *
        (latticeFourierBasisFun Nt (m₁ : ℕ) t * Real.sqrt Ns) =
        (Ns : ℝ) * (latticeFourierBasisFun Nt (m₁ : ℕ) t) ^ 2 := by
      rw [show latticeFourierBasisFun Nt (m₁ : ℕ) t * Real.sqrt Ns *
          (latticeFourierBasisFun Nt (m₁ : ℕ) t * Real.sqrt Ns) =
          (Real.sqrt Ns * Real.sqrt Ns) *
            (latticeFourierBasisFun Nt (m₁ : ℕ) t * latticeFourierBasisFun Nt (m₁ : ℕ) t)
          from by ring,
        Real.mul_self_sqrt hNs.le, ← sq]
    rw [h, mul_div_assoc]
  · -- all other spatial modes vanish
    intro m₂ _ hm₂
    have hm₂v : 1 ≤ (m₂ : ℕ) := by
      rcases Nat.eq_zero_or_pos (m₂ : ℕ) with h0 | h1
      · exact absurd (Fin.ext (by simp [h0]) : m₂ = 0) hm₂
      · exact h1
    rw [singleSlice_dftCoeff Nt Ns t (m₁ : ℕ) (m₂ : ℕ),
      sum_latticeFourierBasisFun_eq_zero Ns (m₂ : ℕ) hm₂v m₂.isLt]
    simp
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **T2 upper bound**: the one-slice free covariance at the constant spatial vector is
bounded by `(a²)⁻¹·Ns·(2/Nt)·Σ_{m₁}(λ_{m₁}+mass²)⁻¹`, uniformly in the time slice `t`
(pointwise basis bound `φ_{m₁}(t)² ≤ 2/Nt` and `‖φ_{m₁}‖² ≥ 1`). -/
theorem freeSingleSliceCovariance_spatialOne_le (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) (t : ZMod Nt) :
    freeSingleSliceCovariance (Nt := Nt) (Ns := Ns) a mass ha hmass t (spatialOneField Ns) ≤
      (a ^ 2 : ℝ)⁻¹ * ((Ns : ℝ) * ((2 / (Nt : ℝ)) *
        ∑ m₁ : Fin Nt, (latticeEigenvalue1d Nt a (m₁ : ℕ) + mass ^ 2)⁻¹)) := by
  rw [freeSingleSliceCovariance_spatialOne_eq Nt Ns a mass ha hmass t]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun m₁ _ => ?_
  have hden : 0 < latticeEigenvalue1d Nt a (m₁ : ℕ) + mass ^ 2 := by
    have := latticeEigenvalue1d_nonneg Nt a (m₁ : ℕ)
    positivity
  have hNS1 : 1 ≤ latticeFourierNormSq Nt (m₁ : ℕ) :=
    latticeFourierNormSq_ge_one Nt (m₁ : ℕ) m₁.isLt
  have hφ : (latticeFourierBasisFun Nt (m₁ : ℕ) t) ^ 2 ≤ 2 / (Nt : ℝ) :=
    latticeFourierBasisFun_sq_le_two_div Nt (m₁ : ℕ) t
  calc
    (latticeFourierBasisFun Nt (m₁ : ℕ) t) ^ 2 /
        ((latticeEigenvalue1d Nt a (m₁ : ℕ) + mass ^ 2) * latticeFourierNormSq Nt (m₁ : ℕ))
      ≤ (2 / (Nt : ℝ)) /
          ((latticeEigenvalue1d Nt a (m₁ : ℕ) + mass ^ 2) * 1) := by
        apply div_le_div₀ (by positivity) hφ (by positivity)
        exact mul_le_mul_of_nonneg_left hNS1 hden.le
    _ = 2 / (Nt : ℝ) * (latticeEigenvalue1d Nt a (m₁ : ℕ) + mass ^ 2)⁻¹ := by
        rw [mul_one, div_eq_mul_inv]

/-! ## T3 — temporal Parseval and the band restriction -/

/-- **T3: band-limited Parseval lower bound.** The squared temporal profile is controlled
by the temporal spectral sum: Parseval converts `Σ_t c_t²` into `Σ_{m₁} ĉ(m₁)²/‖φ_{m₁}‖²`,
and on the band every surviving mode has `λ_{m₁} ≤ κ²`, hence
`1 ≤ (κ²+mass²)·(λ_{m₁}+mass²)⁻¹`. -/
theorem sum_sq_temporalProfile_le_of_band (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass κ : ℝ) (hmass : 0 < mass)
    {G : AsymLatticeField Nt Ns} (hband : temporalBandLimited Nt Ns a κ G) :
    ∑ t : ZMod Nt, (temporalProfile Nt Ns G t) ^ 2 ≤
      (κ ^ 2 + mass ^ 2) * ∑ m₁ : Fin Nt,
        (temporalCoeff Nt Ns (m₁ : ℕ) G) ^ 2 /
          ((latticeEigenvalue1d Nt a (m₁ : ℕ) + mass ^ 2) *
            latticeFourierNormSq Nt (m₁ : ℕ)) := by
  have hparseval : ∑ t : ZMod Nt, (temporalProfile Nt Ns G t) ^ 2 =
      ∑ m₁ : Fin Nt, (temporalCoeff Nt Ns (m₁ : ℕ) G) ^ 2 /
        latticeFourierNormSq Nt (m₁ : ℕ) := by
    unfold temporalCoeff
    simp_rw [pow_two]
    exact dft_parseval_1d Nt (temporalProfile Nt Ns G) (temporalProfile Nt Ns G)
  rw [hparseval, Finset.mul_sum]
  refine Finset.sum_le_sum fun m₁ _ => ?_
  by_cases hc : temporalCoeff Nt Ns (m₁ : ℕ) G = 0
  · rw [hc]
    simp
  · have hlam : latticeEigenvalue1d Nt a (m₁ : ℕ) ≤ κ ^ 2 := by
      by_contra hlt
      push Not at hlt
      exact hc (hband m₁ hlt)
    have hNS : 0 < latticeFourierNormSq Nt (m₁ : ℕ) :=
      latticeFourierNormSq_pos Nt (m₁ : ℕ) m₁.isLt
    have hden : 0 < latticeEigenvalue1d Nt a (m₁ : ℕ) + mass ^ 2 := by
      have := latticeEigenvalue1d_nonneg Nt a (m₁ : ℕ)
      positivity
    have hfrac : (1 : ℝ) ≤ (κ ^ 2 + mass ^ 2) /
        (latticeEigenvalue1d Nt a (m₁ : ℕ) + mass ^ 2) := by
      rw [le_div_iff₀ hden, one_mul]
      linarith
    have key : (1 : ℝ) / latticeFourierNormSq Nt (m₁ : ℕ) ≤
        (κ ^ 2 + mass ^ 2) /
          ((latticeEigenvalue1d Nt a (m₁ : ℕ) + mass ^ 2) *
            latticeFourierNormSq Nt (m₁ : ℕ)) := by
      calc
        (1 : ℝ) / latticeFourierNormSq Nt (m₁ : ℕ)
          = 1 * (1 / latticeFourierNormSq Nt (m₁ : ℕ)) := (one_mul _).symm
        _ ≤ ((κ ^ 2 + mass ^ 2) / (latticeEigenvalue1d Nt a (m₁ : ℕ) + mass ^ 2)) *
              (1 / latticeFourierNormSq Nt (m₁ : ℕ)) :=
            mul_le_mul_of_nonneg_right hfrac (by positivity)
        _ = (κ ^ 2 + mass ^ 2) /
              ((latticeEigenvalue1d Nt a (m₁ : ℕ) + mass ^ 2) *
                latticeFourierNormSq Nt (m₁ : ℕ)) := by
            rw [div_mul_div_comm, mul_one]
    calc
      (temporalCoeff Nt Ns (m₁ : ℕ) G) ^ 2 / latticeFourierNormSq Nt (m₁ : ℕ)
        = (temporalCoeff Nt Ns (m₁ : ℕ) G) ^ 2 *
            ((1 : ℝ) / latticeFourierNormSq Nt (m₁ : ℕ)) := by ring
      _ ≤ (temporalCoeff Nt Ns (m₁ : ℕ) G) ^ 2 *
            ((κ ^ 2 + mass ^ 2) /
              ((latticeEigenvalue1d Nt a (m₁ : ℕ) + mass ^ 2) *
                latticeFourierNormSq Nt (m₁ : ℕ))) :=
          mul_le_mul_of_nonneg_left key (sq_nonneg _)
      _ = (κ ^ 2 + mass ^ 2) * ((temporalCoeff Nt Ns (m₁ : ℕ) G) ^ 2 /
            ((latticeEigenvalue1d Nt a (m₁ : ℕ) + mass ^ 2) *
              latticeFourierNormSq Nt (m₁ : ℕ))) := by ring

/-! ## T4 — the discrete temporal Green's function bound -/

/-- Quadratic lower bound on nonzero 1D lattice eigenvalues: for `1 ≤ m < N`,
`λ_m ≥ (2/(a·N))²·m²`. Jordan's inequality `sin x ≥ (2/π)·x` on `[0, π/2]` plus
`fourierFreq m ≥ m/2`. -/
theorem latticeEigenvalue1d_ge_quadratic (N : ℕ) (a : ℝ) (ha : 0 < a) (m : ℕ)
    (hm1 : 1 ≤ m) (hmN : m < N) :
    (2 / (a * N)) ^ 2 * (m : ℝ) ^ 2 ≤ latticeEigenvalue1d N a m := by
  unfold latticeEigenvalue1d
  set k := SmoothMap_Circle.fourierFreq m with hk_def
  have hN2 : 2 ≤ N := by omega
  have hk1 : 1 ≤ k := by
    cases m with
    | zero => omega
    | succ n => simp only [hk_def, SmoothMap_Circle.fourierFreq]; omega
  have hk2 : 2 * k ≤ N := by
    cases m with
    | zero => omega
    | succ n => simp only [hk_def, SmoothMap_Circle.fourierFreq]; omega
  have hm2k : m ≤ 2 * k := by
    cases m with
    | zero => omega
    | succ n => simp only [hk_def, SmoothMap_Circle.fourierFreq]; omega
  have hNr : (0 : ℝ) < N := by positivity
  have hk1' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hk2' : 2 * (k : ℝ) ≤ N := by exact_mod_cast hk2
  have hm2k' : (m : ℝ) ≤ 2 * k := by exact_mod_cast hm2k
  have hx0 : 0 ≤ π * k / N := by positivity
  have hx2 : π * k / N ≤ π / 2 := by
    rw [div_le_div_iff₀ hNr two_pos]
    nlinarith [Real.pi_pos]
  have hsin : 2 * (k : ℝ) / N ≤ Real.sin (π * k / N) := by
    have h := Real.mul_le_sin hx0 hx2
    calc 2 * (k : ℝ) / N = 2 / π * (π * k / N) := by
          field_simp
      _ ≤ Real.sin (π * k / N) := h
  have hsq : (2 * (k : ℝ) / N) ^ 2 ≤ Real.sin (π * k / N) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hsin 2
  calc
    (2 / (a * N)) ^ 2 * (m : ℝ) ^ 2 ≤ (2 / (a * N)) ^ 2 * (2 * (k : ℝ)) ^ 2 := by
        have hmn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        have h := pow_le_pow_left₀ hmn hm2k' 2
        exact mul_le_mul_of_nonneg_left h (by positivity)
    _ = 4 / a ^ 2 * (2 * (k : ℝ) / N) ^ 2 := by
        field_simp
        ring
    _ ≤ 4 / a ^ 2 * Real.sin (π * k / N) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)

/-- Coarse split bound for the shifted quadratic inverse sum: for `s, m > 0`,
`Σ_{j<J} (s²(j+1)² + m²)⁻¹ ≤ 2/(s·m) + 1/m²`. Split at `k₀ = ⌊m/s⌋ + 1`: below, each term
is `≤ 1/m²` with at most `k₀` terms; above, each term is `≤ 1/(s²k²)` and the inverse-square
tail is `≤ 1/k₀`. -/
theorem sum_inv_quadratic_add_sq_le (J : ℕ) (s m : ℝ) (hs : 0 < s) (hm : 0 < m) :
    ∑ j ∈ Finset.range J, (s ^ 2 * ((j : ℝ) + 1) ^ 2 + m ^ 2)⁻¹ ≤
      2 / (s * m) + 1 / m ^ 2 := by
  set k₀ : ℕ := ⌊m / s⌋₊ + 1 with hk₀_def
  have hk₀_pos : 0 < k₀ := Nat.succ_pos _
  have hms_pos : 0 < m / s := div_pos hm hs
  have hk₀_ge : m / s ≤ (k₀ : ℝ) := by
    rw [hk₀_def]
    push_cast
    exact (Nat.lt_floor_add_one (m / s)).le
  have hk₀_le : (k₀ : ℝ) ≤ m / s + 1 := by
    rw [hk₀_def]
    push_cast
    have := Nat.floor_le hms_pos.le
    linarith
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range J) (fun j => j + 1 ≤ k₀)]
  have hhead : ∑ j ∈ (Finset.range J).filter (fun j => j + 1 ≤ k₀),
      (s ^ 2 * ((j : ℝ) + 1) ^ 2 + m ^ 2)⁻¹ ≤ (k₀ : ℝ) / m ^ 2 := by
    calc
      ∑ j ∈ (Finset.range J).filter (fun j => j + 1 ≤ k₀),
          (s ^ 2 * ((j : ℝ) + 1) ^ 2 + m ^ 2)⁻¹
        ≤ ∑ _j ∈ (Finset.range J).filter (fun j => j + 1 ≤ k₀), (m ^ 2)⁻¹ := by
          refine Finset.sum_le_sum fun j _ => ?_
          have h1 : (0 : ℝ) < m ^ 2 := by positivity
          have h2 : m ^ 2 ≤ s ^ 2 * ((j : ℝ) + 1) ^ 2 + m ^ 2 := by
            nlinarith [sq_nonneg (s * ((j : ℝ) + 1))]
          exact inv_anti₀ h1 h2
      _ = (((Finset.range J).filter (fun j => j + 1 ≤ k₀)).card : ℝ) * (m ^ 2)⁻¹ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (k₀ : ℝ) * (m ^ 2)⁻¹ := by
          have hsub : (Finset.range J).filter (fun j => j + 1 ≤ k₀) ⊆ Finset.range k₀ := by
            intro j hj
            simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
            omega
          have hcard : (((Finset.range J).filter (fun j => j + 1 ≤ k₀)).card : ℝ) ≤
              (k₀ : ℝ) := by
            have := Finset.card_le_card hsub
            rw [Finset.card_range] at this
            exact_mod_cast this
          exact mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = (k₀ : ℝ) / m ^ 2 := by rw [div_eq_mul_inv]
  have htail : ∑ j ∈ (Finset.range J).filter (fun j => ¬(j + 1 ≤ k₀)),
      (s ^ 2 * ((j : ℝ) + 1) ^ 2 + m ^ 2)⁻¹ ≤ 1 / (s * m) := by
    have hstep : ∑ j ∈ (Finset.range J).filter (fun j => ¬(j + 1 ≤ k₀)),
        (s ^ 2 * ((j : ℝ) + 1) ^ 2 + m ^ 2)⁻¹ ≤
        (s ^ 2)⁻¹ * ∑ j ∈ (Finset.range J).filter (fun j => ¬(j + 1 ≤ k₀)),
          (((j : ℝ) + 1) ^ 2)⁻¹ := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j hj => ?_
      have h1 : (0 : ℝ) < s ^ 2 * ((j : ℝ) + 1) ^ 2 := by positivity
      have h2 : s ^ 2 * ((j : ℝ) + 1) ^ 2 ≤ s ^ 2 * ((j : ℝ) + 1) ^ 2 + m ^ 2 := by
        nlinarith
      calc
        (s ^ 2 * ((j : ℝ) + 1) ^ 2 + m ^ 2)⁻¹ ≤ (s ^ 2 * ((j : ℝ) + 1) ^ 2)⁻¹ :=
          inv_anti₀ h1 h2
        _ = (s ^ 2)⁻¹ * (((j : ℝ) + 1) ^ 2)⁻¹ := by rw [mul_inv]
    have htail_sq : ∑ j ∈ (Finset.range J).filter (fun j => ¬(j + 1 ≤ k₀)),
        (((j : ℝ) + 1) ^ 2)⁻¹ ≤ (k₀ : ℝ)⁻¹ := by
      have himg : ∑ j ∈ (Finset.range J).filter (fun j => ¬(j + 1 ≤ k₀)),
          (((j : ℝ) + 1) ^ 2)⁻¹ =
          ∑ i ∈ ((Finset.range J).filter (fun j => ¬(j + 1 ≤ k₀))).image (· + 1),
            (((i : ℕ) : ℝ) ^ 2)⁻¹ := by
        rw [Finset.sum_image (fun x _ y _ h => by omega)]
        push_cast
        rfl
      rw [himg]
      have hsub : ((Finset.range J).filter (fun j => ¬(j + 1 ≤ k₀))).image (· + 1) ⊆
          Finset.Ioc k₀ (max k₀ J) := by
        intro i hi
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hi
        obtain ⟨j, ⟨hjJ, hjk⟩, rfl⟩ := hi
        simp only [Finset.mem_Ioc]
        omega
      calc
        ∑ i ∈ ((Finset.range J).filter (fun j => ¬(j + 1 ≤ k₀))).image (· + 1),
            (((i : ℕ) : ℝ) ^ 2)⁻¹
          ≤ ∑ i ∈ Finset.Ioc k₀ (max k₀ J), (((i : ℕ) : ℝ) ^ 2)⁻¹ := by
            refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => by positivity
        _ ≤ (k₀ : ℝ)⁻¹ - ((max k₀ J : ℕ) : ℝ)⁻¹ :=
            sum_Ioc_inv_sq_le_sub hk₀_pos.ne' (le_max_left _ _)
        _ ≤ (k₀ : ℝ)⁻¹ := by
            have : (0 : ℝ) ≤ ((max k₀ J : ℕ) : ℝ)⁻¹ := by positivity
            linarith
    have hk₀_inv : (k₀ : ℝ)⁻¹ ≤ s / m := by
      have h := inv_anti₀ hms_pos hk₀_ge
      rwa [inv_div] at h
    calc
      ∑ j ∈ (Finset.range J).filter (fun j => ¬(j + 1 ≤ k₀)),
          (s ^ 2 * ((j : ℝ) + 1) ^ 2 + m ^ 2)⁻¹
        ≤ (s ^ 2)⁻¹ * ∑ j ∈ (Finset.range J).filter (fun j => ¬(j + 1 ≤ k₀)),
            (((j : ℝ) + 1) ^ 2)⁻¹ := hstep
      _ ≤ (s ^ 2)⁻¹ * (k₀ : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_left htail_sq (by positivity)
      _ ≤ (s ^ 2)⁻¹ * (s / m) :=
          mul_le_mul_of_nonneg_left hk₀_inv (by positivity)
      _ = 1 / (s * m) := by
          field_simp
  have hk₀_div : (k₀ : ℝ) / m ^ 2 ≤ 1 / (s * m) + 1 / m ^ 2 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < m ^ 2)]
    calc (k₀ : ℝ) ≤ m / s + 1 := hk₀_le
      _ = (1 / (s * m) + 1 / m ^ 2) * m ^ 2 := by
          field_simp
  calc
    (∑ j ∈ (Finset.range J).filter (fun j => j + 1 ≤ k₀),
        (s ^ 2 * ((j : ℝ) + 1) ^ 2 + m ^ 2)⁻¹) +
      ∑ j ∈ (Finset.range J).filter (fun j => ¬(j + 1 ≤ k₀)),
        (s ^ 2 * ((j : ℝ) + 1) ^ 2 + m ^ 2)⁻¹
      ≤ (k₀ : ℝ) / m ^ 2 + 1 / (s * m) := add_le_add hhead htail
    _ ≤ (1 / (s * m) + 1 / m ^ 2) + 1 / (s * m) := add_le_add hk₀_div le_rfl
    _ = 2 / (s * m) + 1 / m ^ 2 := by ring

/-- **T4: the discrete temporal Green's function at coinciding times.** The temporal mode
sum of the inverse shifted eigenvalues is bounded by `2/mass² + a·Nt/mass`: the zero mode
contributes `1/mass²`, and the nonzero modes are compared against the quadratic dispersion
`λ_m ≥ (2/(a·Nt))²·m²` and summed by the coarse split. -/
theorem sum_inv_latticeEigenvalue1d_add_sq_le (Nt : ℕ) [NeZero Nt] (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    ∑ m₁ : Fin Nt, (latticeEigenvalue1d Nt a (m₁ : ℕ) + mass ^ 2)⁻¹ ≤
      2 / mass ^ 2 + a * Nt / mass := by
  have hNt : (0 : ℝ) < Nt := Nat.cast_pos.mpr (NeZero.pos Nt)
  set s : ℝ := 2 / (a * Nt) with hs_def
  have hs : 0 < s := by
    rw [hs_def]
    positivity
  obtain ⟨Nt', hNt'⟩ : ∃ n, Nt = n + 1 :=
    ⟨Nt - 1, (Nat.succ_pred_eq_of_pos (NeZero.pos Nt)).symm⟩
  rw [Fin.sum_univ_eq_sum_range (fun m => (latticeEigenvalue1d Nt a m + mass ^ 2)⁻¹) Nt]
  calc
    ∑ m ∈ Finset.range Nt, (latticeEigenvalue1d Nt a m + mass ^ 2)⁻¹
      = (∑ j ∈ Finset.range Nt', (latticeEigenvalue1d Nt a (j + 1) + mass ^ 2)⁻¹) +
          (latticeEigenvalue1d Nt a 0 + mass ^ 2)⁻¹ := by
        rw [hNt', Finset.sum_range_succ']
    _ ≤ (∑ j ∈ Finset.range Nt', (s ^ 2 * ((j : ℝ) + 1) ^ 2 + mass ^ 2)⁻¹) +
          (mass ^ 2)⁻¹ := by
        refine add_le_add (Finset.sum_le_sum fun j hj => ?_) ?_
        · have hjNt : j + 1 < Nt := by
            rw [hNt']
            exact Nat.succ_lt_succ (Finset.mem_range.mp hj)
          have hev := latticeEigenvalue1d_ge_quadratic Nt a ha (j + 1)
            (Nat.le_add_left 1 j) hjNt
          have h1 : (0 : ℝ) < s ^ 2 * ((j : ℝ) + 1) ^ 2 + mass ^ 2 := by positivity
          refine inv_anti₀ h1 ?_
          have : s ^ 2 * ((j : ℝ) + 1) ^ 2 = (2 / (a * Nt)) ^ 2 * ((j + 1 : ℕ) : ℝ) ^ 2 := by
            rw [hs_def]
            push_cast
            ring
          rw [this]
          linarith [hev]
        · rw [latticeEigenvalue1d_zero, zero_add]
    _ ≤ (2 / (s * mass) + 1 / mass ^ 2) + (mass ^ 2)⁻¹ :=
        add_le_add (sum_inv_quadratic_add_sq_le Nt' s mass hs hmass) le_rfl
    _ = 2 / mass ^ 2 + a * Nt / mass := by
        rw [hs_def]
        field_simp
        ring

/-! ## The band-limited free-side comparison -/

/-- The band comparison constant `C_band(Ls, mass, κ) = (κ² + mass²)·(4/mass² + 2·Ls/mass)`,
uniform in the lattice spacing `a` and the number of time slices `Nt` at fixed spatial
circumference `Ls = Ns·a`. -/
def bandFreeComparisonConstant (Ls mass κ : ℝ) : ℝ :=
  (κ ^ 2 + mass ^ 2) * (4 / mass ^ 2 + 2 * Ls / mass)

/-- Sharp (per-instance) form of the band-limited free-side comparison, with the
`(a, Nt)`-dependent coefficient `(κ²+mass²)·(4/(Nt·mass²) + 2·a/mass)`. Note that the
coefficient vanishes as `a → 0`, `Nt → ∞`. -/
theorem freeSingleSliceCovarianceSum_le_freeVariance_of_band_sharp
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (κ : ℝ) (G : AsymLatticeField Nt Ns) (hsc : sliceConstant Nt Ns G)
    (hband : temporalBandLimited Nt Ns a κ G) :
    freeSingleSliceCovarianceSum (Nt := Nt) (Ns := Ns) a mass ha hmass
        ((asymSliceEquiv Nt Ns) G) ≤
      ((κ ^ 2 + mass ^ 2) * (4 / ((Nt : ℝ) * mass ^ 2) + 2 * a / mass)) *
        ∫ ω : Configuration (AsymLatticeField Nt Ns),
          (ω G) ^ 2 ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) := by
  have hNt : (0 : ℝ) < Nt := Nat.cast_pos.mpr (NeZero.pos Nt)
  have hNs : (0 : ℝ) < Ns := Nat.cast_pos.mpr (NeZero.pos Ns)
  set TS : ℝ := ∑ m₁ : Fin Nt,
      (temporalCoeff Nt Ns (m₁ : ℕ) G) ^ 2 /
        ((latticeEigenvalue1d Nt a (m₁ : ℕ) + mass ^ 2) *
          latticeFourierNormSq Nt (m₁ : ℕ)) with hTS_def
  set S₄ : ℝ := ∑ m₁ : Fin Nt, (latticeEigenvalue1d Nt a (m₁ : ℕ) + mass ^ 2)⁻¹
    with hS₄_def
  set Var : ℝ := ∫ ω : Configuration (AsymLatticeField Nt Ns),
      (ω G) ^ 2 ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) with hVar_def
  have hTS_nonneg : 0 ≤ TS := by
    rw [hTS_def]
    refine Finset.sum_nonneg fun m₁ _ => ?_
    have h1 : 0 ≤ latticeEigenvalue1d Nt a (m₁ : ℕ) + mass ^ 2 := by
      have := latticeEigenvalue1d_nonneg Nt a (m₁ : ℕ)
      positivity
    have h2 := latticeFourierNormSq_pos Nt (m₁ : ℕ) m₁.isLt
    positivity
  have hS₄_nonneg : 0 ≤ S₄ := by
    rw [hS₄_def]
    refine Finset.sum_nonneg fun m₁ _ => ?_
    have := latticeEigenvalue1d_nonneg Nt a (m₁ : ℕ)
    positivity
  -- Step 1 (T2): the covariance sum factorizes through the temporal profile
  have h1 : freeSingleSliceCovarianceSum (Nt := Nt) (Ns := Ns) a mass ha hmass
      ((asymSliceEquiv Nt Ns) G) ≤
      (∑ t : ZMod Nt, (temporalProfile Nt Ns G t) ^ 2) *
        ((a ^ 2 : ℝ)⁻¹ * ((Ns : ℝ) * ((2 / (Nt : ℝ)) * S₄))) := by
    unfold freeSingleSliceCovarianceSum
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun t _ => ?_
    rw [asymSliceEquiv_apply_of_sliceConstant Nt Ns hsc t,
      freeSingleSliceCovariance_smul (Nt := Nt) (Ns := Ns) a mass ha hmass t _ _]
    exact mul_le_mul_of_nonneg_left
      (freeSingleSliceCovariance_spatialOne_le Nt Ns a mass ha hmass t) (sq_nonneg _)
  -- Step 2 (T3): the profile sum is band-controlled by the temporal spectral sum
  have h2 : ∑ t : ZMod Nt, (temporalProfile Nt Ns G t) ^ 2 ≤ (κ ^ 2 + mass ^ 2) * TS :=
    sum_sq_temporalProfile_le_of_band Nt Ns a mass κ hmass hband
  -- Step 3 (T1): the temporal spectral sum is dominated by the free variance
  have h3 : (a ^ 2 : ℝ)⁻¹ * ((Ns : ℝ) * TS) ≤ Var :=
    asymFreeVariance_ge_temporal_spectral_sum Nt Ns a mass ha hmass hsc
  -- Step 4 (T4): the temporal Green's function bound
  have h4 : S₄ ≤ 2 / mass ^ 2 + a * Nt / mass :=
    sum_inv_latticeEigenvalue1d_add_sq_le Nt a mass ha hmass
  -- Combine
  have hκm : 0 ≤ κ ^ 2 + mass ^ 2 := by positivity
  have hVar_nonneg : 0 ≤ Var := by
    rw [hVar_def]
    exact integral_nonneg fun ω => sq_nonneg _
  calc
    freeSingleSliceCovarianceSum (Nt := Nt) (Ns := Ns) a mass ha hmass
        ((asymSliceEquiv Nt Ns) G)
      ≤ (∑ t : ZMod Nt, (temporalProfile Nt Ns G t) ^ 2) *
          ((a ^ 2 : ℝ)⁻¹ * ((Ns : ℝ) * ((2 / (Nt : ℝ)) * S₄))) := h1
    _ ≤ ((κ ^ 2 + mass ^ 2) * TS) *
          ((a ^ 2 : ℝ)⁻¹ * ((Ns : ℝ) * ((2 / (Nt : ℝ)) * S₄))) := by
        exact mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = ((κ ^ 2 + mass ^ 2) * ((2 / (Nt : ℝ)) * S₄)) *
          ((a ^ 2 : ℝ)⁻¹ * ((Ns : ℝ) * TS)) := by ring
    _ ≤ ((κ ^ 2 + mass ^ 2) * ((2 / (Nt : ℝ)) * S₄)) * Var := by
        refine mul_le_mul_of_nonneg_left h3 ?_
        positivity
    _ ≤ ((κ ^ 2 + mass ^ 2) * ((2 / (Nt : ℝ)) * (2 / mass ^ 2 + a * Nt / mass))) * Var := by
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left h4 (by positivity)) hκm) hVar_nonneg
    _ = ((κ ^ 2 + mass ^ 2) * (4 / ((Nt : ℝ) * mass ^ 2) + 2 * a / mass)) * Var := by
        have h : (2 / (Nt : ℝ)) * (2 / mass ^ 2 + a * Nt / mass) =
            4 / ((Nt : ℝ) * mass ^ 2) + 2 * a / mass := by
          field_simp
          ring
        rw [h]

/-- **Hole B-II target: band-limited free-side comparison.** For a slice-constant,
temporally `κ`-band-limited lattice field `G`, the sum of one-slice free covariances of
its slice profiles is bounded by `bandFreeComparisonConstant Ls mass κ` times the free
spacetime variance of `G`, uniformly in `(a, Nt)` at fixed spatial circumference
`Ls = Ns·a`. This discharges the `hFreeAssemble` hypothesis of
`interacting_second_moment_bound_to_lattice_free_covariance` on the band. -/
theorem freeSingleSliceCovarianceSum_le_freeVariance_of_band
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass Ls : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (hLs : (Ns : ℝ) * a = Ls) (κ : ℝ) (_hκ : 0 < κ)
    (G : AsymLatticeField Nt Ns) (hsc : sliceConstant Nt Ns G)
    (hband : temporalBandLimited Nt Ns a κ G) :
    freeSingleSliceCovarianceSum (Nt := Nt) (Ns := Ns) a mass ha hmass
        ((asymSliceEquiv Nt Ns) G) ≤
      bandFreeComparisonConstant Ls mass κ *
        ∫ ω : Configuration (AsymLatticeField Nt Ns),
          (ω G) ^ 2 ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) := by
  have hNt1 : (1 : ℝ) ≤ (Nt : ℝ) := by exact_mod_cast NeZero.one_le
  have hNs1 : (1 : ℝ) ≤ (Ns : ℝ) := by exact_mod_cast NeZero.one_le
  have ha_le : a ≤ Ls := by
    calc a = 1 * a := (one_mul a).symm
      _ ≤ (Ns : ℝ) * a := mul_le_mul_of_nonneg_right hNs1 ha.le
      _ = Ls := hLs
  have hVar_nonneg : 0 ≤ ∫ ω : Configuration (AsymLatticeField Nt Ns),
      (ω G) ^ 2 ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) :=
    integral_nonneg fun ω => sq_nonneg _
  refine (freeSingleSliceCovarianceSum_le_freeVariance_of_band_sharp
    Nt Ns a mass ha hmass κ G hsc hband).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ hVar_nonneg
  unfold bandFreeComparisonConstant
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine add_le_add ?_ ?_
  · -- 4/(Nt·mass²) ≤ 4/mass²
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg mass]
  · -- 2a/mass ≤ 2·Ls/mass
    gcongr

end Pphi2

end
