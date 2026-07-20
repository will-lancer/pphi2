/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.AsymTorus.AsymBandFreeComparison

/-!
# Low-mode projections are temporally band-limited (B2 Stage C, task C1)

Sub-gap spectral projections satisfy the B-II band predicate: if every mode `k ∈ S` has
`λ_k < mass² + κ²` with `κ² ≤ spatialGap Ns a`, then `asymModeProj S G` is
`temporalBandLimited κ` — its temporal DFT coefficients vanish at every 1D temporal mode
`m₁` with `κ² < latticeEigenvalue1d Nt a m₁`.

Route (`planning/b2-stageB-holes-spec.md`, §"Stage C work plan", C1): the two-eigenvalue
pairing trick of Stage A.  Each eigenvector `e_k` with `k ∈ S` is slice-constant
(`massEigenvectorBasisAsym_sliceConstant_of_lt`), so on `e_k` the spatial stencil of the
2D eigen-equation vanishes pointwise and the temporal profile `c_k(t) = e_k(t, 0)` solves
the 1D temporal eigen-equation at eigenvalue `λ_k − mass²`.  Pairing that 1D eigen-equation
against the 1D DFT basis function `φ_{m₁}` via the stencil transfer `oneDim_stencil_coeff`
(size-generic, instantiated at `Nt`) yields
`(λ¹ᵈ_{m₁} − (λ_k − mass²))·⟨c_k, φ_{m₁}⟩ = 0`; on the band `λ¹ᵈ_{m₁} > κ² > λ_k − mass²`
the factor is positive, so the coefficient vanishes.  Linearity of `temporalCoeff` in the
field finishes: the projection is a finite sum of eigenvectors with vanishing coefficients.

## Main results

- `temporal_stencil_of_sliceConstant_eigen` — the temporal profile of a slice-constant
  eigenvector solves the 1D temporal eigen-equation at eigenvalue `λ − mass²`.
- `temporalPairing_eq_zero_of_sliceConstant_eigen` — two-eigenvalue pairing: the temporal
  DFT coefficient of a slice-constant `λ`-eigenvector vanishes at 1D modes with
  `λ¹ᵈ_{m₁} > λ − mass²`.
- `asymModeProj_temporalBandLimited` — **C1 target**: sub-`κ²` spectral projections are
  `temporalBandLimited κ`.
-/

noncomputable section

open GaussianField

namespace Pphi2

/-! ## The 1D temporal eigen-equation for slice-constant eigenvectors -/

/-- **Temporal eigen-equation extraction.** For a slice-constant `lam`-eigenvector `v` of
the mass operator, the spatial stencil vanishes pointwise, so the temporal profile
`t ↦ v (t, 0)` solves the 1D temporal eigen-equation at eigenvalue `lam − mass²`:
`-(a⁻²·(c(t+1) + c(t−1) − 2·c(t))) = (lam − mass²)·c(t)`. -/
theorem temporal_stencil_of_sliceConstant_eigen (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (v : AsymLatticeField Nt Ns)
    (hsc : ∀ (t : ZMod Nt) (s s' : ZMod Ns), v (t, s) = v (t, s')) (lam : ℝ)
    (hv : ∀ x, massOperatorAsym Nt Ns a mass v x = lam * v x) (t : ZMod Nt) :
    -(a⁻¹ ^ 2 * (v (t + 1, 0) + v (t - 1, 0) - 2 * v (t, 0))) =
      (lam - mass ^ 2) * v (t, 0) := by
  have hsplit := massOperatorAsym_stencil_split Nt Ns a mass v t 0
  rw [hv (t, 0)] at hsplit
  have h1 : v (t, (0 : ZMod Ns) + 1) = v (t, 0) := hsc t _ _
  have h2 : v (t, (0 : ZMod Ns) - 1) = v (t, 0) := hsc t _ _
  rw [h1, h2] at hsplit
  linear_combination -hsplit

/-! ## Two-eigenvalue pairing against the temporal DFT basis -/

/-- **Two-eigenvalue pairing.** The temporal DFT coefficient of (the profile of) a
slice-constant `lam`-eigenvector of the mass operator vanishes at every 1D temporal mode
`m₁` whose lattice eigenvalue exceeds `lam − mass²`: pairing the 1D temporal eigen-equation
against `φ_{m₁}` gives `(λ¹ᵈ_{m₁} − (lam − mass²))·⟨c, φ_{m₁}⟩ = 0` with nonzero factor. -/
theorem temporalPairing_eq_zero_of_sliceConstant_eigen (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (v : AsymLatticeField Nt Ns)
    (hsc : ∀ (t : ZMod Nt) (s s' : ZMod Ns), v (t, s) = v (t, s')) (lam : ℝ)
    (hv : ∀ x, massOperatorAsym Nt Ns a mass v x = lam * v x)
    (m₁ : ℕ) (hm₁ : m₁ < Nt) (hband : lam - mass ^ 2 < latticeEigenvalue1d Nt a m₁) :
    ∑ t : ZMod Nt, v (t, 0) * latticeFourierBasisFun Nt m₁ t = 0 := by
  have hpair := oneDim_stencil_coeff Nt a ha.ne' (fun t => v (t, 0)) m₁ hm₁
  have hstencil : ∀ t : ZMod Nt,
      (-(a⁻¹ ^ 2 * (v (t + 1, 0) + v (t - 1, 0) - 2 * v (t, 0)))) *
          latticeFourierBasisFun Nt m₁ t =
        (lam - mass ^ 2) * (v (t, 0) * latticeFourierBasisFun Nt m₁ t) := fun t => by
    rw [temporal_stencil_of_sliceConstant_eigen Nt Ns a mass v hsc lam hv t]
    ring
  simp only [hstencil, ← Finset.mul_sum] at hpair
  have hfactor : (latticeEigenvalue1d Nt a m₁ - (lam - mass ^ 2)) *
      ∑ t : ZMod Nt, v (t, 0) * latticeFourierBasisFun Nt m₁ t = 0 := by
    linear_combination -hpair
  exact (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hband.ne')

/-! ## The C1 target: sub-gap projections are temporally band-limited -/

/-- **C1: low-mode projections are temporally band-limited.** If every mode `k ∈ S` has
eigenvalue `λ_k < mass² + κ²` with `κ² ≤ spatialGap Ns a`, then the spectral projection
`asymModeProj S G` satisfies the B-II band predicate `temporalBandLimited κ`: each
eigenvector in the sum is slice-constant (Stage A) with temporal eigenvalue
`λ_k − mass² < κ²`, so its temporal DFT coefficient vanishes above the band by the
two-eigenvalue pairing, and `temporalCoeff` is linear in the field. -/
theorem asymModeProj_temporalBandLimited (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass κ : ℝ) (ha : 0 < a) (hmass : 0 < mass) (hκ : κ ^ 2 ≤ spatialGap Ns a)
    (S : Finset (AsymLatticeSites Nt Ns))
    (hS : ∀ k ∈ S, massEigenvaluesAsym Nt Ns a mass k < mass ^ 2 + κ ^ 2)
    (G : AsymLatticeField Nt Ns) :
    temporalBandLimited Nt Ns a κ (asymModeProj Nt Ns a mass S G) := by
  intro m₁ hm₁
  unfold temporalCoeff temporalProfile asymModeProj
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k hk => ?_
  have hsc := massEigenvectorBasisAsym_sliceConstant_of_lt Nt Ns a mass ha hmass k
    (lt_of_lt_of_le (hS k hk) (by linarith))
  have hzero := temporalPairing_eq_zero_of_sliceConstant_eigen Nt Ns a mass ha
    (fun y => (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) y) hsc
    (massEigenvaluesAsym Nt Ns a mass k)
    (massOperatorAsym_eigenvectorBasis_apply Nt Ns a mass k)
    (m₁ : ℕ) m₁.isLt (by linarith [hS k hk])
  calc
    ∑ t : ZMod Nt, asymModeCoeff Nt Ns a mass k G *
        (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) (t, 0) *
        latticeFourierBasisFun Nt (m₁ : ℕ) t
      = asymModeCoeff Nt Ns a mass k G * ∑ t : ZMod Nt,
          (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) (t, 0) *
          latticeFourierBasisFun Nt (m₁ : ℕ) t := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by ring
    _ = 0 := by rw [hzero, mul_zero]

end Pphi2

end
