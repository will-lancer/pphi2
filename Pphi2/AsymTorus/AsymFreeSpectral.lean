/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Free-side spectral toolkit on the asymmetric lattice (B2 S4)

The free-measure spectral/DFT layer consumed by the B2 route (a) band-split master lemma
(`planning/b2-route-a-statements.md`, §S4). Everything here is about the *Gaussian* lattice
measure `latticeGaussianMeasureAsym` and the proved Hermitian eigenbasis
`massEigenvectorBasisAsym` — no interacting-measure input.

## Main definitions

- `asymModeCoeff` — the coefficient `c_k(G) = Σ_x e_k(x)·G(x)` of a lattice field in the
  mass-operator eigenbasis.
- `asymModeProj` — the spectral projection of a lattice field onto a finite set of modes.

## Main results

- `asymFreeVariance_eq_spectral_sum` — the free variance in spectral form:
  `Var_free(G) = (a²)⁻¹·Σ_k λ_k⁻¹·c_k(G)²`.
- `sum_asymModeCoeff_sq` — Parseval: `Σ_k c_k(G)² = Σ_x G(x)²`.
- `asymModeCoeff_proj` — projections are diagonal in mode coefficients.
- `asymModeProj_add_compl` — `G` splits exactly into a mode set and its complement.
- `asymFreeVariance_proj_add` — the free variance is additive across a mode split.
-/

import Pphi2.AsymTorus.AsymWickVariance
import Pphi2.AsymTorus.AsymEnergyFactorization

noncomputable section

open GaussianField MeasureTheory

namespace Pphi2

/-! ## Mode coefficients in the mass-operator eigenbasis -/

/-- The `k`-th coefficient of a lattice field `G` in the mass-operator eigenbasis:
`c_k(G) = Σ_x e_k(x)·G(x)` where `e_k = massEigenvectorBasisAsym Nt Ns a mass k`. -/
def asymModeCoeff (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass : ℝ)
    (k : AsymLatticeSites Nt Ns) (G : AsymLatticeField Nt Ns) : ℝ :=
  ∑ x : AsymLatticeSites Nt Ns,
    (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * G x

/-- Mode coefficients are additive in the field. -/
theorem asymModeCoeff_add (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass : ℝ)
    (k : AsymLatticeSites Nt Ns) (F G : AsymLatticeField Nt Ns) :
    asymModeCoeff Nt Ns a mass k (F + G) =
      asymModeCoeff Nt Ns a mass k F + asymModeCoeff Nt Ns a mass k G := by
  unfold asymModeCoeff
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => by simp [mul_add]

/-- Mode coefficients are homogeneous in the field. -/
theorem asymModeCoeff_smul (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass : ℝ)
    (k : AsymLatticeSites Nt Ns) (c : ℝ) (G : AsymLatticeField Nt Ns) :
    asymModeCoeff Nt Ns a mass k (c • G) = c * asymModeCoeff Nt Ns a mass k G := by
  unfold asymModeCoeff
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by simp [mul_left_comm]

/-- Parseval identity for mode coefficients: `Σ_k c_k(G)² = Σ_x G(x)²`. Specialization of
`massEigenbasisAsym_sum_mul_sum_eq_site_inner` to `f = g = G`. -/
theorem sum_asymModeCoeff_sq (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass : ℝ)
    (G : AsymLatticeField Nt Ns) :
    ∑ k : AsymLatticeSites Nt Ns, (asymModeCoeff Nt Ns a mass k G) ^ 2 =
      ∑ x : AsymLatticeSites Nt Ns, (G x) ^ 2 := by
  simpa [asymModeCoeff, sq] using
    massEigenbasisAsym_sum_mul_sum_eq_site_inner Nt Ns a mass G G

/-! ## The free variance in spectral form -/

/-- **Free variance, spectral form**: the second moment of `ω ↦ ω(G)` under the asymmetric
lattice Gaussian measure is the eigenmode sum `(a²)⁻¹·Σ_k λ_k⁻¹·c_k(G)²`. Chains the proved
identities `latticeGaussianMeasureAsym_cross_moment` (moment = GJ covariance),
`latticeCovarianceAsymGJ_inner_eq_inv_a_sq_spectral` (GJ = `(a²)⁻¹`·spectral) and
`covariance_spectralLatticeCovarianceAsym_eq` (spectral = mode sum). -/
theorem asymFreeVariance_eq_spectral_sum (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) (G : AsymLatticeField Nt Ns) :
    ∫ ω : Configuration (AsymLatticeField Nt Ns),
        (ω G) ^ 2 ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) =
      (a ^ 2 : ℝ)⁻¹ * ∑ k : AsymLatticeSites Nt Ns,
        (massEigenvaluesAsym Nt Ns a mass k)⁻¹ *
        (∑ x : AsymLatticeSites Nt Ns,
          (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * G x) ^ 2 := by
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
    _ = (a ^ 2 : ℝ)⁻¹ * ∑ k : AsymLatticeSites Nt Ns,
          (massEigenvaluesAsym Nt Ns a mass k)⁻¹ *
          (∑ x : AsymLatticeSites Nt Ns,
            (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * G x) ^ 2 := by
        rw [covariance_spectralLatticeCovarianceAsym_eq Nt Ns a mass ha hmass G G]
        congr 1
        exact Finset.sum_congr rfl fun k _ => by ring

/-- Free variance in terms of `asymModeCoeff` (restatement of
`asymFreeVariance_eq_spectral_sum` through the named coefficient). -/
theorem asymFreeVariance_eq_sum_modeCoeff_sq (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) (G : AsymLatticeField Nt Ns) :
    ∫ ω : Configuration (AsymLatticeField Nt Ns),
        (ω G) ^ 2 ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) =
      (a ^ 2 : ℝ)⁻¹ * ∑ k : AsymLatticeSites Nt Ns,
        (massEigenvaluesAsym Nt Ns a mass k)⁻¹ * (asymModeCoeff Nt Ns a mass k G) ^ 2 :=
  asymFreeVariance_eq_spectral_sum Nt Ns a mass ha hmass G

/-- Every eigenvalue of the asymmetric massive lattice operator is at least
`mass²`.  The two bond contributions in its quadratic form are nonnegative. -/
theorem massEigenvaluesAsym_ge_mass_sq
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (k : AsymLatticeSites Nt Ns) :
    mass ^ 2 ≤ massEigenvaluesAsym Nt Ns a mass k := by
  let e : AsymLatticeField Nt Ns :=
    massEigenvectorBasisAsym Nt Ns a mass k
  have he_norm : ∑ x : AsymLatticeSites Nt Ns, e x ^ 2 = 1 := by
    simpa [e] using massEigenvectorBasisAsym_norm_sq_eq_one Nt Ns a mass k
  have hQe : massOperatorAsym Nt Ns a mass e =
      massEigenvaluesAsym Nt Ns a mass k • e := by
    ext x
    rw [massOperatorAsym_eq_matrix_mulVec Nt Ns a mass e x]
    simpa [massEigenvaluesAsym, massEigenvectorBasisAsym, e] using
      congrFun (Matrix.IsHermitian.mulVec_eigenvectorBasis
        (hA := massOperatorMatrixAsym_isHermitian Nt Ns a mass) k) x
  have hquad := massOperatorAsym_quadratic_form_bonds
    (Nt := Nt) (Ns := Ns) a mass e
  rw [hQe] at hquad
  have htime_nonneg : 0 ≤ a⁻¹ ^ 2 *
      ∑ x : AsymLatticeSites Nt Ns,
        (e (x + ((1 : ZMod Nt), (0 : ZMod Ns))) - e x) ^ 2 :=
    mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun x _ => sq_nonneg _)
  have hspace_nonneg : 0 ≤ a⁻¹ ^ 2 *
      ∑ x : AsymLatticeSites Nt Ns,
        (e (x + ((0 : ZMod Nt), (1 : ZMod Ns))) - e x) ^ 2 :=
    mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun x _ => sq_nonneg _)
  simp only [Pi.smul_apply, smul_eq_mul] at hquad
  have hleft : ∑ x : AsymLatticeSites Nt Ns,
      e x * (massEigenvaluesAsym Nt Ns a mass k * e x) =
      massEigenvaluesAsym Nt Ns a mass k := by
    calc
      ∑ x : AsymLatticeSites Nt Ns,
          e x * (massEigenvaluesAsym Nt Ns a mass k * e x) =
          massEigenvaluesAsym Nt Ns a mass k * ∑ x, e x ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by ring
      _ = massEigenvaluesAsym Nt Ns a mass k := by rw [he_norm, mul_one]
  rw [hleft, he_norm, mul_one] at hquad
  linarith

/-- The free asymmetric-lattice variance is bounded by the counting `ℓ²`
norm with the exact GJ factor `(a²)⁻¹` and the massive spectral factor
`mass⁻²`. -/
theorem asymFreeVariance_le_mass_inv_sq
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (G : AsymLatticeField Nt Ns) :
    ∫ ω : Configuration (AsymLatticeField Nt Ns),
        (ω G) ^ 2 ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) ≤
      (a ^ 2 : ℝ)⁻¹ * mass⁻¹ ^ 2 *
        ∑ x : AsymLatticeSites Nt Ns, G x ^ 2 := by
  rw [asymFreeVariance_eq_sum_modeCoeff_sq
    (Nt := Nt) (Ns := Ns) a mass ha hmass G]
  have hinv_le : ∀ k : AsymLatticeSites Nt Ns,
      (massEigenvaluesAsym Nt Ns a mass k)⁻¹ ≤ mass⁻¹ ^ 2 := by
    intro k
    rw [inv_pow, ← one_div, ← one_div]
    exact div_le_div_of_nonneg_left zero_le_one (sq_pos_of_pos hmass)
      (massEigenvaluesAsym_ge_mass_sq Nt Ns a mass k)
  calc
    (a ^ 2 : ℝ)⁻¹ * ∑ k : AsymLatticeSites Nt Ns,
        (massEigenvaluesAsym Nt Ns a mass k)⁻¹ *
          (asymModeCoeff Nt Ns a mass k G) ^ 2 ≤
      (a ^ 2 : ℝ)⁻¹ * ∑ k : AsymLatticeSites Nt Ns,
        mass⁻¹ ^ 2 * (asymModeCoeff Nt Ns a mass k G) ^ 2 := by
      apply mul_le_mul_of_nonneg_left
      · exact Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_right (hinv_le k) (sq_nonneg _)
      · exact inv_nonneg.mpr (sq_nonneg a)
    _ = (a ^ 2 : ℝ)⁻¹ * mass⁻¹ ^ 2 *
        ∑ k : AsymLatticeSites Nt Ns,
          (asymModeCoeff Nt Ns a mass k G) ^ 2 := by
      rw [Finset.mul_sum]
      ring
    _ = (a ^ 2 : ℝ)⁻¹ * mass⁻¹ ^ 2 *
        ∑ x : AsymLatticeSites Nt Ns, G x ^ 2 := by
      rw [sum_asymModeCoeff_sq (Nt := Nt) (Ns := Ns) a mass G]

/-- Sitewise absolute value does not change the counting `ℓ²` norm, so the
same massive bound applies without identifying `|G|` with a smooth test
function. -/
theorem asymFreeVariance_sitewiseAbs_le_mass_inv_sq
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (G : AsymLatticeField Nt Ns) :
    ∫ ω : Configuration (AsymLatticeField Nt Ns),
        (ω (fun x => |G x|)) ^ 2
        ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) ≤
      (a ^ 2 : ℝ)⁻¹ * mass⁻¹ ^ 2 *
        ∑ x : AsymLatticeSites Nt Ns, G x ^ 2 := by
  calc
    ∫ ω : Configuration (AsymLatticeField Nt Ns),
        (ω (fun x => |G x|)) ^ 2
        ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) ≤
      (a ^ 2 : ℝ)⁻¹ * mass⁻¹ ^ 2 *
        ∑ x : AsymLatticeSites Nt Ns, |G x| ^ 2 :=
      asymFreeVariance_le_mass_inv_sq Nt Ns a mass ha hmass (fun x => |G x|)
    _ = (a ^ 2 : ℝ)⁻¹ * mass⁻¹ ^ 2 *
        ∑ x : AsymLatticeSites Nt Ns, G x ^ 2 := by
      simp_rw [sq_abs]

/-! ## Spectral projections onto mode sets -/

/-- Orthogonality of the mass-operator eigenbasis in site coordinates:
`Σ_x e_k(x)·e_l(x) = δ_{kl}`. Unfolds the `OrthonormalBasis` inner product. -/
theorem massEigenvectorBasisAsym_orthogonal (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (k l : AsymLatticeSites Nt Ns) :
    ∑ x : AsymLatticeSites Nt Ns,
        (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x *
        (massEigenvectorBasisAsym Nt Ns a mass l : EuclideanSpace ℝ _) x =
      if k = l then 1 else 0 := by
  have h := orthonormal_iff_ite.mp (massEigenvectorBasisAsym Nt Ns a mass).orthonormal k l
  rw [PiLp.inner_apply] at h
  simpa [RCLike.inner_apply, mul_comm] using h

/-- Basis expansion in site coordinates: `Σ_k c_k(G)·e_k(y) = G(y)`. Obtained from the
Parseval bilinear identity paired against the site delta at `y`. -/
theorem sum_asymModeCoeff_mul_eigenvector (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (G : AsymLatticeField Nt Ns) (y : AsymLatticeSites Nt Ns) :
    ∑ k : AsymLatticeSites Nt Ns,
        asymModeCoeff Nt Ns a mass k G *
        (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) y = G y := by
  have h := massEigenbasisAsym_sum_mul_sum_eq_site_inner Nt Ns a mass G
    (asymLatticeDelta Nt Ns y)
  simp_rw [delta_massEigenvectorCoeff_asym Nt Ns a mass _ y] at h
  simpa [asymModeCoeff, asymLatticeDelta] using h

/-- The spectral projection of a lattice field `G` onto the mode set `S`:
`(P_S G)(x) = Σ_{k ∈ S} c_k(G)·e_k(x)`. -/
def asymModeProj (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass : ℝ)
    (S : Finset (AsymLatticeSites Nt Ns)) (G : AsymLatticeField Nt Ns) :
    AsymLatticeField Nt Ns :=
  fun x => ∑ k ∈ S, asymModeCoeff Nt Ns a mass k G *
    (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x

/-- Mode coefficients of a spectral projection: `c_k(P_S G) = c_k(G)` for `k ∈ S`, `0`
otherwise. Eigenbasis orthogonality makes the projection diagonal. -/
theorem asymModeCoeff_proj (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass : ℝ)
    (k : AsymLatticeSites Nt Ns) (S : Finset (AsymLatticeSites Nt Ns))
    (G : AsymLatticeField Nt Ns) :
    asymModeCoeff Nt Ns a mass k (asymModeProj Nt Ns a mass S G) =
      if k ∈ S then asymModeCoeff Nt Ns a mass k G else 0 := by
  unfold asymModeCoeff asymModeProj
  rw [← Finset.sum_ite_eq S k (fun l =>
    ∑ x : AsymLatticeSites Nt Ns,
      (massEigenvectorBasisAsym Nt Ns a mass l : EuclideanSpace ℝ _) x * G x)]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  have horth := massEigenvectorBasisAsym_orthogonal Nt Ns a mass k l
  calc
      ∑ x : AsymLatticeSites Nt Ns,
          (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x *
          ((∑ x' : AsymLatticeSites Nt Ns,
            (massEigenvectorBasisAsym Nt Ns a mass l : EuclideanSpace ℝ _) x' * G x') *
            (massEigenvectorBasisAsym Nt Ns a mass l : EuclideanSpace ℝ _) x)
        = (∑ x' : AsymLatticeSites Nt Ns,
            (massEigenvectorBasisAsym Nt Ns a mass l : EuclideanSpace ℝ _) x' * G x') *
          ∑ x : AsymLatticeSites Nt Ns,
            (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x *
            (massEigenvectorBasisAsym Nt Ns a mass l : EuclideanSpace ℝ _) x := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun x _ => by ring
      _ = if k = l then
            ∑ x' : AsymLatticeSites Nt Ns,
              (massEigenvectorBasisAsym Nt Ns a mass l : EuclideanSpace ℝ _) x' * G x'
          else 0 := by
          rw [horth]
          by_cases hkl : k = l <;> simp [hkl]

/-- A lattice field splits exactly into a mode set and its complement:
`P_S G + P_{Sᶜ} G = G`. -/
theorem asymModeProj_add_compl (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass : ℝ)
    (S : Finset (AsymLatticeSites Nt Ns)) (G : AsymLatticeField Nt Ns) :
    asymModeProj Nt Ns a mass S G + asymModeProj Nt Ns a mass Sᶜ G = G := by
  funext x
  have h := sum_asymModeCoeff_mul_eigenvector Nt Ns a mass G x
  calc
    (asymModeProj Nt Ns a mass S G + asymModeProj Nt Ns a mass Sᶜ G) x
      = ∑ k ∈ S, asymModeCoeff Nt Ns a mass k G *
          (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x +
        ∑ k ∈ Sᶜ, asymModeCoeff Nt Ns a mass k G *
          (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x := rfl
    _ = ∑ k : AsymLatticeSites Nt Ns, asymModeCoeff Nt Ns a mass k G *
          (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x :=
        Finset.sum_add_sum_compl S _
    _ = G x := h

/-- **Free-variance additivity across a mode split**: `Var_free(P_S G) + Var_free(P_{Sᶜ} G)
= Var_free(G)`. The spectral form of the free variance is diagonal in mode coefficients, so
the split is exact (no cross terms). -/
theorem asymFreeVariance_proj_add (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (S : Finset (AsymLatticeSites Nt Ns)) (G : AsymLatticeField Nt Ns) :
    (∫ ω : Configuration (AsymLatticeField Nt Ns),
        (ω (asymModeProj Nt Ns a mass S G)) ^ 2
        ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass)) +
      (∫ ω : Configuration (AsymLatticeField Nt Ns),
        (ω (asymModeProj Nt Ns a mass Sᶜ G)) ^ 2
        ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass)) =
      ∫ ω : Configuration (AsymLatticeField Nt Ns),
        (ω G) ^ 2 ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) := by
  rw [asymFreeVariance_eq_sum_modeCoeff_sq Nt Ns a mass ha hmass
      (asymModeProj Nt Ns a mass S G),
    asymFreeVariance_eq_sum_modeCoeff_sq Nt Ns a mass ha hmass
      (asymModeProj Nt Ns a mass Sᶜ G),
    asymFreeVariance_eq_sum_modeCoeff_sq Nt Ns a mass ha hmass G,
    ← mul_add]
  congr 1
  simp_rw [asymModeCoeff_proj]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : k ∈ S <;> simp [hk]

end Pphi2

end
