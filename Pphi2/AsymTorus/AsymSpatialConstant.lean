/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Sub-gap eigenvectors are spatially constant (B2 Arc-4 Stage A)

The spatially-constant characterization of low modes on the asymmetric lattice
(`planning/b2-route-a-statements.md`, §"Arc-4 staging", Stage A). The slice-average
projector `Π` averages a lattice field over each time slice; it commutes with the mass
operator (the spatial stencil telescopes under spatial averaging), and on its kernel the
quadratic form of `massOperatorAsym` is bounded below by `spatialGap Ns a + mass²`, where
`spatialGap Ns a = (4/a²)·sin²(π/Ns)` is the smallest nonzero eigenvalue of the 1D spatial
Laplacian. Consequently every eigenvector of `massOperatorAsym` with eigenvalue below
`mass² + spatialGap Ns a` is constant along each time slice, and so is the spectral
projection `asymModeProj` onto any sub-gap mode set.

## Main definitions

- `sliceAvgProj` — the linear projector averaging over each time slice.
- `spatialGap` — the 1D spatial Poincaré constant `(4/a²)·sin²(π/Ns)`.

## Main results

- `sliceAvgProj_comm_massOperatorAsym` — `Π` commutes with `-Δ_a + m²`.
- `massOperatorAsym_quadForm_ge_of_sliceAvg_eq_zero` — discrete spatial Poincaré
  inequality: `Π v = 0 → (spatialGap + m²)·Σ v² ≤ ⟨v, (-Δ_a + m²) v⟩`.
- `massEigenvectorBasisAsym_sliceConstant_of_lt` — eigenvectors with
  `λ_k < m² + spatialGap` are slice-constant.
- `asymModeProj_sliceConstant` — spectral projections onto sub-gap mode sets are
  slice-constant.
- `spatialGap_ge_of_fixed_Ls` — at fixed spatial circumference `Ls = Ns·a`,
  `spatialGap Ns a ≥ 16/Ls² ≥ 4/Ls²` uniformly in the lattice spacing.
-/

import Pphi2.AsymTorus.AsymFreeSpectral
import Lattice.CirculantDFT2d

noncomputable section

open GaussianField Real

namespace Pphi2

/-! ## The slice-average projector -/

/-- The slice-average projector: replace a lattice field by its spatial average over each
time slice, `(Π G)(t, s) = Ns⁻¹·∑_{s'} G(t, s')`. -/
def sliceAvgProj (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] :
    AsymLatticeField Nt Ns →ₗ[ℝ] AsymLatticeField Nt Ns where
  toFun G := fun x => (Ns : ℝ)⁻¹ * ∑ s' : ZMod Ns, G (x.1, s')
  map_add' F G := by
    funext x
    simp only [Pi.add_apply, Finset.sum_add_distrib, mul_add]
  map_smul' c G := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
    ring

@[simp] theorem sliceAvgProj_apply (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (G : AsymLatticeField Nt Ns) (x : AsymLatticeSites Nt Ns) :
    sliceAvgProj Nt Ns G x = (Ns : ℝ)⁻¹ * ∑ s' : ZMod Ns, G (x.1, s') :=
  rfl

/-- The slice average at `(t, s)` does not depend on `s`. -/
theorem sliceAvgProj_apply_eq (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (G : AsymLatticeField Nt Ns) (t : ZMod Nt) (s s' : ZMod Ns) :
    sliceAvgProj Nt Ns G (t, s) = sliceAvgProj Nt Ns G (t, s') :=
  rfl

/-- The slice-average projector is idempotent. -/
theorem sliceAvgProj_idem (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (G : AsymLatticeField Nt Ns) :
    sliceAvgProj Nt Ns (sliceAvgProj Nt Ns G) = sliceAvgProj Nt Ns G := by
  have hNs : ((Ns : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne Ns)
  funext x
  calc sliceAvgProj Nt Ns (sliceAvgProj Nt Ns G) x
      = (Ns : ℝ)⁻¹ * ∑ _s' : ZMod Ns, sliceAvgProj Nt Ns G x := rfl
    _ = (Ns : ℝ)⁻¹ * ((Ns : ℝ) * sliceAvgProj Nt Ns G x) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ZMod.card]
    _ = sliceAvgProj Nt Ns G x := inv_mul_cancel_left₀ hNs _

/-- A field is slice-constant iff it is fixed by the slice-average projector. -/
theorem sliceAvgProj_eq_self_iff (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (G : AsymLatticeField Nt Ns) :
    sliceAvgProj Nt Ns G = G ↔
      ∀ (t : ZMod Nt) (s s' : ZMod Ns), G (t, s) = G (t, s') := by
  constructor
  · intro h t s s'
    calc G (t, s) = sliceAvgProj Nt Ns G (t, s) := (congrFun h (t, s)).symm
      _ = sliceAvgProj Nt Ns G (t, s') := rfl
      _ = G (t, s') := congrFun h (t, s')
  · intro hG
    have hNs : ((Ns : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne Ns)
    funext x
    calc sliceAvgProj Nt Ns G x
        = (Ns : ℝ)⁻¹ * ∑ s' : ZMod Ns, G (x.1, s') := rfl
      _ = (Ns : ℝ)⁻¹ * ∑ _s' : ZMod Ns, G (x.1, x.2) :=
          congrArg ((Ns : ℝ)⁻¹ * ·) (Finset.sum_congr rfl fun s' _ => hG x.1 s' x.2)
      _ = (Ns : ℝ)⁻¹ * ((Ns : ℝ) * G (x.1, x.2)) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ZMod.card]
      _ = G (x.1, x.2) := inv_mul_cancel_left₀ hNs _
      _ = G x := by rw [Prod.mk.eta]

/-! ## Commutation with the mass operator -/

/-- Definitional unfolding of the asymmetric lattice Laplacian. -/
theorem finiteLaplacianAsym_apply (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a : ℝ) (f : AsymLatticeField Nt Ns) (x : AsymLatticeSites Nt Ns) :
    finiteLaplacianAsym Nt Ns a f x = finiteLaplacianAsymFun Nt Ns a f x :=
  rfl

/-- The slice-average projector commutes with the lattice Laplacian: the temporal stencil
acts slice-by-slice, and the spatial neighbor terms telescope under spatial averaging. -/
theorem sliceAvgProj_comm_finiteLaplacianAsym (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a : ℝ) (G : AsymLatticeField Nt Ns) :
    finiteLaplacianAsym Nt Ns a (sliceAvgProj Nt Ns G) =
      sliceAvgProj Nt Ns (finiteLaplacianAsym Nt Ns a G) := by
  funext x
  simp only [finiteLaplacianAsym_apply, finiteLaplacianAsymFun, sliceAvgProj_apply]
  have hplus : ∑ s' : ZMod Ns, G (x.1, s' + 1) = ∑ s' : ZMod Ns, G (x.1, s') :=
    Fintype.sum_equiv (Equiv.addRight (1 : ZMod Ns))
      (fun s' => G (x.1, s' + 1)) (fun s' => G (x.1, s')) (fun s' => rfl)
  have hminus : ∑ s' : ZMod Ns, G (x.1, s' - 1) = ∑ s' : ZMod Ns, G (x.1, s') :=
    Fintype.sum_equiv (Equiv.subRight (1 : ZMod Ns))
      (fun s' => G (x.1, s' - 1)) (fun s' => G (x.1, s')) (fun s' => rfl)
  have expand : ∀ s' : ZMod Ns,
      a⁻¹ ^ 2 * (G (x.1 + 1, s') + G (x.1 - 1, s') + G (x.1, s' + 1) + G (x.1, s' - 1) -
        4 * G (x.1, s')) =
      a⁻¹ ^ 2 * G (x.1 + 1, s') + a⁻¹ ^ 2 * G (x.1 - 1, s') + a⁻¹ ^ 2 * G (x.1, s' + 1) +
        a⁻¹ ^ 2 * G (x.1, s' - 1) - 4 * a⁻¹ ^ 2 * G (x.1, s') :=
    fun s' => by ring
  simp_rw [expand, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    hplus, hminus]
  ring

/-- **A2: the slice-average projector commutes with the mass operator.** -/
theorem sliceAvgProj_comm_massOperatorAsym (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (G : AsymLatticeField Nt Ns) :
    massOperatorAsym Nt Ns a mass (sliceAvgProj Nt Ns G) =
      sliceAvgProj Nt Ns (massOperatorAsym Nt Ns a mass G) := by
  have hΔ := sliceAvgProj_comm_finiteLaplacianAsym Nt Ns a G
  funext x
  simp only [massOperatorAsym, ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, Pi.add_apply, Pi.neg_apply,
    Pi.smul_apply, smul_eq_mul, sliceAvgProj_apply]
  rw [congrFun hΔ x, sliceAvgProj_apply, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    ← Finset.mul_sum]
  ring

/-! ## The 1D spectral toolkit on `ZMod N` -/

/-- The 1D spatial Poincaré constant: the smallest nonzero eigenvalue
`(4/a²)·sin²(π/Ns)` of the 1D lattice Laplacian on `ZMod Ns` with spacing `a`. -/
def spatialGap (Ns : ℕ) (a : ℝ) : ℝ := (4 / a ^ 2) * Real.sin (π / Ns) ^ 2

/-- DFT coefficient transfer for the 1D stencil: pairing the discrete Laplacian of `g`
against the `m`-th DFT basis function multiplies the `m`-th coefficient of `g` by the
eigenvalue `λ_m`. -/
theorem oneDim_stencil_coeff (N : ℕ) [NeZero N] (a : ℝ) (ha : a ≠ 0)
    (g : ZMod N → ℝ) (m : ℕ) (hm : m < N) :
    ∑ z : ZMod N, (-(a⁻¹ ^ 2 * (g (z + 1) + g (z - 1) - 2 * g z))) *
        latticeFourierBasisFun N m z =
      latticeEigenvalue1d N a m * ∑ z : ZMod N, g z * latticeFourierBasisFun N m z := by
  have hplus : ∑ z : ZMod N, g (z + 1) * latticeFourierBasisFun N m z =
      ∑ z : ZMod N, g z * latticeFourierBasisFun N m (z - 1) :=
    Fintype.sum_equiv (Equiv.addRight (1 : ZMod N))
      (fun z => g (z + 1) * latticeFourierBasisFun N m z)
      (fun z => g z * latticeFourierBasisFun N m (z - 1))
      (fun z => by simp)
  have hminus : ∑ z : ZMod N, g (z - 1) * latticeFourierBasisFun N m z =
      ∑ z : ZMod N, g z * latticeFourierBasisFun N m (z + 1) :=
    Fintype.sum_equiv (Equiv.subRight (1 : ZMod N))
      (fun z => g (z - 1) * latticeFourierBasisFun N m z)
      (fun z => g z * latticeFourierBasisFun N m (z + 1))
      (fun z => by simp)
  have expand : ∀ z : ZMod N,
      (-(a⁻¹ ^ 2 * (g (z + 1) + g (z - 1) - 2 * g z))) * latticeFourierBasisFun N m z =
      (-(a⁻¹ ^ 2)) * (g (z + 1) * latticeFourierBasisFun N m z) +
        (-(a⁻¹ ^ 2)) * (g (z - 1) * latticeFourierBasisFun N m z) +
        (2 * a⁻¹ ^ 2) * (g z * latticeFourierBasisFun N m z) :=
    fun z => by ring
  have hev : ∀ z : ZMod N,
      latticeEigenvalue1d N a m * (g z * latticeFourierBasisFun N m z) =
      (-(a⁻¹ ^ 2)) * (g z * latticeFourierBasisFun N m (z + 1)) +
        (-(a⁻¹ ^ 2)) * (g z * latticeFourierBasisFun N m (z - 1)) +
        (2 * a⁻¹ ^ 2) * (g z * latticeFourierBasisFun N m z) := by
    intro z
    have h := dft_1d_eigenvalue_pointwise N a ha m hm z
    linear_combination (-(g z)) * h
  rw [Finset.mul_sum]
  simp_rw [expand, hev, Finset.sum_add_distrib, ← Finset.mul_sum, hplus, hminus]
  ring

/-- Spectral form of the 1D stencil quadratic form: `⟨g, -Δ₁ g⟩ = Σ_m λ_m·c_m(g)²/‖φ_m‖²`. -/
theorem oneDim_quadForm_eq_spectral (N : ℕ) [NeZero N] (a : ℝ) (ha : a ≠ 0)
    (g : ZMod N → ℝ) :
    ∑ z : ZMod N, g z * (-(a⁻¹ ^ 2 * (g (z + 1) + g (z - 1) - 2 * g z))) =
      ∑ m : Fin N, latticeEigenvalue1d N a m *
        ((∑ z : ZMod N, g z * latticeFourierBasisFun N m z) ^ 2 /
          latticeFourierNormSq N m) := by
  rw [dft_parseval_1d N g (fun z => -(a⁻¹ ^ 2 * (g (z + 1) + g (z - 1) - 2 * g z)))]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [oneDim_stencil_coeff N a ha g m m.isLt]
  ring

/-- The 1D stencil quadratic form is nonnegative. -/
theorem oneDim_quadForm_nonneg (N : ℕ) [NeZero N] (a : ℝ) (ha : a ≠ 0)
    (g : ZMod N → ℝ) :
    0 ≤ ∑ z : ZMod N, g z * (-(a⁻¹ ^ 2 * (g (z + 1) + g (z - 1) - 2 * g z))) := by
  rw [oneDim_quadForm_eq_spectral N a ha g]
  refine Finset.sum_nonneg fun m _ => ?_
  exact mul_nonneg (latticeEigenvalue1d_nonneg N a m)
    (div_nonneg (sq_nonneg _) (latticeFourierNormSq_pos N m m.isLt).le)

/-- Every nonzero 1D lattice eigenvalue is at least `(4/a²)·sin²(π/N)`: the `fourierFreq`
of a nonzero mode lies in `[1, N/2]`, so its angle lies in `[π/N, π/2]` where `sin` is
monotone. -/
theorem latticeEigenvalue1d_ge_spatialGap (N : ℕ) (a : ℝ) (m : ℕ)
    (hm1 : 1 ≤ m) (hmN : m < N) :
    spatialGap N a ≤ latticeEigenvalue1d N a m := by
  unfold spatialGap latticeEigenvalue1d
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
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
  have hNr : (0 : ℝ) < N := by positivity
  have hk1' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hk2' : 2 * (k : ℝ) ≤ N := by exact_mod_cast hk2
  have h0 : 0 ≤ π / N := by positivity
  have h1 : π / N ≤ π * k / N := by
    rw [div_le_div_iff_of_pos_right hNr]
    nlinarith [Real.pi_pos]
  have h2 : π * k / N ≤ π / 2 := by
    rw [div_le_div_iff₀ hNr two_pos]
    nlinarith [Real.pi_pos]
  have hs : Real.sin (π / N) ≤ Real.sin (π * k / N) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) h2 h1
  have hsin0 : 0 ≤ Real.sin (π / N) := by
    refine Real.sin_nonneg_of_nonneg_of_le_pi h0 ?_
    have h1N : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    calc π / N ≤ π / 1 := by
          apply div_le_div_of_nonneg_left Real.pi_pos.le one_pos h1N
      _ = π := by ring
  exact pow_le_pow_left₀ hsin0 hs 2

/-- **1D discrete Poincaré inequality**: for a zero-average function on `ZMod N`, the
stencil quadratic form dominates `(4/a²)·sin²(π/N)` times the sum of squares. -/
theorem oneDim_poincare (N : ℕ) [NeZero N] (a : ℝ) (ha : 0 < a)
    (g : ZMod N → ℝ) (hg : ∑ z : ZMod N, g z = 0) :
    spatialGap N a * ∑ z : ZMod N, g z ^ 2 ≤
      ∑ z : ZMod N, g z * (-(a⁻¹ ^ 2 * (g (z + 1) + g (z - 1) - 2 * g z))) := by
  rw [oneDim_quadForm_eq_spectral N a ha.ne' g]
  have hsq : ∑ z : ZMod N, g z ^ 2 = ∑ m : Fin N,
      (∑ z : ZMod N, g z * latticeFourierBasisFun N m z) ^ 2 /
        latticeFourierNormSq N m := by
    simp_rw [pow_two]
    exact dft_parseval_1d N g g
  rw [hsq, Finset.mul_sum]
  refine Finset.sum_le_sum fun m _ => ?_
  by_cases hm : (m : ℕ) = 0
  · have hc0 : ∑ z : ZMod N, g z * latticeFourierBasisFun N (m : ℕ) z = 0 := by
      rw [hm]
      simp only [latticeFourierBasisFun]
      rw [← Finset.sum_mul, hg, zero_mul]
    rw [hc0]
    simp
  · exact mul_le_mul_of_nonneg_right
      (latticeEigenvalue1d_ge_spatialGap N a (m : ℕ) (Nat.one_le_iff_ne_zero.mpr hm) m.isLt)
      (div_nonneg (sq_nonneg _) (latticeFourierNormSq_pos N (m : ℕ) m.isLt).le)

/-! ## The 2D spatial Poincaré inequality -/

/-- Pointwise stencil split of the mass operator into temporal, spatial and mass parts. -/
theorem massOperatorAsym_stencil_split (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (v : AsymLatticeField Nt Ns) (t : ZMod Nt) (s : ZMod Ns) :
    massOperatorAsym Nt Ns a mass v (t, s) =
      (-(a⁻¹ ^ 2 * (v (t + 1, s) + v (t - 1, s) - 2 * v (t, s)))) +
        (-(a⁻¹ ^ 2 * (v (t, s + 1) + v (t, s - 1) - 2 * v (t, s)))) +
        mass ^ 2 * v (t, s) := by
  simp only [massOperatorAsym, ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, Pi.add_apply, Pi.neg_apply,
    Pi.smul_apply, smul_eq_mul, finiteLaplacianAsym_apply, finiteLaplacianAsymFun]
  ring

/-- **A3: discrete spatial Poincaré inequality.** On the kernel of the slice-average
projector, the quadratic form of the mass operator is bounded below by
`(spatialGap Ns a + mass²)·Σ v²`: slice-by-slice 1D Poincaré for the spatial stencil,
nonnegativity of the temporal stencil, and the exact mass term. -/
theorem massOperatorAsym_quadForm_ge_of_sliceAvg_eq_zero
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass : ℝ) (ha : 0 < a)
    (v : AsymLatticeField Nt Ns) (hv : sliceAvgProj Nt Ns v = 0) :
    (spatialGap Ns a + mass ^ 2) * ∑ x, (v x) ^ 2 ≤
      ∑ x, v x * massOperatorAsym Nt Ns a mass v x := by
  have hzero : ∀ t : ZMod Nt, ∑ s : ZMod Ns, v (t, s) = 0 := by
    intro t
    have h := congrFun hv (t, 0)
    rw [sliceAvgProj_apply] at h
    simp only [Pi.zero_apply] at h
    have hNs : ((Ns : ℝ))⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne Ns))
    exact (mul_eq_zero.mp h).resolve_left hNs
  -- split the quadratic form into temporal + spatial + mass parts
  have hsplit : ∑ x : AsymLatticeSites Nt Ns, v x * massOperatorAsym Nt Ns a mass v x =
      (∑ t : ZMod Nt, ∑ s : ZMod Ns,
        v (t, s) * (-(a⁻¹ ^ 2 * (v (t + 1, s) + v (t - 1, s) - 2 * v (t, s))))) +
      (∑ t : ZMod Nt, ∑ s : ZMod Ns,
        v (t, s) * (-(a⁻¹ ^ 2 * (v (t, s + 1) + v (t, s - 1) - 2 * v (t, s))))) +
      mass ^ 2 * ∑ x : AsymLatticeSites Nt Ns, (v x) ^ 2 := by
    rw [Fintype.sum_prod_type (f := fun x : AsymLatticeSites Nt Ns =>
        v x * massOperatorAsym Nt Ns a mass v x),
      Fintype.sum_prod_type (f := fun x : AsymLatticeSites Nt Ns => (v x) ^ 2)]
    simp_rw [massOperatorAsym_stencil_split Nt Ns a mass v]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  -- temporal part is nonnegative (columnwise 1D quadratic form)
  have hT : 0 ≤ ∑ t : ZMod Nt, ∑ s : ZMod Ns,
      v (t, s) * (-(a⁻¹ ^ 2 * (v (t + 1, s) + v (t - 1, s) - 2 * v (t, s)))) := by
    rw [Finset.sum_comm]
    refine Finset.sum_nonneg fun s _ => ?_
    simpa using oneDim_quadForm_nonneg Nt a ha.ne' (fun t => v (t, s))
  -- spatial part dominates the gap (slicewise 1D Poincaré)
  have hS : spatialGap Ns a * ∑ x : AsymLatticeSites Nt Ns, (v x) ^ 2 ≤
      ∑ t : ZMod Nt, ∑ s : ZMod Ns,
        v (t, s) * (-(a⁻¹ ^ 2 * (v (t, s + 1) + v (t, s - 1) - 2 * v (t, s)))) := by
    rw [Fintype.sum_prod_type (f := fun x : AsymLatticeSites Nt Ns => (v x) ^ 2),
      Finset.mul_sum]
    refine Finset.sum_le_sum fun t _ => ?_
    simpa using oneDim_poincare Ns a ha (fun s => v (t, s)) (hzero t)
  rw [hsplit, add_mul]
  linarith

/-! ## Sub-gap eigenvectors are slice-constant -/

/-- The eigen-equation for `massEigenvectorBasisAsym` in pointwise form:
`(-Δ_a + m²) e_k = λ_k·e_k`. Extracted from the Hermitian spectral API via the matrix
`mulVec` bridge. -/
theorem massOperatorAsym_eigenvectorBasis_apply (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (k : AsymLatticeSites Nt Ns) (x : AsymLatticeSites Nt Ns) :
    massOperatorAsym Nt Ns a mass
        (fun y => (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) y) x =
      massEigenvaluesAsym Nt Ns a mass k *
        (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x := by
  rw [massOperatorAsym_eq_matrix_mulVec]
  simpa [massEigenvaluesAsym, massEigenvectorBasisAsym] using
    congrFun (Matrix.IsHermitian.mulVec_eigenvectorBasis
      (hA := massOperatorMatrixAsym_isHermitian Nt Ns a mass) k) x

/-- **A4: sub-gap eigenvectors are slice-constant.** If the eigenvalue of a mass-operator
eigenvector lies strictly below `mass² + spatialGap Ns a`, the eigenvector is constant along
each time slice. The projected difference `w = e_k − Π e_k` is again a `λ_k`-eigenvector
with `Π w = 0`, so the spatial Poincaré inequality squeezes `Σ w² = 0`. -/
theorem massEigenvectorBasisAsym_sliceConstant_of_lt
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass : ℝ) (ha : 0 < a) (_hmass : 0 < mass)
    (k : AsymLatticeSites Nt Ns)
    (hk : massEigenvaluesAsym Nt Ns a mass k < mass ^ 2 + spatialGap Ns a) :
    ∀ (t : ZMod Nt) (s s' : ZMod Ns),
      (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) (t, s) =
        (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) (t, s') := by
  set lam := massEigenvaluesAsym Nt Ns a mass k with hlam_def
  set e : AsymLatticeField Nt Ns :=
    fun y => (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) y with he_def
  have hAe : massOperatorAsym Nt Ns a mass e = lam • e := by
    funext y
    rw [Pi.smul_apply, smul_eq_mul]
    exact massOperatorAsym_eigenvectorBasis_apply Nt Ns a mass k y
  have hAPe : massOperatorAsym Nt Ns a mass (sliceAvgProj Nt Ns e) =
      lam • sliceAvgProj Nt Ns e := by
    rw [sliceAvgProj_comm_massOperatorAsym, hAe, map_smul]
  set w : AsymLatticeField Nt Ns := e - sliceAvgProj Nt Ns e with hw_def
  have hAw : massOperatorAsym Nt Ns a mass w = lam • w := by
    rw [hw_def, map_sub, hAe, hAPe, smul_sub]
  have hPw : sliceAvgProj Nt Ns w = 0 := by
    rw [hw_def, map_sub, sliceAvgProj_idem, sub_self]
  have hquad := massOperatorAsym_quadForm_ge_of_sliceAvg_eq_zero Nt Ns a mass ha w hPw
  have hform : ∑ x, w x * massOperatorAsym Nt Ns a mass w x = lam * ∑ x, (w x) ^ 2 := by
    rw [hAw, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by
      rw [Pi.smul_apply, smul_eq_mul]; ring
  rw [hform] at hquad
  have hQnonneg : 0 ≤ ∑ x, (w x) ^ 2 := Finset.sum_nonneg fun x _ => sq_nonneg _
  have hQ0 : ∑ x, (w x) ^ 2 = 0 := by
    refine le_antisymm ?_ hQnonneg
    nlinarith
  have hw0 : ∀ x : AsymLatticeSites Nt Ns, w x = 0 := by
    intro x
    have hx := (Finset.sum_eq_zero_iff_of_nonneg
      (fun x _ => sq_nonneg (w x))).mp hQ0 x (Finset.mem_univ x)
    exact sq_eq_zero_iff.mp hx
  have hPe : sliceAvgProj Nt Ns e = e := by
    funext x
    have hx := hw0 x
    rw [hw_def, Pi.sub_apply, sub_eq_zero] at hx
    exact hx.symm
  exact (sliceAvgProj_eq_self_iff Nt Ns e).mp hPe

/-- **A5: sub-gap spectral projections are slice-constant.** The spectral projection onto a
mode set with eigenvalues strictly below `mass² + spatialGap Ns a` is constant along each
time slice (finite sum of slice-constant eigenvectors). -/
theorem asymModeProj_sliceConstant (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (S : Finset (AsymLatticeSites Nt Ns))
    (hS : ∀ k ∈ S, massEigenvaluesAsym Nt Ns a mass k < mass ^ 2 + spatialGap Ns a)
    (G : AsymLatticeField Nt Ns) :
    ∀ (t : ZMod Nt) (s s' : ZMod Ns),
      asymModeProj Nt Ns a mass S G (t, s) = asymModeProj Nt Ns a mass S G (t, s') := by
  intro t s s'
  unfold asymModeProj
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [massEigenvectorBasisAsym_sliceConstant_of_lt Nt Ns a mass ha hmass k (hS k hk) t s s']

/-! ## a-uniformity of the spatial gap at fixed spatial circumference -/

/-- Sharp form of the a-uniform lower bound: at fixed spatial circumference `Ls = Ns·a`,
`spatialGap Ns a ≥ 16/Ls²`, via Jordan's inequality `sin x ≥ (2/π)·x` on `[0, π/2]`. -/
theorem spatialGap_ge_sixteen_of_fixed_Ls (Ns : ℕ) [NeZero Ns] (a Ls : ℝ) (ha : 0 < a)
    (hLs : (Ns : ℝ) * a = Ls) (hNs : 2 ≤ Ns) :
    16 / Ls ^ 2 ≤ spatialGap Ns a := by
  have hNs' : (2 : ℝ) ≤ (Ns : ℝ) := by exact_mod_cast hNs
  have hNspos : (0 : ℝ) < (Ns : ℝ) := by linarith
  have hx0 : 0 ≤ π / (Ns : ℝ) := by positivity
  have hx2 : π / (Ns : ℝ) ≤ π / 2 :=
    div_le_div_of_nonneg_left Real.pi_pos.le two_pos hNs'
  have hsin : 2 / (Ns : ℝ) ≤ Real.sin (π / Ns) := by
    have h := Real.mul_le_sin hx0 hx2
    calc 2 / (Ns : ℝ) = 2 / π * (π / Ns) := by
          field_simp
      _ ≤ Real.sin (π / Ns) := h
  have hsq : (2 / (Ns : ℝ)) ^ 2 ≤ Real.sin (π / Ns) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hsin 2
  calc 16 / Ls ^ 2 = 4 / a ^ 2 * (2 / (Ns : ℝ)) ^ 2 := by
        rw [← hLs]
        field_simp
        ring
    _ ≤ 4 / a ^ 2 * Real.sin (π / Ns) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = spatialGap Ns a := rfl

/-- **A6: a-uniform lower bound on the spatial gap at fixed spatial circumference**
`Ls = Ns·a`. Weakening of the sharp bound `spatialGap_ge_sixteen_of_fixed_Ls`. -/
theorem spatialGap_ge_of_fixed_Ls (Ns : ℕ) [NeZero Ns] (a Ls : ℝ) (ha : 0 < a)
    (hLs : (Ns : ℝ) * a = Ls) (hNs : 2 ≤ Ns) :
    4 / Ls ^ 2 ≤ spatialGap Ns a := by
  have h16 := spatialGap_ge_sixteen_of_fixed_Ls Ns a Ls ha hLs hNs
  have hLspos : 0 < Ls := by
    rw [← hLs]
    have : (0 : ℝ) < (Ns : ℝ) := by exact_mod_cast (by omega : 0 < Ns)
    positivity
  have h4 : 4 / Ls ^ 2 ≤ 16 / Ls ^ 2 := by
    gcongr
    norm_num
  linarith

end Pphi2

end
