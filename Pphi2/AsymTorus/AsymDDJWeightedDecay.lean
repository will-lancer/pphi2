/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cell-weighted powers from centered temporal decay

This file isolates the elementary finite-grid estimate used by a source-ball
argument.  A pointwise inverse-square bound in the centered temporal
coordinate gives a cell-weighted `p`-power bound, uniformly in both lattice
cardinalities.  The physical identity `Ns * a = Ls` is the only spatial
bookkeeping input.
This is not Dimock–Dang–Jäkel (DDJ) 5.3/6.1.
-/

import Pphi2.AsymTorus.AsymDDJSource
import Pphi2.GaussianContinuumLimit.PropagatorConvergence

noncomputable section

open GaussianField

namespace Pphi2

/-!
The hypothesis uses the temporal coordinate `x.1`; the spatial coordinate is
summed out.  The assumptions `ha`, `ha1`, `hLs`, and `hA` make every positivity
used by the finite interpolation and centered-decay estimates explicit.
-/
theorem asymWeightedLpPow_le_of_centered_temporal_decay
    {Nt Ns : ℕ} [NeZero Nt] [NeZero Ns]
    (a Ls A p : ℝ) (h : AsymLatticeField Nt Ns)
    (ha : 0 < a) (ha1 : a ≤ 1) (hLs : 0 < Ls) (hA : 0 ≤ A)
    (hNs : (Ns : ℝ) * a = Ls) (hp : 1 ≤ p)
    (hpoint : ∀ x : AsymLatticeSites Nt Ns,
      |h x| ≤ A /
        (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2) :
    asymWeightedLpPow p a h ≤ 3 * Ls * Real.rpow A p := by
  have hsum :
      ∑ x : AsymLatticeSites Nt Ns, |h x| ≤
        A * ∑ x : AsymLatticeSites Nt Ns,
          1 / (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2 := by
    calc
      ∑ x : AsymLatticeSites Nt Ns, |h x| ≤
          ∑ x : AsymLatticeSites Nt Ns,
            A * (1 /
              (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2) := by
        exact Finset.sum_le_sum fun x _ => by
          calc
            |h x| ≤ A /
                (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2 := hpoint x
            _ = A * (1 /
                (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2) := by ring
      _ = A * ∑ x : AsymLatticeSites Nt Ns,
          1 / (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2 := by
        rw [Finset.mul_sum]

  have hdecay :
      ∑ x : AsymLatticeSites Nt Ns,
          1 / (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2 =
        (Ns : ℝ) * ∑ i : ZMod Nt,
          1 / (1 + a * ((signedVal Nt i).natAbs : ℝ)) ^ 2 := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    rw [Finset.mul_sum]

  have hL : asymWeightedLpPow 1 a h ≤ 3 * Ls * A := by
    unfold asymWeightedLpPow
    calc
      a ^ 2 * ∑ x : AsymLatticeSites Nt Ns, Real.rpow |h x| 1 =
          a ^ 2 * ∑ x : AsymLatticeSites Nt Ns, |h x| := by
            change a ^ 2 * ∑ x : AsymLatticeSites Nt Ns, |h x| ^ (1 : ℝ) =
              a ^ 2 * ∑ x : AsymLatticeSites Nt Ns, |h x|
            simp only [Real.rpow_one]
      _ ≤ a ^ 2 *
          (A * ∑ x : AsymLatticeSites Nt Ns,
            1 / (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2) :=
        mul_le_mul_of_nonneg_left hsum (sq_nonneg a)
      _ = A * ((Ns : ℝ) * a) *
          ∑ i : ZMod Nt,
            a / (1 + a * ((signedVal Nt i).natAbs : ℝ)) ^ 2 := by
        rw [hdecay]
        calc
          a ^ 2 *
                (A * ((Ns : ℝ) *
                  ∑ i : ZMod Nt,
                    1 / (1 + a * ((signedVal Nt i).natAbs : ℝ)) ^ 2)) =
              A * ((Ns : ℝ) * a) *
                (a * ∑ i : ZMod Nt,
                  1 / (1 + a * ((signedVal Nt i).natAbs : ℝ)) ^ 2) := by
            ring
          _ = A * ((Ns : ℝ) * a) *
                ∑ i : ZMod Nt,
                  a / (1 + a * ((signedVal Nt i).natAbs : ℝ)) ^ 2 := by
            congr 2
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = A * Ls *
          ∑ i : ZMod Nt,
            a / (1 + a * ((signedVal Nt i).natAbs : ℝ)) ^ 2 := by
        rw [hNs]
      _ ≤ A * Ls * 3 := by
        gcongr
        exact centeredZMod_decay_sum_le_three Nt a ha ha1
      _ = 3 * Ls * A := by ring

  have hsup : ∀ x : AsymLatticeSites Nt Ns, |h x| ≤ A := by
    intro x
    let d : ℝ := 1 + a * ((signedVal Nt x.1).natAbs : ℝ)
    have hd : 1 ≤ d := by
      dsimp [d]
      have : 0 ≤ a * ((signedVal Nt x.1).natAbs : ℝ) := by positivity
      linarith
    have hdpos : 0 < d ^ 2 := by positivity
    have hd_sq : 1 ≤ d ^ 2 := by nlinarith [sq_nonneg (d - 1)]
    calc
      |h x| ≤ A / d ^ 2 := by simpa [d] using hpoint x
      _ ≤ A := by
        apply (div_le_iff₀ hdpos).2
        have hmul := mul_le_mul_of_nonneg_left hd_sq hA
        simpa using hmul

  calc
    asymWeightedLpPow p a h ≤
        Real.rpow A (p - 1) * (3 * Ls * A) :=
      asymWeightedLpPow_le_of_sup_of_weightedL1
        p a A (3 * Ls * A) h hp hA hsup hL
    _ = 3 * Ls * Real.rpow A p := by
      calc
        Real.rpow A (p - 1) * (3 * Ls * A) =
            3 * Ls * (Real.rpow A (p - 1) * A) := by ring
        _ = 3 * Ls * Real.rpow A p := by
          calc
            3 * Ls * (Real.rpow A (p - 1) * A) =
                3 * Ls * Real.rpow A ((p - 1) + 1) := by
              congr 1
              exact (Real.rpow_add_one' hA (y := p - 1) (by linarith)).symm
            _ = 3 * Ls * Real.rpow A p := by
              congr 1
              ring

end Pphi2
