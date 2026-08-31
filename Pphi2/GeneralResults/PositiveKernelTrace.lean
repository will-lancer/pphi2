/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import ReflectionPositivity.TransferSystem

/-!
# Scalar lower bound from a positive spectral diagonal sum

This file isolates the last scalar step in the periodic partition lower bound.
The model-specific work is the diagonal spectral-sum identity and its
summability and nonnegativity hypotheses.
-/

open MeasureTheory
open scoped BigOperators

namespace ReflectionPositivity
namespace TransferSystem

/-- Select one nonnegative term from a summable diagonal spectral expansion of
the periodic partition function. -/
theorem partition_ge_eigenvalue_pow_of_diag_tsum
    {S : Type*} [MeasurableSpace S]
    (Ts : TransferSystem S)
    {ι : Type*} (eigenval : ι → ℝ) (i₀ : ι)
    (n : ℕ) [NeZero n]
    (hterm : ∀ i, 0 ≤ eigenval i ^ n)
    (hsum : Summable (fun i => eigenval i ^ n))
    (hdiag :
      (∫ x, Ts.kPow (n - 1) x x ∂Ts.ν) =
        ∑' i, eigenval i ^ n) :
    eigenval i₀ ^ n ≤ Ts.partition n := by
  calc
    eigenval i₀ ^ n ≤ ∑' i, eigenval i ^ n :=
      hsum.le_tsum i₀ (fun _ _ => hterm _)
    _ = ∫ x, Ts.kPow (n - 1) x x ∂Ts.ν := hdiag.symm
    _ = Ts.partition n := (partition_eq_trace Ts n).symm

end TransferSystem
end ReflectionPositivity
