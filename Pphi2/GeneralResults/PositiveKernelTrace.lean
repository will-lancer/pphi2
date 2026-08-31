/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import ReflectionPositivity.TransferSystem

/-!
# Scalar lower bound from a positive spectral diagonal sum

This file isolates the last scalar step in the periodic partition lower bound.
The abstract `TransferSystem` API provides the diagonal integral through
`partition_eq_trace`, but it has no operator, trace-class, or spectral-basis
data. `DiagonalSpectralTsum` records the smallest additional contract needed
for the spectral argument. The model-specific work is to construct that
certificate from a concrete trace-class spectral theorem.
-/

open MeasureTheory
open scoped BigOperators

namespace ReflectionPositivity
namespace TransferSystem

/-- The missing diagonal spectral input for a periodic `TransferSystem`.

The abstract transfer-system API has no operator or trace-class decomposition.
This certificate records exactly the data needed to identify the diagonal
partition integral with a summable series of nonnegative eigenvalue powers.
-/
structure DiagonalSpectralTsum
    {S : Type*} [MeasurableSpace S]
    (Ts : TransferSystem S) (ι : Type*) (n : ℕ) where
  /-- The eigenvalue attached to each spectral index. -/
  eigenval : ι → ℝ
  /-- Every term in the diagonal series is nonnegative. -/
  term_nonneg : ∀ i, 0 ≤ eigenval i ^ n
  /-- The diagonal spectral series is summable. -/
  summable : Summable (fun i => eigenval i ^ n)
  /-- The kernel diagonal has the asserted spectral expansion. -/
  diagonal_eq :
    (∫ x, Ts.kPow (n - 1) x x ∂Ts.ν) =
      ∑' i, eigenval i ^ n

/-- Reverse the orientation of the abstract partition-trace identity. -/
theorem diagonal_integral_eq_partition
    {S : Type*} [MeasurableSpace S]
    (Ts : TransferSystem S) (n : ℕ) [NeZero n] :
    (∫ x, Ts.kPow (n - 1) x x ∂Ts.ν) = Ts.partition n :=
  (partition_eq_trace Ts n).symm

/-- Turn a diagonal spectral certificate into the corresponding partition
identity. This is the measure-theoretic bridge supplied by `partition_eq_trace`.
-/
theorem partition_eq_tsum_of_diagonal_spectral
    {S : Type*} [MeasurableSpace S]
    (Ts : TransferSystem S) {ι : Type*} {n : ℕ} [NeZero n]
    (h : DiagonalSpectralTsum Ts ι n) :
    Ts.partition n = ∑' i, h.eigenval i ^ n := by
  calc
    Ts.partition n = ∫ x, Ts.kPow (n - 1) x x ∂Ts.ν := partition_eq_trace Ts n
    _ = ∑' i, h.eigenval i ^ n := h.diagonal_eq

/-- Build the certificate when nonnegative eigenvalues imply termwise
nonnegativity of their powers. -/
theorem diagonal_spectral_tsum_of_nonneg
    {S : Type*} [MeasurableSpace S]
    (Ts : TransferSystem S) {ι : Type*} (eigenval : ι → ℝ) (n : ℕ)
    (heigenval : ∀ i, 0 ≤ eigenval i)
    (hsum : Summable (fun i => eigenval i ^ n))
    (hdiag :
      (∫ x, Ts.kPow (n - 1) x x ∂Ts.ν) =
        ∑' i, eigenval i ^ n) :
    DiagonalSpectralTsum Ts ι n :=
  { eigenval := eigenval
    term_nonneg := fun i => pow_nonneg (heigenval i) n
    summable := hsum
    diagonal_eq := hdiag }

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
    _ = Ts.partition n := diagonal_integral_eq_partition Ts n

/-- The ground-term floor in the packaged diagonal spectral contract. -/
theorem partition_ge_eigenvalue_pow_of_diagonal_spectral
    {S : Type*} [MeasurableSpace S]
    (Ts : TransferSystem S) {ι : Type*} {n : ℕ} [NeZero n]
    (h : DiagonalSpectralTsum Ts ι n) (i₀ : ι) :
    h.eigenval i₀ ^ n ≤ Ts.partition n :=
  partition_ge_eigenvalue_pow_of_diag_tsum Ts h.eigenval i₀ n
    h.term_nonneg h.summable h.diagonal_eq

end TransferSystem
end ReflectionPositivity
