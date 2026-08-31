/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Lattice.AsymCovariance
import LeeYang.Measure.PositiveSourceApprox
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Ring

/-!
# Shared-spin adapter for the asymmetric finite lattice

The asymmetric lattice has one forward temporal bond and one forward spatial
bond at every site.  A `Finset (site × site)` forgets this distinction when
periodicity makes two labelled bonds have the same endpoints.  The adapter
therefore starts with direction-labelled bonds, removes periodic self-loops
into a separate finite sum, and only then aggregates the remaining endpoint
pairs for the shared-spin API.

Every site remains in the spin type.  In particular, a zero source entry is
not removed from an interacting graph.  The floor-based positive-source
constructor below keeps every spin and converges to a nonnegative source,
including one with zero entries.
-/

noncomputable section

open scoped BigOperators
open GaussianField

namespace Pphi2

/-! ## Labelled lattice bonds -/

/-- `true` labels a forward temporal bond and `false` a forward spatial bond. -/
abbrev AsymBondDirection := Bool

/-- A bond label records its direction and its starting lattice site. -/
abbrev AsymBondLabel (Nt Ns : ℕ) :=
  AsymBondDirection × AsymLatticeSites Nt Ns

/-- Forward temporal and spatial displacements. -/
def asymBondShift (Nt Ns : ℕ) (d : AsymBondDirection) : AsymLatticeSites Nt Ns :=
  if d then ((1 : ZMod Nt), (0 : ZMod Ns)) else ((0 : ZMod Nt), (1 : ZMod Ns))

@[simp] theorem asymBondShift_true (Nt Ns : ℕ) :
    asymBondShift Nt Ns true = ((1 : ZMod Nt), (0 : ZMod Ns)) := by
  simp [asymBondShift]

@[simp] theorem asymBondShift_false (Nt Ns : ℕ) :
    asymBondShift Nt Ns false = ((0 : ZMod Nt), (1 : ZMod Ns)) := by
  simp [asymBondShift]

/-- The ordered endpoints of a labelled forward bond. -/
def asymBondEndpoint (Nt Ns : ℕ) (b : AsymBondLabel Nt Ns) :
    AsymLatticeSites Nt Ns × AsymLatticeSites Nt Ns :=
  (b.2, b.2 + asymBondShift Nt Ns b.1)

@[simp] theorem asymBondEndpoint_true (Nt Ns : ℕ)
    (x : AsymLatticeSites Nt Ns) :
    asymBondEndpoint Nt Ns (true, x) =
      (x, x + ((1 : ZMod Nt), (0 : ZMod Ns))) := by
  simp [asymBondEndpoint]

@[simp] theorem asymBondEndpoint_false (Nt Ns : ℕ)
    (x : AsymLatticeSites Nt Ns) :
    asymBondEndpoint Nt Ns (false, x) =
      (x, x + ((0 : ZMod Nt), (1 : ZMod Ns))) := by
  simp [asymBondEndpoint]

/-- One labelled temporal or spatial bond at every site.  Distinct labels are
retained even when their endpoint pairs coincide. -/
def asymBondLabels (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] :
    Finset (AsymBondLabel Nt Ns) := Finset.univ

/-- The endpoint predicate used to separate periodic self-loops. -/
def asymBondIsLoop {Nt Ns : ℕ} (b : AsymBondLabel Nt Ns) : Prop :=
  (asymBondEndpoint Nt Ns b).1 = (asymBondEndpoint Nt Ns b).2

/-- Labelled bonds whose two endpoints coincide. -/
def asymBondLoopLabels (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] :
    Finset (AsymBondLabel Nt Ns) :=
  (asymBondLabels Nt Ns).filter (fun b => asymBondIsLoop b)

/-- Labelled bonds with distinct endpoints. -/
def asymBondNonloopLabels (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] :
    Finset (AsymBondLabel Nt Ns) :=
  (asymBondLabels Nt Ns).filter (fun b => ¬asymBondIsLoop b)

theorem asymBondLabels_split (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] :
    asymBondLabels Nt Ns = asymBondLoopLabels Nt Ns ∪
      asymBondNonloopLabels Nt Ns := by
  classical
  ext b
  by_cases h : asymBondIsLoop b <;> simp [asymBondLoopLabels,
    asymBondNonloopLabels, asymBondLabels, h]

/-! ## Spin energies and endpoint aggregation -/

/-- The spin product attached to an ordered pair of lattice sites. -/
def asymSpinPairTerm {Nt Ns : ℕ} [NeZero Nt] [NeZero Ns]
    (eta : AsymLatticeSites Nt Ns → Bool)
    (e : AsymLatticeSites Nt Ns × AsymLatticeSites Nt Ns) : ℝ :=
  LeeYang.Ising.sharedSpinValue (eta e.1) *
    LeeYang.Ising.sharedSpinValue (eta e.2)

/-- The spin product attached to a labelled bond. -/
def asymBondSpinTerm {Nt Ns : ℕ} [NeZero Nt] [NeZero Ns]
    (eta : AsymLatticeSites Nt Ns → Bool) (b : AsymBondLabel Nt Ns) : ℝ :=
  asymSpinPairTerm eta (asymBondEndpoint Nt Ns b)

/-- The labelled nearest-neighbour energy, before loop removal or aggregation. -/
def asymLatticeSpinEnergy (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (eta : AsymLatticeSites Nt Ns → Bool) : ℝ :=
  -- This packet uses coefficient-one bond factors.  Action-dependent bond
  -- coefficients and the one-site Wick factors belong to the density bridge.
  ∑ b in asymBondLabels Nt Ns, asymBondSpinTerm eta b

/-- The constant energy carried by periodic self-loops. -/
def asymLoopConstant (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] : ℝ :=
  (asymBondLoopLabels Nt Ns).card

/-- The loop contribution to the labelled energy. -/
def asymLoopSpinEnergy (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (eta : AsymLatticeSites Nt Ns → Bool) : ℝ :=
  ∑ b in asymBondLoopLabels Nt Ns, asymBondSpinTerm eta b

/-- The nonloop contribution to the labelled energy. -/
def asymNonloopSpinEnergy (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (eta : AsymLatticeSites Nt Ns → Bool) : ℝ :=
  ∑ b in asymBondNonloopLabels Nt Ns, asymBondSpinTerm eta b

/-- Aggregate all labelled nonloop bonds with a fixed ordered endpoint pair.
The sum of ones is intentional: it records bond multiplicity. -/
def asymSharedSpinCoupling (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (u v : AsymLatticeSites Nt Ns) : ℝ :=
  ∑ b in (asymBondNonloopLabels Nt Ns).filter
      (fun b => asymBondEndpoint Nt Ns b = (u, v)), (1 : ℝ)

/-- The endpoint edge set exposed to the shared-spin API. -/
def asymSharedSpinEdges (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] :
    Finset (AsymLatticeSites Nt Ns × AsymLatticeSites Nt Ns) :=
  (asymBondNonloopLabels Nt Ns).image (asymBondEndpoint Nt Ns)

theorem asymSharedSpinCoupling_eq_card (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (u v : AsymLatticeSites Nt Ns) :
    asymSharedSpinCoupling Nt Ns u v =
      ((asymBondNonloopLabels Nt Ns).filter
        (fun b => asymBondEndpoint Nt Ns b = (u, v))).card := by
  simp [asymSharedSpinCoupling]

theorem asymSharedSpinCoupling_nonneg (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (u v : AsymLatticeSites Nt Ns) :
    0 ≤ asymSharedSpinCoupling Nt Ns u v := by
  apply Finset.sum_nonneg
  intro b hb
  exact zero_le_one

theorem asymSharedSpinEdges_loopless (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] :
    ∀ e ∈ asymSharedSpinEdges Nt Ns, e.1 ≠ e.2 := by
  intro e he
  rcases Finset.mem_image.mp he with ⟨b, hb, rfl⟩
  simpa [asymBondIsLoop] using (Finset.mem_filter.mp hb).2

theorem asymSharedSpinEdges_mem_iff (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (e : AsymLatticeSites Nt Ns × AsymLatticeSites Nt Ns) :
    e ∈ asymSharedSpinEdges Nt Ns ↔
      ∃ b ∈ asymBondNonloopLabels Nt Ns, asymBondEndpoint Nt Ns b = e := by
  simp [asymSharedSpinEdges]

theorem asymLoopSpinEnergy_eq_constant (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (eta : AsymLatticeSites Nt Ns → Bool) :
    asymLoopSpinEnergy Nt Ns eta = asymLoopConstant Nt Ns := by
  classical
  unfold asymLoopSpinEnergy asymLoopConstant
  calc
    (∑ b in asymBondLoopLabels Nt Ns, asymBondSpinTerm eta b) =
        ∑ _b in asymBondLoopLabels Nt Ns, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro b hb
      change asymSpinPairTerm eta (asymBondEndpoint Nt Ns b) = 1
      unfold asymSpinPairTerm
      have hloop : (asymBondEndpoint Nt Ns b).1 =
          (asymBondEndpoint Nt Ns b).2 := by
        simpa [asymBondIsLoop] using (Finset.mem_filter.mp hb).2
      rw [hloop]
      cases h : eta (asymBondEndpoint Nt Ns b).2 <;>
        simp [LeeYang.Ising.sharedSpinValue, h]
    _ = (asymBondLoopLabels Nt Ns).card := by simp

theorem asymLatticeSpinEnergy_eq_loop_add_nonloop
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (eta : AsymLatticeSites Nt Ns → Bool) :
    asymLatticeSpinEnergy Nt Ns eta =
      asymLoopSpinEnergy Nt Ns eta + asymNonloopSpinEnergy Nt Ns eta := by
  classical
  unfold asymLatticeSpinEnergy asymLoopSpinEnergy asymNonloopSpinEnergy
  simpa [asymBondLoopLabels, asymBondNonloopLabels] using
    (Finset.sum_filter_add_sum_filter_not
      (asymBondLabels Nt Ns) (fun b => asymBondIsLoop b)
      (fun b => asymBondSpinTerm eta b)).symm

theorem asymNonloopSpinEnergy_eq_sharedSpinIsingEnergy
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (eta : AsymLatticeSites Nt Ns → Bool) :
    asymNonloopSpinEnergy Nt Ns eta =
      LeeYang.Ising.sharedSpinIsingEnergy
        (asymSharedSpinCoupling Nt Ns) (asymSharedSpinEdges Nt Ns) eta := by
  classical
  let L := asymBondNonloopLabels Nt Ns
  let E := asymSharedSpinEdges Nt Ns
  let g := asymBondEndpoint Nt Ns
  have hmap : ∀ b ∈ L, g b ∈ E := by
    intro b hb
    exact Finset.mem_image.mpr ⟨b, hb, rfl⟩
  have hfilter :
      (∑ b in L, asymSpinPairTerm eta (g b)) =
        ∑ b in L.filter (fun b => g b ∈ E), asymSpinPairTerm eta (g b) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro b hb hnot
    exact (hnot (Finset.mem_filter.mpr ⟨hb, hmap b hb⟩)).elim
  have hfiber :=
    Finset.sum_fiberwise_eq_sum_filter' L E g
      (fun e : AsymLatticeSites Nt Ns × AsymLatticeSites Nt Ns =>
        asymSpinPairTerm eta e)
  calc
    asymNonloopSpinEnergy Nt Ns eta =
        ∑ b in L, asymSpinPairTerm eta (g b) := rfl
    _ = ∑ b in L.filter (fun b => g b ∈ E),
        asymSpinPairTerm eta (g b) := hfilter
    _ = ∑ e in E, ∑ b in L.filter (fun b => g b = e),
        asymSpinPairTerm eta e := hfiber.symm
    _ = LeeYang.Ising.sharedSpinIsingEnergy
        (asymSharedSpinCoupling Nt Ns) E eta := by
      unfold LeeYang.Ising.sharedSpinIsingEnergy
      apply Finset.sum_congr rfl
      intro e he
      symm
      simp [asymSharedSpinCoupling, asymSpinPairTerm, L, g, Finset.sum_mul,
        mul_assoc]

theorem asymLatticeSpinEnergy_eq_loopConstant_add_shared
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (eta : AsymLatticeSites Nt Ns → Bool) :
    asymLatticeSpinEnergy Nt Ns eta = asymLoopConstant Nt Ns +
      LeeYang.Ising.sharedSpinIsingEnergy
        (asymSharedSpinCoupling Nt Ns) (asymSharedSpinEdges Nt Ns) eta := by
  rw [asymLatticeSpinEnergy_eq_loop_add_nonloop,
    asymLoopSpinEnergy_eq_constant,
    asymNonloopSpinEnergy_eq_sharedSpinIsingEnergy]

/-! ## Weight, polynomial, and normalized MGF factorization -/

/-- The positive weight of a labelled lattice spin assignment. -/
def asymLatticeSpinWeight (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (eta : AsymLatticeSites Nt Ns → Bool) : ℝ :=
  Real.exp (asymLatticeSpinEnergy Nt Ns eta)

theorem asymLatticeSpinWeight_eq_loopFactor_mul_shared
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (eta : AsymLatticeSites Nt Ns → Bool) :
    asymLatticeSpinWeight Nt Ns eta =
      Real.exp (asymLoopConstant Nt Ns) *
        LeeYang.Ising.sharedSpinIsingWeight
          (asymSharedSpinCoupling Nt Ns) (asymSharedSpinEdges Nt Ns) eta := by
  rw [asymLatticeSpinWeight,
    asymLatticeSpinEnergy_eq_loopConstant_add_shared,
    LeeYang.Ising.sharedSpinIsingWeight, Real.exp_add]

/-- The full labelled finite-lattice Gibbs polynomial. -/
def asymLatticeSpinPartitionMv (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] :
    MvPolynomial (AsymLatticeSites Nt Ns) ℂ :=
  ∑ eta : AsymLatticeSites Nt Ns → Bool,
    MvPolynomial.C ((asymLatticeSpinWeight Nt Ns eta : ℝ) : ℂ) *
      LeeYang.Ising.sharedSpinFugacityMonomial eta

theorem asymLatticeSpinPartitionMv_eq_loopFactor_mul_shared
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] :
    asymLatticeSpinPartitionMv Nt Ns =
      MvPolynomial.C (Real.exp (asymLoopConstant Nt Ns) : ℂ) *
        LeeYang.Ising.sharedSpinIsingPartitionMv
          (asymSharedSpinCoupling Nt Ns) (asymSharedSpinEdges Nt Ns) := by
  classical
  unfold asymLatticeSpinPartitionMv
  rw [LeeYang.Ising.sharedSpinIsingPartitionMv]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro eta heta
  rw [asymLatticeSpinWeight_eq_loopFactor_mul_shared]
  rw [Complex.ofReal_mul, MvPolynomial.C_mul]
  ring

/-- The full labelled external-field partition function. -/
def asymLatticeSpinFieldPartition (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (h : AsymLatticeSites Nt Ns → ℝ) : ℝ :=
  ∑ eta : AsymLatticeSites Nt Ns → Bool,
    Real.exp (asymLatticeSpinEnergy Nt Ns eta +
      LeeYang.Ising.sharedSpinFieldEnergy h eta)

theorem asymLatticeSpinFieldPartition_eq_loopFactor_mul_shared
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (h : AsymLatticeSites Nt Ns → ℝ) :
    asymLatticeSpinFieldPartition Nt Ns h =
      Real.exp (asymLoopConstant Nt Ns) *
        LeeYang.Ising.sharedSpinIsingFieldPartition
          (asymSharedSpinCoupling Nt Ns) (asymSharedSpinEdges Nt Ns) h := by
  classical
  unfold asymLatticeSpinFieldPartition
  unfold LeeYang.Ising.sharedSpinIsingFieldPartition
  calc
    (∑ eta : AsymLatticeSites Nt Ns → Bool,
        Real.exp (asymLatticeSpinEnergy Nt Ns eta +
          LeeYang.Ising.sharedSpinFieldEnergy h eta)) =
        ∑ eta : AsymLatticeSites Nt Ns → Bool,
          Real.exp (asymLoopConstant Nt Ns +
            (LeeYang.Ising.sharedSpinIsingEnergy
                (asymSharedSpinCoupling Nt Ns) (asymSharedSpinEdges Nt Ns) eta +
              LeeYang.Ising.sharedSpinFieldEnergy h eta)) := by
      apply Finset.sum_congr rfl
      intro eta heta
      rw [asymLatticeSpinEnergy_eq_loopConstant_add_shared]
      congr 1
      ring
    _ = ∑ eta : AsymLatticeSites Nt Ns → Bool,
          (Real.exp (asymLoopConstant Nt Ns)) *
            Real.exp (LeeYang.Ising.sharedSpinIsingEnergy
              (asymSharedSpinCoupling Nt Ns) (asymSharedSpinEdges Nt Ns) eta +
              LeeYang.Ising.sharedSpinFieldEnergy h eta) := by
      apply Finset.sum_congr rfl
      intro eta heta
      rw [Real.exp_add]
    _ = Real.exp (asymLoopConstant Nt Ns) *
          ∑ eta : AsymLatticeSites Nt Ns → Bool,
            Real.exp (LeeYang.Ising.sharedSpinIsingEnergy
              (asymSharedSpinCoupling Nt Ns) (asymSharedSpinEdges Nt Ns) eta +
              LeeYang.Ising.sharedSpinFieldEnergy h eta) := by
      symm
      rw [Finset.mul_sum]

/-- The normalized MGF formed from the full labelled energy. -/
def asymLatticeSpinMgf (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (f : AsymLatticeSites Nt Ns → ℝ) (t : ℝ) : ℝ :=
  asymLatticeSpinFieldPartition Nt Ns (fun i => t * f i) /
    asymLatticeSpinFieldPartition Nt Ns 0

theorem asymLatticeSpinMgf_eq_sharedSpinIsingMgf
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (f : AsymLatticeSites Nt Ns → ℝ) (t : ℝ) :
    asymLatticeSpinMgf Nt Ns f t =
      LeeYang.Ising.sharedSpinIsingMgf
        (asymSharedSpinCoupling Nt Ns) (asymSharedSpinEdges Nt Ns) f t := by
  unfold asymLatticeSpinMgf
  rw [asymLatticeSpinFieldPartition_eq_loopFactor_mul_shared,
    asymLatticeSpinFieldPartition_eq_loopFactor_mul_shared]
  simpa only [LeeYang.Ising.sharedSpinIsingMgf] using
    (mul_div_mul_left _ _ (Real.exp_ne_zero (asymLoopConstant Nt Ns)))

/-! ## Lee-Yang target and zero-source route -/

theorem asymSharedSpinIsingPartitionMv_isPolydiskZeroFree
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] :
    MvPolynomial.IsPolydiskZeroFree
      (LeeYang.Ising.sharedSpinIsingPartitionMv
        (asymSharedSpinCoupling Nt Ns) (asymSharedSpinEdges Nt Ns)) := by
  apply LeeYang.Ising.sharedSpinIsingPartitionMv_isPolydiskZeroFree
  · intro e he
    exact asymSharedSpinCoupling_nonneg Nt Ns e.1 e.2
  · exact asymSharedSpinEdges_loopless Nt Ns

theorem asymSharedSpinDiagonal_leeYangCircle
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (w : AsymLatticeSites Nt Ns → ℕ) (hwpos : ∀ i, 0 < w i) :
    (LeeYang.Ising.diagonalSpecialization w
      (LeeYang.Ising.sharedSpinIsingPartitionMv
        (asymSharedSpinCoupling Nt Ns) (asymSharedSpinEdges Nt Ns))).LeeYangCircle :=
  LeeYang.Ising.sharedSpinIsingDiagonal_leeYangCircle
    (asymSharedSpinCoupling Nt Ns) (asymSharedSpinEdges Nt Ns) w
    (fun e he => asymSharedSpinCoupling_nonneg Nt Ns e.1 e.2)
    (asymSharedSpinEdges_loopless Nt Ns) hwpos

/-- Positive integer source approximants keep every lattice spin, even when
the target source vanishes at some sites. -/
noncomputable def asymSharedSpinPositiveSourceApproximation
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (f : AsymLatticeSites Nt Ns → ℝ) (hf : ∀ i, 0 ≤ f i) :
    LeeYang.Ising.PositiveIntegerSourceApproximation
      (σ := AsymLatticeSites Nt Ns) f :=
  by
    refine
      { weights := fun n i =>
          Nat.floor (((n + 1 : ℕ) : ℝ) * f i) + 1
        scales := fun n => ⟨n + 1, Nat.succ_pos n⟩
        target_nonneg := hf
        weights_pos := ?_
        ratio_tendsto := ?_ }
    · intro n i
      exact Nat.succ_pos _
    · intro i
      change Filter.Tendsto
        (fun n : ℕ =>
          ((Nat.floor (((n + 1 : ℕ) : ℝ) * f i) + 1 : ℕ) : ℝ) /
            ((n + 1 : ℕ) : ℝ))
        Filter.atTop (nhds (f i))
      have hscale :
          Filter.Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ))
            Filter.atTop Filter.atTop :=
        tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1)
      have hfloor :
          Filter.Tendsto
            (fun n : ℕ =>
              (⌊f i * ((n + 1 : ℕ) : ℝ)⌋₊ : ℝ) /
                ((n + 1 : ℕ) : ℝ))
            Filter.atTop (nhds (f i)) :=
        (tendsto_nat_floor_mul_div_atTop (R := ℝ) (a := f i) (hf i)).comp hscale
      have hone :
          Filter.Tendsto
            (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ))
            Filter.atTop (nhds 0) := by
        simpa [Nat.cast_add] using
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa [Nat.cast_add, mul_comm, add_div] using hfloor.add hone

theorem asymSharedSpinPositiveSourceApproximation_source_tendsto
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (f : AsymLatticeSites Nt Ns → ℝ) (hf : ∀ i, 0 ≤ f i)
    (i : AsymLatticeSites Nt Ns) :
    Filter.Tendsto
      (fun n =>
        (asymSharedSpinPositiveSourceApproximation Nt Ns f hf).source n i)
      Filter.atTop (nhds (f i)) := by
  exact (asymSharedSpinPositiveSourceApproximation Nt Ns f hf).source_tendsto i

theorem asymSharedSpinPositiveSourceApproximation_mgf_tendsto
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (f : AsymLatticeSites Nt Ns → ℝ) (hf : ∀ i, 0 ≤ f i) (t : ℝ) :
    Filter.Tendsto
      (fun n => asymLatticeSpinMgf Nt Ns
        ((asymSharedSpinPositiveSourceApproximation Nt Ns f hf).source n) t)
      Filter.atTop (nhds (asymLatticeSpinMgf Nt Ns f t)) := by
  simpa only [asymLatticeSpinMgf_eq_sharedSpinIsingMgf] using
    (LeeYang.Ising.PositiveIntegerSourceApproximation.mgf_tendsto
      (asymSharedSpinPositiveSourceApproximation Nt Ns f hf)
      (asymSharedSpinCoupling Nt Ns) (asymSharedSpinEdges Nt Ns) t)

theorem asymSharedSpinPositiveSourceApproximation_diagonal_leeYangCircle
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (f : AsymLatticeSites Nt Ns → ℝ) (hf : ∀ i, 0 ≤ f i) (n : ℕ) :
    (LeeYang.Ising.diagonalSpecialization
        ((asymSharedSpinPositiveSourceApproximation Nt Ns f hf).weights n)
      (LeeYang.Ising.sharedSpinIsingPartitionMv
        (asymSharedSpinCoupling Nt Ns) (asymSharedSpinEdges Nt Ns))).LeeYangCircle :=
  LeeYang.Ising.PositiveIntegerSourceApproximation.diagonal_leeYangCircle
    (asymSharedSpinPositiveSourceApproximation Nt Ns f hf)
    (asymSharedSpinCoupling Nt Ns) (asymSharedSpinEdges Nt Ns) n
    (fun e he => asymSharedSpinCoupling_nonneg Nt Ns e.1 e.2)
    (asymSharedSpinEdges_loopless Nt Ns)

/-! ## Focused two-site smoke target -/

/-- The `2 × 1` lattice has two sites.  This specialization checks the full
loop/aggregation/MGF route on the smallest temporal two-site lattice while
retaining the spatial labelled loops. -/
theorem asymSharedSpin_twoVertex_smoke
    (eta : AsymLatticeSites 2 1 → Bool)
    (f : AsymLatticeSites 2 1 → ℝ) (t : ℝ) :
    asymLatticeSpinEnergy 2 1 eta = asymLoopConstant 2 1 +
      LeeYang.Ising.sharedSpinIsingEnergy
        (asymSharedSpinCoupling 2 1) (asymSharedSpinEdges 2 1) eta ∧
    asymLatticeSpinMgf 2 1 f t =
      LeeYang.Ising.sharedSpinMgf
        (asymSharedSpinCoupling 2 1) (asymSharedSpinEdges 2 1) f t := by
  exact ⟨asymLatticeSpinEnergy_eq_loopConstant_add_shared 2 1 eta,
    asymLatticeSpinMgf_eq_sharedSpinIsingMgf 2 1 f t⟩

end Pphi2

#print axioms Pphi2.asymLatticeSpinEnergy_eq_loopConstant_add_shared
#print axioms Pphi2.asymLatticeSpinWeight_eq_loopFactor_mul_shared
#print axioms Pphi2.asymLatticeSpinPartitionMv_eq_loopFactor_mul_shared
#print axioms Pphi2.asymLatticeSpinMgf_eq_sharedSpinIsingMgf
#print axioms Pphi2.asymSharedSpinIsingPartitionMv_isPolydiskZeroFree
#print axioms Pphi2.asymSharedSpinPositiveSourceApproximation_mgf_tendsto
#print axioms Pphi2.asymSharedSpinPositiveSourceApproximation_diagonal_leeYangCircle
#print axioms Pphi2.asymSharedSpin_twoVertex_smoke
