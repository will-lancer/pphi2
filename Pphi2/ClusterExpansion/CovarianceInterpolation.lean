/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Pphi2.ClusterExpansion.ForestPositivity

/-!
# Covariance interpolation by block couplings

The pullback of a positive-semidefinite block matrix along a site-to-block map
is positive semidefinite.  Schur multiplication with the original covariance
then preserves positive semidefiniteness.
-/

namespace Pphi2.ClusterExpansion

/-- Pull a block coupling matrix back to the finite site set. -/
def pulledCouplingMatrix
    {Site Block : Type*}
    (blockOf : Site → Block) (S : Matrix Block Block ℝ) :
    Matrix Site Site ℝ :=
  S.submatrix blockOf blockOf

theorem pulledCouplingMatrix_posSemidef
    {Site Block : Type*} [Fintype Site] [Fintype Block]
    (blockOf : Site → Block) (S : Matrix Block Block ℝ)
    (hS : S.PosSemidef) :
    (pulledCouplingMatrix blockOf S).PosSemidef := by
  exact hS.submatrix blockOf

/-- Covariance obtained by switching cross-block entries with a coupling
matrix pulled back to sites. -/
def interpolatedCovariance
    {Site Block : Type*}
    (C : Matrix Site Site ℝ) (blockOf : Site → Block)
    (S : Matrix Block Block ℝ) : Matrix Site Site ℝ :=
  Matrix.hadamard C (pulledCouplingMatrix blockOf S)

/-- The reviewed Schur step: every interpolation whose block coupling is PSD
produces a PSD covariance. -/
theorem interpolatedCovariance_posSemidef
    {Site Block : Type*} [Fintype Site] [Fintype Block]
    (C : Matrix Site Site ℝ) (hC : C.PosSemidef)
    (blockOf : Site → Block) (S : Matrix Block Block ℝ)
    (hS : S.PosSemidef) :
    (interpolatedCovariance C blockOf S).PosSemidef := by
  exact hC.hadamard (pulledCouplingMatrix_posSemidef blockOf S hS)

/-- Forest coupling pulled from blocks to sites. -/
noncomputable def pulledForestMatrix
    {Site Block : Type*} [Fintype Block] [DecidableEq Block]
    (blockOf : Site → Block) (T : SpanningForest Block)
    (t : ForestEdge T → ℝ) : Matrix Site Site ℝ :=
  pulledCouplingMatrix blockOf
    (edgeCouplingMatrix (forestEdgePoint T t))

theorem pulledForestMatrix_posSemidef_of_block
    {Site Block : Type*} [Fintype Site] [Fintype Block]
    [DecidableEq Block]
    (blockOf : Site → Block) (T : SpanningForest Block)
    (t : ForestEdge T → ℝ)
    (hS : (edgeCouplingMatrix (forestEdgePoint T t)).PosSemidef) :
    (pulledForestMatrix blockOf T t).PosSemidef := by
  exact hS.submatrix blockOf

theorem pulledForestMatrix_posSemidef
    {Site Block : Type*} [Fintype Site] [Fintype Block]
    [DecidableEq Block]
    (blockOf : Site → Block) (T : SpanningForest Block)
    (t : ForestEdge T → ℝ) (ht : t ∈ unitCube T) :
    (pulledForestMatrix blockOf T t).PosSemidef := by
  exact pulledForestMatrix_posSemidef_of_block blockOf T t
    (forestEdgeCouplingMatrix_posSemidef T t ht)

/-- Forest-interpolated site covariance. -/
noncomputable def forestInterpolatedCovariance
    {Site Block : Type*} [Fintype Block] [DecidableEq Block]
    (C : Matrix Site Site ℝ) (blockOf : Site → Block)
    (T : SpanningForest Block) (t : ForestEdge T → ℝ) :
    Matrix Site Site ℝ :=
  Matrix.hadamard C (pulledForestMatrix blockOf T t)

theorem forestInterpolatedCovariance_posSemidef_of_block
    {Site Block : Type*} [Fintype Site] [Fintype Block]
    [DecidableEq Block]
    (C : Matrix Site Site ℝ) (hC : C.PosSemidef)
    (blockOf : Site → Block) (T : SpanningForest Block)
    (t : ForestEdge T → ℝ)
    (hS : (edgeCouplingMatrix (forestEdgePoint T t)).PosSemidef) :
    (forestInterpolatedCovariance C blockOf T t).PosSemidef := by
  exact hC.hadamard
    (pulledForestMatrix_posSemidef_of_block blockOf T t hS)

/-- Every BKAR forest interpolation in the unit edge cube preserves
positive semidefiniteness of the site covariance. -/
theorem forestInterpolatedCovariance_posSemidef
    {Site Block : Type*} [Fintype Site] [Fintype Block]
    [DecidableEq Block]
    (C : Matrix Site Site ℝ) (hC : C.PosSemidef)
    (blockOf : Site → Block) (T : SpanningForest Block)
    (t : ForestEdge T → ℝ) (ht : t ∈ unitCube T) :
    (forestInterpolatedCovariance C blockOf T t).PosSemidef := by
  exact hC.hadamard (pulledForestMatrix_posSemidef blockOf T t ht)

end Pphi2.ClusterExpansion
