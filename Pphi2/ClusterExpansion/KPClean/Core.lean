/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Finset.Powerset

/-!
# A clean finite Kotecký--Preiss core

This file records the finite polymer-gas data used by the Kotecký--Preiss
criterion.  A polymer is an element of an arbitrary type, and a finite volume
is a `Finset` of polymers.  Collections are admissible when distinct members
are compatible.  The finite partition function is the sum of the products of
their activities.

The activity is real-valued here so that the finite positivity interface is
available without importing any measure theory.  The Kotecký--Preiss row sum
uses absolute activities, as in the published criterion.  The analytic
rooted cluster estimate is deliberately left for the next packet; this module
only exposes its finite rooted and pinned boundary data.

The definitions follow the finite-volume form of the criterion in
Kotecký--Preiss, *Cluster expansion for abstract polymer models*,
Communications in Mathematical Physics 103 (1986), 491--498.
-/

open scoped BigOperators

namespace Pphi2.ClusterExpansion.KPClean

variable {Polymer : Type*} [DecidableEq Polymer]

/-- A polymer type together with the symmetric, reflexive incompatibility
relation used by an abstract polymer gas. -/
structure PolymerSystem where
  incompatible : Polymer → Polymer → Prop
  decIncompatible : DecidableRel incompatible
  incompatible_refl : Reflexive incompatible
  incompatible_symm : Symmetric incompatible

instance (S : PolymerSystem Polymer) : DecidableRel S.incompatible :=
  S.decIncompatible

/-- Real activities indexed by polymers. -/
abbrev Activity (Polymer : Type*) := Polymer → ℝ

/-- A finite collection has no incompatible pair of distinct polymers.  The
relation is reflexive, so the distinctness hypothesis is part of the usual
independent-set convention. -/
def IsCompatible (S : PolymerSystem Polymer) (I : Finset Polymer) : Prop :=
  ∀ p ∈ I, ∀ q ∈ I, p ≠ q → ¬ S.incompatible p q

theorem isCompatible_empty (S : PolymerSystem Polymer) :
    IsCompatible S (∅ : Finset Polymer) := by
  simp [IsCompatible]

theorem isCompatible_singleton (S : PolymerSystem Polymer) (p : Polymer) :
    IsCompatible S ({p} : Finset Polymer) := by
  simp [IsCompatible]

theorem isCompatible_subset (S : PolymerSystem Polymer)
    {I J : Finset Polymer} (hIJ : I ⊆ J) (hJ : IsCompatible S J) :
    IsCompatible S I := by
  intro p hp q hq hpq
  exact hJ p (hIJ hp) q (hIJ hq) hpq

/-- The admissible finite polymer collections in a volume `V`. -/
def admissibleCollections (S : PolymerSystem Polymer) (V : Finset Polymer) :
    Finset (Finset Polymer) :=
  V.powerset.filter (fun I => IsCompatible S I)

@[simp]
theorem mem_admissibleCollections (S : PolymerSystem Polymer)
    (V I : Finset Polymer) :
    I ∈ admissibleCollections S V ↔ I ⊆ V ∧ IsCompatible S I := by
  simp [admissibleCollections]

theorem empty_mem_admissibleCollections (S : PolymerSystem Polymer)
    (V : Finset Polymer) :
    (∅ : Finset Polymer) ∈ admissibleCollections S V := by
  simp [admissibleCollections, IsCompatible]

theorem admissibleCollections_subset_powerset
    (S : PolymerSystem Polymer) (V : Finset Polymer) :
    admissibleCollections S V ⊆ V.powerset := by
  intro I hI
  exact (Finset.mem_filter.mp hI).1

/-- Product of activities over a finite polymer collection. -/
def polymerWeight (activity : Activity Polymer) (I : Finset Polymer) : ℝ :=
  ∏ p in I, activity p

@[simp]
theorem polymerWeight_empty (activity : Activity Polymer) :
    polymerWeight activity (∅ : Finset Polymer) = 1 := by
  simp [polymerWeight]

@[simp]
theorem polymerWeight_singleton (activity : Activity Polymer) (p : Polymer) :
    polymerWeight activity ({p} : Finset Polymer) = activity p := by
  simp [polymerWeight]

theorem polymerWeight_nonneg (activity : Activity Polymer)
    (I : Finset Polymer) (hactivity : ∀ p ∈ I, 0 ≤ activity p) :
    0 ≤ polymerWeight activity I := by
  exact Finset.prod_nonneg hactivity

theorem polymerWeight_pos (activity : Activity Polymer)
    (I : Finset Polymer) (hactivity : ∀ p ∈ I, 0 < activity p) :
    0 < polymerWeight activity I := by
  exact Finset.prod_pos hactivity

/-- The finite-volume polymer partition function. -/
def finitePartitionFunction (S : PolymerSystem Polymer) (V : Finset Polymer)
    (activity : Activity Polymer) : ℝ :=
  ∑ I in admissibleCollections S V, polymerWeight activity I

@[simp]
theorem finitePartitionFunction_empty (S : PolymerSystem Polymer)
    (activity : Activity Polymer) :
    finitePartitionFunction S (∅ : Finset Polymer) activity = 1 := by
  simp [finitePartitionFunction, admissibleCollections, IsCompatible,
    polymerWeight]

theorem finitePartitionFunction_nonneg_of_nonneg
    (S : PolymerSystem Polymer) (V : Finset Polymer)
    (activity : Activity Polymer)
    (hactivity : ∀ p ∈ V, 0 ≤ activity p) :
    0 ≤ finitePartitionFunction S V activity := by
  unfold finitePartitionFunction
  apply Finset.sum_nonneg
  intro I hI
  have hsub : I ⊆ V :=
    (mem_admissibleCollections S V I).mp hI |>.1
  exact polymerWeight_nonneg activity I (fun p hp => hactivity p (hsub hp))

theorem finitePartitionFunction_pos_of_pos
    (S : PolymerSystem Polymer) (V : Finset Polymer)
    (activity : Activity Polymer)
    (hactivity : ∀ p ∈ V, 0 < activity p) :
    0 < finitePartitionFunction S V activity := by
  unfold finitePartitionFunction
  apply Finset.sum_pos'
  · intro I hI
    have hsub : I ⊆ V :=
      (mem_admissibleCollections S V I).mp hI |>.1
    exact polymerWeight_pos activity I (fun p hp => hactivity p (hsub hp))
  · exact ⟨∅, empty_mem_admissibleCollections S V,
      by simp [polymerWeight]⟩

/-- The polymers in a finite volume that are incompatible with a chosen root.
The root itself is included because incompatibility is reflexive. -/
def incompatibleNeighbors (S : PolymerSystem Polymer) (V : Finset Polymer)
    (root : Polymer) : Finset Polymer :=
  V.filter (fun q => S.incompatible root q)

theorem incompatibleNeighbors_subset (S : PolymerSystem Polymer)
    (V : Finset Polymer) (root : Polymer) :
    incompatibleNeighbors S V root ⊆ V := by
  exact Finset.filter_subset _ _

theorem root_mem_incompatibleNeighbors (S : PolymerSystem Polymer)
    (V : Finset Polymer) (root : Polymer) (hroot : root ∈ V) :
    root ∈ incompatibleNeighbors S V root := by
  exact Finset.mem_filter.mpr ⟨hroot, S.incompatible_refl root⟩

/-- The finite Kotecký--Preiss row sum at a root. -/
def kpRowSum (S : PolymerSystem Polymer) (V : Finset Polymer)
    (activity size : Activity Polymer) (root : Polymer) : ℝ :=
  ∑ q in incompatibleNeighbors S V root,
    |activity q| * Real.exp (size q)

theorem kpRowSum_nonneg (S : PolymerSystem Polymer) (V : Finset Polymer)
    (activity size : Activity Polymer) (root : Polymer) :
    0 ≤ kpRowSum S V activity size root := by
  unfold kpRowSum
  apply Finset.sum_nonneg
  intro q hq
  exact mul_nonneg (abs_nonneg _) (Real.exp_pos _).le

/-- Finite-volume Kotecký--Preiss smallness: the size function is
nonnegative and every incompatibility row is bounded by the size at its root.
The corresponding infinite-volume statement is obtained by requiring this
condition on each finite volume or by replacing the finite sum with a `tsum`.
-/
def KoteckyPreissCondition (S : PolymerSystem Polymer) (V : Finset Polymer)
    (activity size : Activity Polymer) : Prop :=
  (∀ p ∈ V, 0 ≤ size p) ∧
    (∀ p ∈ V, kpRowSum S V activity size p ≤ size p)

theorem koteckyPreissCondition_size_nonneg
    (S : PolymerSystem Polymer) (V : Finset Polymer)
    (activity size : Activity Polymer)
    (hKP : KoteckyPreissCondition S V activity size) :
    ∀ p ∈ V, 0 ≤ size p :=
  hKP.1

theorem koteckyPreissCondition_row_bound
    (S : PolymerSystem Polymer) (V : Finset Polymer)
    (activity size : Activity Polymer)
    (hKP : KoteckyPreissCondition S V activity size) :
    ∀ p ∈ V, kpRowSum S V activity size p ≤ size p :=
  hKP.2

theorem koteckyPreissCondition_empty (S : PolymerSystem Polymer)
    (activity size : Activity Polymer) :
    KoteckyPreissCondition S (∅ : Finset Polymer) activity size := by
  simp [KoteckyPreissCondition]

/-- Collections containing a specified root.  This is the finite rooted
boundary on which a cluster estimate will later be stated. -/
def rootedCollections (S : PolymerSystem Polymer) (V : Finset Polymer)
    (root : Polymer) : Finset (Finset Polymer) :=
  (admissibleCollections S V).filter (fun I => root ∈ I)

@[simp]
theorem mem_rootedCollections (S : PolymerSystem Polymer) (V : Finset Polymer)
    (root : Polymer) (I : Finset Polymer) :
    I ∈ rootedCollections S V root ↔
      I ⊆ V ∧ IsCompatible S I ∧ root ∈ I := by
  simp [rootedCollections, and_assoc]

/-- A pinned collection omits the root itself and remains compatible after the
root is inserted.  This form exposes the activity of the pinned root as a
separate factor. -/
def pinnedCollections (S : PolymerSystem Polymer) (V : Finset Polymer)
    (root : Polymer) : Finset (Finset Polymer) :=
  (admissibleCollections S (V.erase root)).filter
    (fun I => IsCompatible S (insert root I))

@[simp]
theorem mem_pinnedCollections (S : PolymerSystem Polymer) (V : Finset Polymer)
    (root : Polymer) (I : Finset Polymer) :
    I ∈ pinnedCollections S V root ↔
      I ⊆ V.erase root ∧ IsCompatible S I ∧
        IsCompatible S (insert root I) := by
  simp [pinnedCollections, and_assoc]

theorem empty_mem_pinnedCollections (S : PolymerSystem Polymer)
    (V : Finset Polymer) (root : Polymer) :
    (∅ : Finset Polymer) ∈ pinnedCollections S V root := by
  rw [Finset.mem_filter]
  constructor
  · exact empty_mem_admissibleCollections S (V.erase root)
  · simpa using isCompatible_singleton S root

/-- The rooted finite polymer weight. -/
def rootedPartitionFunction (S : PolymerSystem Polymer) (V : Finset Polymer)
    (activity : Activity Polymer) (root : Polymer) : ℝ :=
  ∑ I in rootedCollections S V root, polymerWeight activity I

/-- The pinned finite polymer weight, with the root activity factored out. -/
def pinnedPartitionFunction (S : PolymerSystem Polymer) (V : Finset Polymer)
    (activity : Activity Polymer) (root : Polymer) : ℝ :=
  activity root *
    ∑ I in pinnedCollections S V root, polymerWeight activity I

theorem rootedPartitionFunction_nonneg_of_nonneg
    (S : PolymerSystem Polymer) (V : Finset Polymer)
    (activity : Activity Polymer) (root : Polymer)
    (hactivity : ∀ p ∈ V, 0 ≤ activity p) :
    0 ≤ rootedPartitionFunction S V activity root := by
  unfold rootedPartitionFunction
  apply Finset.sum_nonneg
  intro I hI
  have hsub : I ⊆ V :=
    (mem_rootedCollections S V root I).mp hI |>.1
  exact polymerWeight_nonneg activity I (fun p hp => hactivity p (hsub hp))

theorem rootedPartitionFunction_pos_of_pos
    (S : PolymerSystem Polymer) (V : Finset Polymer)
    (activity : Activity Polymer) (root : Polymer) (hroot : root ∈ V)
    (hactivity : ∀ p ∈ V, 0 < activity p) :
    0 < rootedPartitionFunction S V activity root := by
  unfold rootedPartitionFunction
  apply Finset.sum_pos'
  · intro I hI
    have hsub : I ⊆ V :=
      (mem_rootedCollections S V root I).mp hI |>.1
    exact polymerWeight_pos activity I (fun p hp => hactivity p (hsub hp))
  · refine ⟨{root}, ?_, ?_⟩
    · rw [Finset.mem_filter]
      constructor
      · rw [mem_admissibleCollections]
        exact ⟨Finset.singleton_subset_iff.mpr hroot,
          isCompatible_singleton S root⟩
      · simp
    · simpa [polymerWeight] using hactivity root hroot

theorem pinnedPartitionFunction_nonneg_of_nonneg
    (S : PolymerSystem Polymer) (V : Finset Polymer)
    (activity : Activity Polymer) (root : Polymer) (hroot : root ∈ V)
    (hactivity : ∀ p ∈ V, 0 ≤ activity p) :
    0 ≤ pinnedPartitionFunction S V activity root := by
  unfold pinnedPartitionFunction
  apply mul_nonneg
  · exact hactivity root hroot
  · apply Finset.sum_nonneg
    intro I hI
    have hsub : I ⊆ V.erase root :=
      (mem_pinnedCollections S V root I).mp hI |>.1
    exact polymerWeight_nonneg activity I (fun p hp =>
      hactivity p (Finset.mem_of_mem_erase (hsub hp)))

theorem pinnedPartitionFunction_pos_of_pos
    (S : PolymerSystem Polymer) (V : Finset Polymer)
    (activity : Activity Polymer) (root : Polymer) (hroot : root ∈ V)
    (hactivity : ∀ p ∈ V, 0 < activity p) :
    0 < pinnedPartitionFunction S V activity root := by
  unfold pinnedPartitionFunction
  apply mul_pos
  · exact hactivity root hroot
  · apply Finset.sum_pos'
    · intro I hI
      have hsub : I ⊆ V.erase root :=
        (mem_pinnedCollections S V root I).mp hI |>.1
      exact polymerWeight_pos activity I (fun p hp =>
        hactivity p (Finset.mem_of_mem_erase (hsub hp)))
    · exact ⟨∅, empty_mem_pinnedCollections S V root,
        by simp [polymerWeight]⟩

end Pphi2.ClusterExpansion.KPClean
