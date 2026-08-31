/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.ENNReal.Basic
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

open scoped BigOperators ENNReal

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

/-- A signed real activity together with an `ENNReal` majorant.  This is the
interface for the later continuous-spin activity estimates: the majorant is
the quantity to which finite summation and analytic bounds should be applied.
No Kotecký--Preiss estimate is asserted by this data structure. -/
structure SignedActivityMajorant (Polymer : Type*) where
  activity : Activity Polymer
  majorant : Polymer → ℝ≥0∞
  dominates : ∀ p, ENNReal.ofReal |activity p| ≤ majorant p

theorem signedActivityMajorant_dominates
    (M : SignedActivityMajorant Polymer) (p : Polymer) :
    ENNReal.ofReal |M.activity p| ≤ M.majorant p :=
  M.dominates p

/-- The canonical majorant for a real activity. -/
def absActivityMajorant (activity : Activity Polymer) :
    SignedActivityMajorant Polymer where
  activity := activity
  majorant := fun p => ENNReal.ofReal |activity p|
  dominates := fun p => le_rfl

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

theorem polymerWeight_eq_activity_mul_erase
    (activity : Activity Polymer) (I : Finset Polymer) (root : Polymer)
    (hroot : root ∈ I) :
    polymerWeight activity I =
      activity root * polymerWeight activity (I.erase root) := by
  calc
    polymerWeight activity I =
        polymerWeight activity (insert root (I.erase root)) := by
          rw [Finset.insert_erase hroot]
    _ = activity root * polymerWeight activity (I.erase root) := by
      rw [polymerWeight, Finset.prod_insert (Finset.notMem_erase root I)]

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

/-- Erasing a rooted polymer gives a pinned collection. -/
theorem erase_mem_pinnedCollections
    (S : PolymerSystem Polymer) (V : Finset Polymer) (root : Polymer)
    {I : Finset Polymer} (hI : I ∈ rootedCollections S V root) :
    I.erase root ∈ pinnedCollections S V root := by
  have hI' := (mem_rootedCollections S V root I).mp hI
  apply (mem_pinnedCollections S V root (I.erase root)).mpr
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    exact Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hp,
      hI'.1 (Finset.mem_of_mem_erase hp)⟩
  · exact isCompatible_subset S (Finset.erase_subset root I) hI'.2.1
  · rw [Finset.insert_erase hI'.2.2]
    exact hI'.2.1

/-- Inserting a root into a pinned collection gives a rooted collection. -/
theorem insert_mem_rootedCollections
    (S : PolymerSystem Polymer) (V : Finset Polymer) (root : Polymer)
    (hroot : root ∈ V) {I : Finset Polymer}
    (hI : I ∈ pinnedCollections S V root) :
    insert root I ∈ rootedCollections S V root := by
  have hI' := (mem_pinnedCollections S V root I).mp hI
  apply (mem_rootedCollections S V root (insert root I)).mpr
  refine ⟨?_, hI'.2.2, Finset.mem_insert_self root I⟩
  exact Finset.insert_subset_iff.mpr ⟨hroot,
    fun p hp => Finset.mem_of_mem_erase (hI'.1 hp)⟩

/-- Erase and insert are inverse maps on the rooted and pinned collection
finsets. -/
def eraseRootEquiv
    (S : PolymerSystem Polymer) (V : Finset Polymer) (root : Polymer)
    (hroot : root ∈ V) :
    rootedCollections S V root ≃ pinnedCollections S V root :=
  { toFun := fun I =>
      ⟨I.1.erase root, erase_mem_pinnedCollections S V root I.2⟩
    invFun := fun I =>
      ⟨insert root I.1, insert_mem_rootedCollections S V root hroot I.2⟩
    left_inv := by
      intro I
      apply Subtype.ext
      exact Finset.insert_erase
        ((mem_rootedCollections S V root I.1).mp I.2).2.2
    right_inv := by
      intro I
      apply Subtype.ext
      have hI := (mem_pinnedCollections S V root I.1).mp I.2
      have hnot : root ∉ I.1 := fun hmem =>
        Finset.notMem_erase root V (hI.1 hmem)
      exact Finset.erase_insert hnot }

/-- The rooted finite collection sum.  It is named as a collection sum rather
than a partition function because it is a root-pinned sub-sum. -/
def rootedCollectionSum (S : PolymerSystem Polymer) (V : Finset Polymer)
    (activity : Activity Polymer) (root : Polymer)
    (hroot : root ∈ V) : ℝ :=
  ∑ I in rootedCollections S V root, polymerWeight activity I

/-- The pinned finite collection sum, with the root activity factored out. -/
def pinnedCollectionSum (S : PolymerSystem Polymer) (V : Finset Polymer)
    (activity : Activity Polymer) (root : Polymer)
    (hroot : root ∈ V) : ℝ :=
  activity root *
    ∑ I in pinnedCollections S V root, polymerWeight activity I

/-- Erase and insert reindex the rooted collection sum. -/
theorem rootedCollectionSum_eq_pinnedCollectionSum
    (S : PolymerSystem Polymer) (V : Finset Polymer)
    (activity : Activity Polymer) (root : Polymer) (hroot : root ∈ V) :
    rootedCollectionSum S V activity root hroot =
      pinnedCollectionSum S V activity root hroot := by
  unfold rootedCollectionSum pinnedCollectionSum
  rw [Finset.mul_sum]
  refine Finset.sum_bij'
    (fun I _ => I.erase root) (fun I _ => insert root I) ?_ ?_ ?_ ?_ ?_
  · intro I hI
    exact erase_mem_pinnedCollections S V root hI
  · intro I hI
    exact insert_mem_rootedCollections S V root hroot hI
  · intro I hI
    exact Finset.insert_erase
      ((mem_rootedCollections S V root I).mp hI).2.2
  · intro I hI
    have hI' := (mem_pinnedCollections S V root I).mp hI
    have hnot : root ∉ I := fun hmem =>
      Finset.notMem_erase root V (hI'.1 hmem)
    exact Finset.erase_insert hnot
  · intro I hI
    exact polymerWeight_eq_activity_mul_erase activity I root
      ((mem_rootedCollections S V root I).mp hI).2.2

theorem rootedCollectionSum_nonneg_of_nonneg
    (S : PolymerSystem Polymer) (V : Finset Polymer)
    (activity : Activity Polymer) (root : Polymer)
    (hroot : root ∈ V) (hactivity : ∀ p ∈ V, 0 ≤ activity p) :
    0 ≤ rootedCollectionSum S V activity root hroot := by
  unfold rootedCollectionSum
  apply Finset.sum_nonneg
  intro I hI
  have hsub : I ⊆ V :=
    (mem_rootedCollections S V root I).mp hI |>.1
  exact polymerWeight_nonneg activity I (fun p hp => hactivity p (hsub hp))

theorem rootedCollectionSum_pos_of_pos
    (S : PolymerSystem Polymer) (V : Finset Polymer)
    (activity : Activity Polymer) (root : Polymer) (hroot : root ∈ V)
    (hactivity : ∀ p ∈ V, 0 < activity p) :
    0 < rootedCollectionSum S V activity root hroot := by
  unfold rootedCollectionSum
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

theorem pinnedCollectionSum_nonneg_of_nonneg
    (S : PolymerSystem Polymer) (V : Finset Polymer)
    (activity : Activity Polymer) (root : Polymer) (hroot : root ∈ V)
    (hactivity : ∀ p ∈ V, 0 ≤ activity p) :
    0 ≤ pinnedCollectionSum S V activity root hroot := by
  unfold pinnedCollectionSum
  apply mul_nonneg
  · exact hactivity root hroot
  · apply Finset.sum_nonneg
    intro I hI
    have hsub : I ⊆ V.erase root :=
      (mem_pinnedCollections S V root I).mp hI |>.1
    exact polymerWeight_nonneg activity I (fun p hp =>
      hactivity p (Finset.mem_of_mem_erase (hsub hp)))

theorem pinnedCollectionSum_pos_of_pos
    (S : PolymerSystem Polymer) (V : Finset Polymer)
    (activity : Activity Polymer) (root : Polymer) (hroot : root ∈ V)
    (hactivity : ∀ p ∈ V, 0 < activity p) :
    0 < pinnedCollectionSum S V activity root hroot := by
  unfold pinnedCollectionSum
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
