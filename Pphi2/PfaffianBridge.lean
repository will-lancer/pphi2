/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.Finset.Sort

/-!
# Ordered indexing of finite subsets

For a finite subset of a linearly ordered ambient type, Mathlib's
`Finset.orderIsoOfFin` identifies the canonical finite index type with the
subset subtype.  The declarations here keep that identification and its
ambient order embedding under stable Pphi2 names.  The inverse is the
direction used when a matching on the ambient subset is reindexed by its
subtype coordinates.
-/

noncomputable section

namespace Pphi2

/-- The increasing enumeration of `s` as its finite subtype. -/
def finsetOrderIsoSubtype {α : Type*} [LinearOrder α] (s : Finset α) :
    Fin s.card ≃o s :=
  s.orderIsoOfFin rfl

/-- The inverse of `finsetOrderIsoSubtype`, from the subtype to its indices. -/
def finsetSubtypeOrderIso {α : Type*} [LinearOrder α] (s : Finset α) :
    s ≃o Fin s.card :=
  (finsetOrderIsoSubtype s).symm

/-- The increasing enumeration of `s` viewed in the ambient ordered type. -/
def finsetOrderEmbedding {α : Type*} [LinearOrder α] (s : Finset α) :
    Fin s.card ↪o α :=
  s.orderEmbOfFin rfl

@[simp]
theorem finsetOrderIsoSubtype_coe {α : Type*} [LinearOrder α] (s : Finset α)
    (i : Fin s.card) :
    (finsetOrderIsoSubtype s i : α) = finsetOrderEmbedding s i := by
  rfl

@[simp]
theorem finsetOrderIsoSubtype_mem {α : Type*} [LinearOrder α] (s : Finset α)
    (i : Fin s.card) :
    (finsetOrderIsoSubtype s i : α) ∈ s := by
  exact (finsetOrderIsoSubtype s i).property

@[simp]
theorem finsetOrderEmbedding_mem {α : Type*} [LinearOrder α] (s : Finset α)
    (i : Fin s.card) :
    finsetOrderEmbedding s i ∈ s := by
  exact Finset.orderEmbOfFin_mem s rfl i

@[simp]
theorem finsetOrderEmbedding_image_univ {α : Type*} [LinearOrder α]
    (s : Finset α) :
    Finset.image (finsetOrderEmbedding s) Finset.univ = s := by
  exact Finset.image_orderEmbOfFin_univ s rfl

theorem finsetOrderIsoSubtype_lt_iff {α : Type*} [LinearOrder α]
    (s : Finset α) (i j : Fin s.card) :
    finsetOrderIsoSubtype s i < finsetOrderIsoSubtype s j ↔ i < j := by
  exact (finsetOrderIsoSubtype s).lt_iff_lt

@[simp]
theorem finsetSubtypeOrderIso_apply_finsetOrderIsoSubtype
    {α : Type*} [LinearOrder α] (s : Finset α) (i : Fin s.card) :
    finsetSubtypeOrderIso s (finsetOrderIsoSubtype s i) = i := by
  exact (finsetOrderIsoSubtype s).symm_apply_apply i

@[simp]
theorem finsetOrderIsoSubtype_apply_finsetSubtypeOrderIso
    {α : Type*} [LinearOrder α] (s : Finset α) (x : s) :
    finsetOrderIsoSubtype s (finsetSubtypeOrderIso s x) = x := by
  exact (finsetOrderIsoSubtype s).apply_symm_apply x

/-- The inverse coordinate is the position of the subtype element in `s.sort`. -/
theorem finsetSubtypeOrderIso_coe {α : Type*} [LinearOrder α] (s : Finset α)
    (x : s) :
    (finsetSubtypeOrderIso s x : ℕ) = s.sort.idxOf (x : α) := by
  exact Finset.orderIsoOfFin_symm_apply s rfl x

end Pphi2

end
