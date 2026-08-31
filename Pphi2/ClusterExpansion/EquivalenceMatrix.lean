/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Fintype.Quotient
import Pphi2.ClusterExpansion.SchurProduct

/-!
# Positive-semidefinite equivalence matrices

The zero-one matrix of a finite equivalence relation is a sum of the rank-one
matrices of its equivalence classes.
-/

open scoped BigOperators

namespace Pphi2.ClusterExpansion

/-- The zero-one matrix of a relation. -/
def relationMatrix {ι : Type*} [DecidableEq ι]
    (r : ι → ι → Prop) [DecidableRel r] : Matrix ι ι ℝ :=
  fun i j => if r i j then 1 else 0

/-- A finite equivalence relation has a positive-semidefinite zero-one
matrix. -/
theorem relationMatrix_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ι → ι → Prop) [DecidableRel r]
    (hrefl : Reflexive r) (hsymm : Symmetric r) (htrans : Transitive r) :
    (relationMatrix r).PosSemidef := by
  let setoid : Setoid ι :=
    { r := r
      iseqv :=
        { refl := hrefl
          symm := fun h => hsymm h
          trans := fun h₁ h₂ => htrans h₁ h₂ } }
  let classVector : Quotient setoid → ι → ℝ := fun c i =>
    if Quotient.mk setoid i = c then 1 else 0
  have hrank : ∀ c : Quotient setoid,
      (Matrix.vecMulVec (classVector c) (classVector c)).PosSemidef := by
    intro c
    simpa using Matrix.posSemidef_vecMulVec_self_star (classVector c)
  have hsum :
      (∑ c : Quotient setoid,
        Matrix.vecMulVec (classVector c) (classVector c)) =
        relationMatrix r := by
    ext i j
    by_cases hij : r i j
    · have hq : Quotient.mk setoid i = Quotient.mk setoid j :=
        Quotient.sound hij
      simp only [Matrix.sum_apply, Matrix.vecMulVec_apply]
      rw [Fintype.sum_eq_single (Quotient.mk setoid i)]
      · simp [classVector, relationMatrix, hij, hq]
      · intro c hc
        simp [classVector, Ne.symm hc]
    · have hq : Quotient.mk setoid i ≠ Quotient.mk setoid j := by
        intro h
        exact hij (show r i j from Quotient.exact h)
      simp only [Matrix.sum_apply, Matrix.vecMulVec_apply]
      rw [Fintype.sum_eq_single (Quotient.mk setoid i)]
      · have hq' : Quotient.mk setoid j ≠ Quotient.mk setoid i := Ne.symm hq
        simp [classVector, relationMatrix, hij, hq']
      · intro c hc
        simp [classVector, Ne.symm hc]
  rw [← hsum]
  exact Matrix.posSemidef_sum Finset.univ fun c _ => hrank c

/-- A finite nonnegative combination of equivalence matrices is positive
semidefinite.  Forest path-min matrices use the nested threshold
connectivity relations in this form. -/
theorem sum_relationMatrix_posSemidef
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (weight : κ → ℝ) (r : κ → ι → ι → Prop)
    [∀ k, DecidableRel (r k)]
    (hweight : ∀ k, 0 ≤ weight k)
    (hrefl : ∀ k, Reflexive (r k))
    (hsymm : ∀ k, Symmetric (r k))
    (htrans : ∀ k, Transitive (r k)) :
    (∑ k : κ, weight k • relationMatrix (r k)).PosSemidef := by
  apply Matrix.posSemidef_sum Finset.univ
  intro k _
  exact (relationMatrix_posSemidef (r k) (hrefl k) (hsymm k) (htrans k)).smul
    (hweight k)

end Pphi2.ClusterExpansion
