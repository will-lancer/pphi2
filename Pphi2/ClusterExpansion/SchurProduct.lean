/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Matrix.Order

/-!
# Schur-product positivity

The Hadamard product of two finite positive-semidefinite real matrices is
positive semidefinite.  The proof restricts their positive-semidefinite
Kronecker product to the diagonal copy of the index set.
-/

namespace Pphi2.ClusterExpansion

variable {ι : Type*} [Fintype ι]

/-- Project-level entry point for Mathlib's Schur product theorem. -/
theorem schurProduct_posSemidef {A B : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (Matrix.hadamard A B).PosSemidef :=
  hA.hadamard hB

end Pphi2.ClusterExpansion
