/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cell-weighted source powers for cylinder pullbacks

The centered temporal source estimate supplies the pointwise majorant needed
by the finite weighted interpolation lemma.  This file packages the two
estimates into the cylinder-level source-power bound.
-/

import Pphi2.AsymTorus.AsymDDJSourceSampling
import Pphi2.AsymTorus.AsymDDJWeightedDecay

noncomputable section

namespace Pphi2

open GaussianField MeasureTheory

theorem asymRawSource_weightedLpPow_le_of_centered_decay
    (Ls p : ℝ) [Fact (0 < Ls)] (hp : 1 ≤ p) :
    ∃ (C : ℝ), 0 < C ∧
      ∃ (q : Seminorm ℝ (CylinderTestFunction Ls)), Continuous q ∧
        ∀ (Lt : ℝ) [Fact (0 < Lt)], 1 ≤ Lt →
          ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
            (a : ℝ) (ha : 0 < a),
            (Nt : ℝ) * a = Lt → (Ns : ℝ) * a = Ls →
            a ≤ 1 →
            ∀ f : CylinderTestFunction Ls,
              asymWeightedLpPow p a
                  (asymRawSource a
                    (asymLatticeTestFnIso Lt Ls Nt Ns a
                      (cylinderToTorusEmbed Lt Ls f))) ≤
                C * Real.rpow (q f) p := by
  obtain ⟨A, q, hA, hq, hpoint⟩ :=
    asymRawSource_pointwise_centered_decay Ls
  let C : ℝ := 3 * Ls * Real.rpow A p
  refine ⟨C, ?_, q, hq, ?_⟩
  · dsimp [C]
    exact mul_pos (mul_pos (by norm_num) (Fact.out : 0 < Ls))
      (Real.rpow_pos_of_pos hA p)
  · intro Lt _ hLt1 Nt Ns _ _ a ha hLtphys hLsphys ha1 f
    have hq_nonneg : 0 ≤ q f := apply_nonneg q f
    have hsource_point : ∀ x : AsymLatticeSites Nt Ns,
        |asymRawSource a
            (asymLatticeTestFnIso Lt Ls Nt Ns a
              (cylinderToTorusEmbed Lt Ls f)) x| ≤
          (A * q f) /
            (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2 := by
      intro x
      simpa [mul_assoc] using
        hpoint Lt hLt1 Nt Ns a ha hLtphys hLsphys f x
    have hweighted :=
      asymWeightedLpPow_le_of_centered_temporal_decay
        a Ls (A * q f) p
        (asymRawSource a
          (asymLatticeTestFnIso Lt Ls Nt Ns a
            (cylinderToTorusEmbed Lt Ls f)))
        ha ha1 (Fact.out : 0 < Ls)
        (mul_nonneg hA.le hq_nonneg) hLsphys hp hsource_point
    calc
      asymWeightedLpPow p a
          (asymRawSource a
            (asymLatticeTestFnIso Lt Ls Nt Ns a
              (cylinderToTorusEmbed Lt Ls f))) ≤
          3 * Ls * Real.rpow (A * q f) p := hweighted
      _ = C * Real.rpow (q f) p := by
        dsimp [C]
        have hmul :
            Real.rpow (A * q f) p =
              Real.rpow A p * Real.rpow (q f) p :=
          Real.mul_rpow hA.le hq_nonneg
        rw [hmul]
        ring

end Pphi2
