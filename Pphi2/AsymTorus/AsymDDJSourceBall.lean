/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A common deterministic source ball for the DDJ source

The zero-order raw source and its finite Laplacian have separate sampling
estimates.  This file packages them with one continuous cylinder seminorm and
one radius.  The quarter-radius leaves the stronger room needed when the
source is doubled in the finite tilted-integrability argument.
-/

import Pphi2.AsymTorus.AsymDDJSourceLp
import Pphi2.AsymTorus.AsymDDJSourceLaplacianSampling
import Pphi2.AsymTorus.AsymDDJWeightedDecay

noncomputable section

namespace Pphi2

open GaussianField MeasureTheory

/-- The two weighted source-ball inequalities used by the finite DDJ route. -/
def AsymDDJSourceBall
    {Nt Ns : ℕ} [NeZero Nt] [NeZero Ns]
    (n : ℕ) (a : ℝ) (g : AsymLatticeField Nt Ns) : Prop :=
  let p : ℝ := (n : ℝ) / ((n : ℝ) - 1)
  asymWeightedLpPow p a (asymRawSource a g) ≤
      (1 / 4 : ℝ) ^ p ∧
    asymWeightedLpPow p a
      (finiteLaplacianAsymFun Nt Ns a (asymRawSource a g)) ≤
      (1 / 4 : ℝ) ^ p

theorem asymDDJSourceBall_of_centered_decay
    (P : InteractionPolynomial) (Ls : ℝ) [Fact (0 < Ls)] :
    ∃ (r : ℝ) (q : Seminorm ℝ (CylinderTestFunction Ls)),
      0 < r ∧ Continuous q ∧
      ∀ (Lt : ℝ) [Fact (0 < Lt)], (4 : ℝ) ≤ Lt →
        ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
          (a : ℝ) (ha : 0 < a),
          (Nt : ℝ) * a = Lt →
          (Ns : ℝ) * a = Ls →
          a ≤ (1 : ℝ) →
          ∀ f : CylinderTestFunction Ls,
            q f ≤ r →
            AsymDDJSourceBall P.n a
              (asymLatticeTestFnIso Lt Ls Nt Ns a
                (cylinderToTorusEmbed Lt Ls f)) := by
  let p : ℝ := (P.n : ℝ) / ((P.n : ℝ) - 1)
  have hn_nat : 1 < P.n := by
    have h := P.hn_ge
    omega
  have hn_real : 1 < (P.n : ℝ) := by
    exact_mod_cast hn_nat
  have hp_pos : 0 < p := by
    dsimp [p]
    exact div_pos (by positivity) (sub_pos.mpr hn_real)
  have hp : 1 ≤ p := by
    dsimp [p]
    apply (le_div_iff₀ (sub_pos.mpr hn_real)).2
    linarith

  obtain ⟨C₀, hC₀, q₀, hq₀, hsource⟩ :=
    asymRawSource_weightedLpPow_le_of_centered_decay Ls p hp
  obtain ⟨A, hA, q₁, hq₁, hlap⟩ :=
    asymFiniteLaplacianRawSource_pointwise_centered_decay Ls

  let C₁ : ℝ := 3 * Ls * Real.rpow A p
  have hC₁ : 0 < C₁ := by
    dsimp [C₁]
    exact mul_pos (mul_pos (by norm_num) (Fact.out : 0 < Ls))
      (Real.rpow_pos_of_pos hA p)
  let D : ℝ := C₀ + C₁
  have hD : 0 < D := add_pos hC₀ hC₁
  let T : ℝ := (1 / 4 : ℝ) ^ p
  have hT : 0 < T := by
    dsimp [T]
    exact Real.rpow_pos_of_pos (by norm_num) p
  let r : ℝ := Real.rpow (T / D) (1 / p)
  have hTD : 0 < T / D := div_pos hT hD
  have hr : 0 < r := by
    dsimp [r]
    exact Real.rpow_pos_of_pos hTD _
  have hrpow : Real.rpow r p = T / D := by
    simpa [r, one_div] using
      (Real.rpow_inv_rpow hTD.le hp.ne')

  let q : Seminorm ℝ (CylinderTestFunction Ls) := q₀ + q₁
  have hq : Continuous q := by
    change Continuous (fun f : CylinderTestFunction Ls => q₀ f + q₁ f)
    exact hq₀.add hq₁

  refine ⟨r, q, hr, hq, ?_⟩
  intro Lt _ hLt4 Nt Ns _ _ a ha hLtphys hLsphys ha1 f hqf
  let g : AsymLatticeField Nt Ns :=
    asymLatticeTestFnIso Lt Ls Nt Ns a
      (cylinderToTorusEmbed Lt Ls f)
  change
    asymWeightedLpPow p a (asymRawSource a g) ≤
        (1 / 4 : ℝ) ^ p ∧
      asymWeightedLpPow p a
        (finiteLaplacianAsymFun Nt Ns a
          (asymRawSource a g)) ≤
        (1 / 4 : ℝ) ^ p

  have hq₀_le : q₀ f ≤ q f := by
    change q₀ f ≤ q₀ f + q₁ f
    exact le_add_of_nonneg_right (apply_nonneg q₁ f)
  have hq₁_le : q₁ f ≤ q f := by
    change q₁ f ≤ q₀ f + q₁ f
    exact le_add_of_nonneg_left (apply_nonneg q₀ f)
  have hq₀r : q₀ f ≤ r := hq₀_le.trans hqf
  have hq₁r : q₁ f ≤ r := hq₁_le.trans hqf
  have hq₀pow : Real.rpow (q₀ f) p ≤ Real.rpow r p :=
    Real.rpow_le_rpow (apply_nonneg q₀ f) hq₀r hp.le
  have hq₁pow : Real.rpow (q₁ f) p ≤ Real.rpow r p :=
    Real.rpow_le_rpow (apply_nonneg q₁ f) hq₁r hp.le
  have hC₀D : C₀ ≤ D := by
    dsimp [D]
    exact le_add_of_nonneg_right hC₁.le
  have hC₁D : C₁ ≤ D := by
    dsimp [D]
    exact le_add_of_nonneg_left hC₀.le
  have hrpow_nonneg : 0 ≤ Real.rpow r p :=
    Real.rpow_nonneg hr.le p

  have hsource' :
      asymWeightedLpPow p a (asymRawSource a g) ≤
        C₀ * Real.rpow (q₀ f) p := by
    simpa [g] using
      (hsource Lt (by linarith : (1 : ℝ) ≤ Lt) Nt Ns a ha
        hLtphys hLsphys ha1 f)
  have hsource_quarter :
      asymWeightedLpPow p a (asymRawSource a g) ≤ T := by
    calc
      asymWeightedLpPow p a (asymRawSource a g) ≤
          C₀ * Real.rpow (q₀ f) p := hsource'
      _ ≤ C₀ * Real.rpow r p :=
        mul_le_mul_of_nonneg_left hq₀pow hC₀.le
      _ ≤ D * Real.rpow r p :=
        mul_le_mul_of_nonneg_right hC₀D hrpow_nonneg
      _ = T := by
        rw [hrpow]
        field_simp [ne_of_gt hD] <;> ring

  have hpoint :
      ∀ x : AsymLatticeSites Nt Ns,
        |finiteLaplacianAsymFun Nt Ns a (asymRawSource a g) x| ≤
          (A * q₁ f) /
            (1 + a * ((signedVal Nt x.1).natAbs : ℝ)) ^ 2 := by
    intro x
    simpa [g, mul_assoc] using
      (hlap Lt hLt4 Nt Ns a ha hLtphys hLsphys ha1 f x)
  have hlapLp :=
    asymWeightedLpPow_le_of_centered_temporal_decay
      a Ls (A * q₁ f) p
      (finiteLaplacianAsymFun Nt Ns a (asymRawSource a g))
      ha ha1 (Fact.out : 0 < Ls)
      (mul_nonneg hA.le (apply_nonneg q₁ f))
      hLsphys hp hpoint
  have hlap_bound :
      asymWeightedLpPow p a
          (finiteLaplacianAsymFun Nt Ns a (asymRawSource a g)) ≤
        C₁ * Real.rpow (q₁ f) p := by
    calc
      asymWeightedLpPow p a
          (finiteLaplacianAsymFun Nt Ns a (asymRawSource a g)) ≤
          3 * Ls * Real.rpow (A * q₁ f) p := hlapLp
      _ = C₁ * Real.rpow (q₁ f) p := by
        dsimp [C₁]
        have hmul :
            Real.rpow (A * q₁ f) p =
              Real.rpow A p * Real.rpow (q₁ f) p :=
          Real.mul_rpow hA.le (apply_nonneg q₁ f)
        rw [hmul]
        ring
  have hlap_quarter :
      asymWeightedLpPow p a
          (finiteLaplacianAsymFun Nt Ns a (asymRawSource a g)) ≤ T := by
    calc
      asymWeightedLpPow p a
          (finiteLaplacianAsymFun Nt Ns a (asymRawSource a g)) ≤
          C₁ * Real.rpow (q₁ f) p := hlap_bound
      _ ≤ C₁ * Real.rpow r p :=
        mul_le_mul_of_nonneg_left hq₁pow hC₁.le
      _ ≤ D * Real.rpow r p :=
        mul_le_mul_of_nonneg_right hC₁D hrpow_nonneg
      _ = T := by
        rw [hrpow]
        field_simp [ne_of_gt hD] <;> ring

  simpa [T] using And.intro hsource_quarter hlap_quarter

end Pphi2
