/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/

import Pphi2.IRLimit.CylinderEmbedding
import Pphi2.AsymTorus.AsymTorusOS
import Pphi2.OSforGFF.TimeTranslation

/-!
# Link Reflection on the Asymmetric Torus and Cylinder

Small scaffolding for the Phase-2 cylinder RP adapter. The link reflection is
the shifted reflection `t ↦ -t - a`, implemented as time reflection after time
translation by `a`.
-/

noncomputable section

namespace Pphi2

open GaussianField Filter TimeTranslation

private theorem schwartzTranslation_continuous_in_τ
    (h : SchwartzMap ℝ ℝ) :
    Continuous (fun τ : ℝ => schwartzTranslation τ h) := by
  let T : SchwartzMap ℝ ℝ ≃L[ℝ] SchwartzMap (EuclideanSpace ℝ (Fin 1)) ℝ :=
    schwartzDomCongr euclideanFin1Equiv
  have hbridge : (fun τ : ℝ => schwartzTranslation τ h) =
      fun τ : ℝ => T.symm (timeTranslationSchwartz (-τ) (T h)) := by
    funext τ
    apply T.injective
    ext u
    simp [T, schwartzDomCongr, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
      timeTranslationSchwartz_apply, schwartzTranslation_apply, euclideanFin1Equiv,
      timeShift]
    ring_nf
  rw [hbridge]
  exact T.symm.continuous.comp
    ((continuous_timeTranslationSchwartz (T h)).comp continuous_neg)

private theorem schwartzTranslation_seminorm_bound
    (k n : ℕ) (τ : ℝ) (h : SchwartzMap ℝ ℝ) :
    (SchwartzMap.seminorm ℝ k n) (schwartzTranslation τ h) ≤
    (1 + |τ|) ^ k * (2 : ℝ) ^ k *
      ((SchwartzMap.seminorm ℝ k n) h +
        (SchwartzMap.seminorm ℝ 0 n) h + 1) := by
  apply SchwartzMap.seminorm_le_bound'
  · positivity
  intro x
  have h_deriv : iteratedDeriv n (⇑(schwartzTranslation τ h)) x =
      iteratedDeriv n (⇑h) (x - τ) := by
    exact congr_fun (iteratedDeriv_comp_sub_const n (⇑h) τ) x
  rw [h_deriv]
  set w := x - τ with hw
  have hx_eq : x = w + τ := by
    rw [hw]
    ring
  have h_absx : |x| ^ k ≤ (1 + |τ|) ^ k * (1 + |w|) ^ k := by
    have h1 : |x| ≤ |w| + |τ| := by
      rw [hx_eq]
      exact abs_add_le w τ
    have h2 : |x| ≤ (1 + |τ|) * (1 + |w|) := by
      calc |x| ≤ |w| + |τ| := h1
        _ ≤ (1 + |τ|) * (1 + |w|) := by
          nlinarith [abs_nonneg τ, abs_nonneg w]
    calc |x| ^ k ≤ ((1 + |τ|) * (1 + |w|)) ^ k := by
          apply pow_le_pow_left₀ (abs_nonneg x) h2
      _ = (1 + |τ|) ^ k * (1 + |w|) ^ k := by rw [mul_pow]
  let S_k := (SchwartzMap.seminorm ℝ k n) h
  let S_0 := (SchwartzMap.seminorm ℝ 0 n) h
  have h_weighted : (1 + |w|) ^ k * ‖iteratedDeriv n (⇑h) w‖ ≤
      (2 : ℝ) ^ k * (S_k + S_0 + 1) := by
    have h_one_plus :
        (1 + |w|) ^ k ≤ (2 : ℝ) ^ k * max 1 (|w| ^ k) := by
      by_cases hw1 : |w| ≤ 1
      · have hpow : (1 + |w|) ^ k ≤ (2 : ℝ) ^ k := by
          apply pow_le_pow_left₀ (by linarith [abs_nonneg w])
          linarith
        have hmax : max 1 (|w| ^ k) = 1 :=
          max_eq_left (pow_le_one₀ (abs_nonneg w) hw1)
        rw [hmax, mul_one]
        exact hpow
      · push Not at hw1
        have hlin : 1 + |w| ≤ 2 * |w| := by linarith
        have hpow : (1 + |w|) ^ k ≤ (2 * |w|) ^ k := by
          apply pow_le_pow_left₀ (by linarith [abs_nonneg w]) hlin
        have hmax : max 1 (|w| ^ k) = |w| ^ k :=
          max_eq_right (one_le_pow₀ hw1.le)
        rw [hmax]
        simpa [mul_pow] using hpow
    have hS0 : ‖iteratedDeriv n (⇑h) w‖ ≤ S_0 := by
      have := SchwartzMap.le_seminorm' ℝ 0 n h w
      simpa [S_0] using this
    have hSk : |w| ^ k * ‖iteratedDeriv n (⇑h) w‖ ≤ S_k := by
      simpa [S_k] using SchwartzMap.le_seminorm' ℝ k n h w
    calc (1 + |w|) ^ k * ‖iteratedDeriv n (⇑h) w‖
        ≤ ((2 : ℝ) ^ k * max 1 (|w| ^ k)) *
            ‖iteratedDeriv n (⇑h) w‖ := by
          exact mul_le_mul_of_nonneg_right h_one_plus (norm_nonneg _)
      _ = (2 : ℝ) ^ k *
            (max 1 (|w| ^ k) * ‖iteratedDeriv n (⇑h) w‖) := by ring
      _ ≤ (2 : ℝ) ^ k *
          (‖iteratedDeriv n (⇑h) w‖ +
            |w| ^ k * ‖iteratedDeriv n (⇑h) w‖) := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) k)
          have hmaxle := max_le_add_of_nonneg
            (by positivity : 0 ≤ (1 : ℝ)) (pow_nonneg (abs_nonneg w) k)
          calc max 1 (|w| ^ k) * ‖iteratedDeriv n (⇑h) w‖
              ≤ (1 + |w| ^ k) * ‖iteratedDeriv n (⇑h) w‖ := by
                exact mul_le_mul_of_nonneg_right hmaxle (norm_nonneg _)
            _ = ‖iteratedDeriv n (⇑h) w‖ +
                |w| ^ k * ‖iteratedDeriv n (⇑h) w‖ := by ring
      _ ≤ (2 : ℝ) ^ k * (S_k + S_0) := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) k)
          linarith
      _ ≤ (2 : ℝ) ^ k * (S_k + S_0 + 1) := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) k)
          linarith
  calc |x| ^ k * ‖iteratedDeriv n (⇑h) w‖
      ≤ ((1 + |τ|) ^ k * (1 + |w|) ^ k) *
          ‖iteratedDeriv n (⇑h) w‖ := by
        exact mul_le_mul_of_nonneg_right h_absx (norm_nonneg _)
    _ = (1 + |τ|) ^ k *
          ((1 + |w|) ^ k * ‖iteratedDeriv n (⇑h) w‖) := by ring
    _ ≤ (1 + |τ|) ^ k * ((2 : ℝ) ^ k * (S_k + S_0 + 1)) := by
        apply mul_le_mul_of_nonneg_left h_weighted
        positivity
    _ = (1 + |τ|) ^ k * (2 : ℝ) ^ k *
        ((SchwartzMap.seminorm ℝ k n) h +
          (SchwartzMap.seminorm ℝ 0 n) h + 1) := by
        simp [S_k, S_0]
        ring

private theorem schwartz_standard_basis_poly_bound
    (i : ℕ × ℕ) :
    ∃ D > 0, ∃ S : ℕ, ∀ m : ℕ,
      (schwartzSeminormFamily ℝ ℝ ℝ i)
        (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) m) ≤
      D * (1 + (m : ℝ)) ^ S := by
  classical
  have hq_cont :
      Continuous
        (schwartzSeminormFamily ℝ ℝ ℝ i : Seminorm ℝ (SchwartzMap ℝ ℝ)) :=
    (schwartz_withSeminorms (𝕜 := ℝ) (E := ℝ) (F := ℝ)).continuous_seminorm i
  obtain ⟨t, Cnn, hCnn, hle⟩ := Seminorm.bound_of_continuous
    (DyninMityaginSpace.h_with (E := SchwartzMap ℝ ℝ))
    (schwartzSeminormFamily ℝ ℝ ℝ i) hq_cont
  obtain ⟨D, hD, S, hbasis⟩ := finset_sup_poly_bound
    DyninMityaginSpace.p t (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ))
    (fun j _ => DyninMityaginSpace.basis_growth (E := SchwartzMap ℝ ℝ) j)
  refine ⟨(Cnn : ℝ) * D, ?_, S, fun m => ?_⟩
  · have hCpos : (0 : ℝ) < Cnn :=
      NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hCnn)
    positivity
  · calc (schwartzSeminormFamily ℝ ℝ ℝ i)
          (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) m)
        ≤ (Cnn : ℝ) * (t.sup DyninMityaginSpace.p)
            (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) m) := hle _
      _ ≤ (Cnn : ℝ) * (D * (1 + (m : ℝ)) ^ S) := by
          apply mul_le_mul_of_nonneg_left (hbasis m)
          exact NNReal.coe_nonneg Cnn
      _ = (Cnn : ℝ) * D * (1 + (m : ℝ)) ^ S := by ring

private theorem schwartzTranslation_standard_basis_uniform_bound
    (i : ℕ × ℕ) :
    ∃ D > 0, ∃ S : ℕ, ∀ τ : ℝ, |τ| < 1 → ∀ m : ℕ,
      (schwartzSeminormFamily ℝ ℝ ℝ i)
        (schwartzTranslation τ
          (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) m)) ≤
      D * (1 + (m : ℝ)) ^ S := by
  obtain ⟨Dk, hDk, Sk, hbk⟩ := schwartz_standard_basis_poly_bound i
  obtain ⟨D0, hD0, S0, hb0⟩ := schwartz_standard_basis_poly_bound (0, i.2)
  refine ⟨(2 : ℝ) ^ (2 * i.1) * (Dk + D0 + 1), ?_,
    max Sk S0, fun τ hτ m => ?_⟩
  · positivity
  · have hτpow : (1 + |τ|) ^ i.1 ≤ (2 : ℝ) ^ i.1 := by
      apply pow_le_pow_left₀ (by linarith [abs_nonneg τ])
      linarith
    have hbase : (1 : ℝ) ≤ 1 + (m : ℝ) := by
      have hmnonneg : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
      linarith
    have hpowk :
        (1 + (m : ℝ)) ^ Sk ≤ (1 + (m : ℝ)) ^ max Sk S0 :=
      pow_le_pow_right₀ hbase (le_max_left Sk S0)
    have hpow0 :
        (1 + (m : ℝ)) ^ S0 ≤ (1 + (m : ℝ)) ^ max Sk S0 :=
      pow_le_pow_right₀ hbase (le_max_right Sk S0)
    have hk' :
        (SchwartzMap.seminorm ℝ i.1 i.2)
          (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) m) ≤
        Dk * (1 + (m : ℝ)) ^ max Sk S0 := by
      calc
        _ ≤ Dk * (1 + (m : ℝ)) ^ Sk := by
          simpa [schwartzSeminormFamily] using hbk m
        _ ≤ Dk * (1 + (m : ℝ)) ^ max Sk S0 := by
          exact mul_le_mul_of_nonneg_left hpowk (le_of_lt hDk)
    have h0' :
        (SchwartzMap.seminorm ℝ 0 i.2)
          (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) m) ≤
        D0 * (1 + (m : ℝ)) ^ max Sk S0 := by
      calc
        _ ≤ D0 * (1 + (m : ℝ)) ^ S0 := by
          simpa [schwartzSeminormFamily] using hb0 m
        _ ≤ D0 * (1 + (m : ℝ)) ^ max Sk S0 := by
          exact mul_le_mul_of_nonneg_left hpow0 (le_of_lt hD0)
    have hone : (1 : ℝ) ≤ (1 + (m : ℝ)) ^ max Sk S0 :=
      one_le_pow₀ hbase
    calc
      (schwartzSeminormFamily ℝ ℝ ℝ i)
          (schwartzTranslation τ
            (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) m))
        = (SchwartzMap.seminorm ℝ i.1 i.2)
            (schwartzTranslation τ
              (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) m)) := by rfl
      _ ≤ (1 + |τ|) ^ i.1 * (2 : ℝ) ^ i.1 *
          ((SchwartzMap.seminorm ℝ i.1 i.2)
              (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) m) +
            (SchwartzMap.seminorm ℝ 0 i.2)
              (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) m) + 1) :=
        schwartzTranslation_seminorm_bound i.1 i.2 τ _
      _ ≤ (2 : ℝ) ^ i.1 * (2 : ℝ) ^ i.1 *
          ((Dk + D0 + 1) * (1 + (m : ℝ)) ^ max Sk S0) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_right hτpow (pow_nonneg (by norm_num) i.1)
          · calc
              (SchwartzMap.seminorm ℝ i.1 i.2)
                  (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) m) +
                  (SchwartzMap.seminorm ℝ 0 i.2)
                    (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) m) + 1
                ≤ Dk * (1 + (m : ℝ)) ^ max Sk S0 +
                    D0 * (1 + (m : ℝ)) ^ max Sk S0 +
                    1 * (1 + (m : ℝ)) ^ max Sk S0 := by
                    nlinarith [hk', h0', hone]
              _ = (Dk + D0 + 1) * (1 + (m : ℝ)) ^ max Sk S0 := by
                ring
          · positivity
          · positivity
      _ = (2 : ℝ) ^ (2 * i.1) * (Dk + D0 + 1) *
          (1 + (m : ℝ)) ^ max Sk S0 := by
          rw [← pow_add]
          ring_nf

private theorem schwartzTranslation_standard_finset_uniform_bound
    (s : Finset (ℕ × ℕ)) :
    ∃ D > 0, ∃ S : ℕ, ∀ τ : ℝ, |τ| < 1 → ∀ m : ℕ,
      (s.sup (schwartzSeminormFamily ℝ ℝ ℝ))
        (schwartzTranslation τ
          (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) m)) ≤
      D * (1 + (m : ℝ)) ^ S := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
      refine ⟨1, one_pos, 0, fun τ hτ m => ?_⟩
      simp [Finset.sup_empty, Seminorm.bot_eq_zero]
  | cons i s his ih =>
      obtain ⟨Di, hDi, Si, hbi⟩ :=
        schwartzTranslation_standard_basis_uniform_bound i
      obtain ⟨Ds, hDs, Ss, hbs⟩ := ih
      refine ⟨Di + Ds, by linarith, max Si Ss, fun τ hτ m => ?_⟩
      have hbase : (1 : ℝ) ≤ 1 + (m : ℝ) := by
        have hmnonneg : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
        linarith
      have hpowi :
          (1 + (m : ℝ)) ^ Si ≤ (1 + (m : ℝ)) ^ max Si Ss :=
        pow_le_pow_right₀ hbase (le_max_left Si Ss)
      have hpows :
          (1 + (m : ℝ)) ^ Ss ≤ (1 + (m : ℝ)) ^ max Si Ss :=
        pow_le_pow_right₀ hbase (le_max_right Si Ss)
      have hi_bound :
          (schwartzSeminormFamily ℝ ℝ ℝ i)
            (schwartzTranslation τ
              (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) m)) ≤
          (Di + Ds) * (1 + (m : ℝ)) ^ max Si Ss := by
        calc
          _ ≤ Di * (1 + (m : ℝ)) ^ Si := hbi τ hτ m
          _ ≤ Di * (1 + (m : ℝ)) ^ max Si Ss := by
            exact mul_le_mul_of_nonneg_left hpowi (le_of_lt hDi)
          _ ≤ (Di + Ds) * (1 + (m : ℝ)) ^ max Si Ss := by
            apply mul_le_mul_of_nonneg_right (by linarith)
            positivity
      have hs_bound :
          (s.sup (schwartzSeminormFamily ℝ ℝ ℝ))
            (schwartzTranslation τ
              (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) m)) ≤
          (Di + Ds) * (1 + (m : ℝ)) ^ max Si Ss := by
        calc
          _ ≤ Ds * (1 + (m : ℝ)) ^ Ss := hbs τ hτ m
          _ ≤ Ds * (1 + (m : ℝ)) ^ max Si Ss := by
            exact mul_le_mul_of_nonneg_left hpows (le_of_lt hDs)
          _ ≤ (Di + Ds) * (1 + (m : ℝ)) ^ max Si Ss := by
            apply mul_le_mul_of_nonneg_right (by linarith)
            positivity
      rw [Finset.sup_cons]
      exact sup_le hi_bound hs_bound

private theorem schwartzTranslation_basis_finset_uniform_bound
    (s : Finset (DyninMityaginSpace.ι (E := SchwartzMap ℝ ℝ))) :
    ∃ D > 0, ∃ S : ℕ, ∀ τ : ℝ, |τ| < 1 → ∀ m : ℕ,
      (s.sup (DyninMityaginSpace.p (E := SchwartzMap ℝ ℝ)))
        (schwartzTranslation τ
          (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) m)) ≤
      D * (1 + (m : ℝ)) ^ S := by
  classical
  have hq_cont :
      Continuous ((s.sup (DyninMityaginSpace.p (E := SchwartzMap ℝ ℝ))) :
        Seminorm ℝ (SchwartzMap ℝ ℝ)) := by
    apply Seminorm.continuous_of_le _
      (Seminorm.finset_sup_le_sum
        (DyninMityaginSpace.p (E := SchwartzMap ℝ ℝ)) s)
    change Continuous fun (x : SchwartzMap ℝ ℝ) =>
      (Seminorm.coeFnAddMonoidHom ℝ (SchwartzMap ℝ ℝ))
        (∑ i ∈ s, DyninMityaginSpace.p (E := SchwartzMap ℝ ℝ) i) x
    simp_rw [map_sum, Finset.sum_apply]
    exact continuous_finsetSum _ fun i _ =>
      (DyninMityaginSpace.h_with (E := SchwartzMap ℝ ℝ)).continuous_seminorm i
  obtain ⟨t, Cnn, hCnn, hle⟩ := Seminorm.bound_of_continuous
    (schwartz_withSeminorms (𝕜 := ℝ) (E := ℝ) (F := ℝ))
    (s.sup (DyninMityaginSpace.p (E := SchwartzMap ℝ ℝ))) hq_cont
  obtain ⟨D, hD, S, hb⟩ := schwartzTranslation_standard_finset_uniform_bound t
  refine ⟨(Cnn : ℝ) * D, ?_, S, fun τ hτ m => ?_⟩
  · have hCpos : (0 : ℝ) < Cnn :=
      NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hCnn)
    positivity
  · calc
      (s.sup (DyninMityaginSpace.p (E := SchwartzMap ℝ ℝ)))
          (schwartzTranslation τ
            (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) m))
        ≤ (Cnn : ℝ) * (t.sup (schwartzSeminormFamily ℝ ℝ ℝ))
            (schwartzTranslation τ
              (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) m)) := hle _
      _ ≤ (Cnn : ℝ) * (D * (1 + (m : ℝ)) ^ S) := by
          apply mul_le_mul_of_nonneg_left (hb τ hτ m)
          exact NNReal.coe_nonneg Cnn
      _ = (Cnn : ℝ) * D * (1 + (m : ℝ)) ^ S := by ring

private theorem cylinderTranslation_mapImage_uniform_bound
    {Ls : ℝ} [Fact (0 < Ls)] (k : ℕ) :
    ∃ K > 0, ∃ S : ℕ, ∀ τ : ℝ, |τ| < 1 → ∀ m : ℕ,
      RapidDecaySeq.rapidDecaySeminorm k
        (GaussianField.mapImage
          (GaussianField.circleTranslation Ls 0)
          (GaussianField.schwartzTranslation τ) m) ≤
      K * (1 + (m : ℝ)) ^ S := by
  classical
  set E_s := GaussianField.SmoothMap_Circle Ls ℝ
  set E_t := SchwartzMap ℝ ℝ
  obtain ⟨C, s1, s2, hpure⟩ :=
    GaussianField.NuclearTensorProduct.pure_seminorm_bound
      (E₁ := E_s) (E₂ := E_t) k
  set ψ_s := DyninMityaginSpace.basis (E := E_s)
  set ψ_t := DyninMityaginSpace.basis (E := E_t)
  obtain ⟨D1, hD1, S1, hb1⟩ := GaussianField.finset_sup_poly_bound
    DyninMityaginSpace.p s1 (DyninMityaginSpace.basis (E := E_s))
    (fun i _ => DyninMityaginSpace.basis_growth (E := E_s) i)
  obtain ⟨D2, hD2, S2, hb2⟩ :=
    schwartzTranslation_basis_finset_uniform_bound s2
  refine ⟨((C : ℝ) + 1) * D1 * D2, ?_, S1 + S2, fun τ hτ m => ?_⟩
  · positivity
  · set a := (Nat.unpair m).1
    set b := (Nat.unpair m).2
    have ha_le : (1 + (a : ℝ)) ≤ (1 + (m : ℝ)) :=
      add_le_add_right (Nat.cast_le.mpr (Nat.unpair_left_le m)) 1
    have hb_le : (1 + (b : ℝ)) ≤ (1 + (m : ℝ)) :=
      add_le_add_right (Nat.cast_le.mpr (Nat.unpair_right_le m)) 1
    have hbasea : (0 : ℝ) ≤ 1 + (a : ℝ) := by positivity
    have hbaseb : (0 : ℝ) ≤ 1 + (b : ℝ) := by positivity
    change (RapidDecaySeq.rapidDecaySeminorm k
      (GaussianField.NuclearTensorProduct.pure
        (GaussianField.circleTranslation Ls 0 (ψ_s a))
        (GaussianField.schwartzTranslation τ (ψ_t b)))) ≤
      ((C : ℝ) + 1) * D1 * D2 * (1 + (m : ℝ)) ^ (S1 + S2)
    calc
      (RapidDecaySeq.rapidDecaySeminorm k
        (GaussianField.NuclearTensorProduct.pure
          (GaussianField.circleTranslation Ls 0 (ψ_s a))
          (GaussianField.schwartzTranslation τ (ψ_t b))))
        ≤ (C : ℝ) * (s1.sup DyninMityaginSpace.p)
            (GaussianField.circleTranslation Ls 0 (ψ_s a)) *
          (s2.sup DyninMityaginSpace.p)
            (GaussianField.schwartzTranslation τ (ψ_t b)) := hpure _ _
      _ ≤ (C : ℝ) * (D1 * (1 + (a : ℝ)) ^ S1) *
          (D2 * (1 + (b : ℝ)) ^ S2) := by
          apply mul_le_mul
          · apply mul_le_mul_of_nonneg_left _ (NNReal.coe_nonneg C)
            simpa [ψ_s, circleTranslation_zero] using hb1 a
          · simpa [ψ_t] using hb2 τ hτ b
          · positivity
          · positivity
      _ ≤ (C : ℝ) * (D1 * (1 + (m : ℝ)) ^ S1) *
          (D2 * (1 + (m : ℝ)) ^ S2) := by
          gcongr
      _ = (C : ℝ) * D1 * D2 * (1 + (m : ℝ)) ^ (S1 + S2) := by
          rw [pow_add]
          ring
      _ ≤ ((C : ℝ) + 1) * D1 * D2 *
          (1 + (m : ℝ)) ^ (S1 + S2) := by
          gcongr
          linarith [NNReal.coe_nonneg C]

private theorem cylinderTranslation_tendsto_zero
    {Ls : ℝ} [Fact (0 < Ls)] (f : CylinderTestFunction Ls) :
    Tendsto (fun τ : ℝ => cylinderTranslation Ls 0 τ f)
      (nhds 0) (nhds f) := by
  classical
  set E_s := GaussianField.SmoothMap_Circle Ls ℝ
  set E_t := SchwartzMap ℝ ℝ
  have h_ws : WithSeminorms (RapidDecaySeq.rapidDecaySeminorm :
      ℕ → Seminorm ℝ (CylinderTestFunction Ls)) :=
    RapidDecaySeq.rapidDecay_withSeminorms
  have hzero : cylinderTranslation Ls 0 0 f = f := by
    simp [cylinderTranslation, circleTranslation_zero, schwartzTranslation_zero,
      nuclearTensorProduct_mapCLM_id]
  suffices Tendsto (fun τ : ℝ => cylinderTranslation Ls 0 τ f)
      (nhds 0) (nhds (cylinderTranslation Ls 0 0 f)) by
    simpa [hzero] using this
  apply (h_ws.tendsto_nhds _ _).mpr
  intro k ε hε
  obtain ⟨K, hK, S, h_uniform_bound⟩ :=
    cylinderTranslation_mapImage_uniform_bound (Ls := Ls) k
  set ψ_s := DyninMityaginSpace.basis (E := E_s)
  set ψ_t := DyninMityaginSpace.basis (E := E_t)
  set g : ℕ → ℝ := fun m => |f.val m| * (2 * K) * (1 + (m : ℝ)) ^ S
  have hg_summable : Summable g := by
    have := f.rapid_decay S
    exact (this.mul_left (2 * K)).congr (fun m => by
      simp [g]
      ring)
  have h_tail_small : ∃ N : ℕ, ∑' m, g (m + N) < ε / 2 := by
    have h_tendsto : Filter.Tendsto (fun N => ∑' m, g (m + N))
        Filter.atTop (nhds 0) :=
      tendsto_sum_nat_add g
    have h_ev := (Filter.Tendsto.eventually h_tendsto
      (Iio_mem_nhds (show (0 : ℝ) < ε / 2 by linarith)))
    rw [Filter.Eventually, Filter.mem_atTop_sets] at h_ev
    obtain ⟨N, hN⟩ := h_ev
    exact ⟨N, hN N le_rfl⟩
  obtain ⟨N, hN_tail⟩ := h_tail_small
  have h_mapImage_cont : ∀ m,
      Continuous (fun τ : ℝ => GaussianField.mapImage
        (GaussianField.circleTranslation Ls 0)
        (GaussianField.schwartzTranslation τ) m) := by
    intro m
    change Continuous (fun τ : ℝ =>
      GaussianField.NuclearTensorProduct.pure
        (GaussianField.circleTranslation Ls 0 (ψ_s (Nat.unpair m).1))
        (GaussianField.schwartzTranslation τ (ψ_t (Nat.unpair m).2)))
    exact GaussianField.NuclearTensorProduct.pure_continuous.comp
      (continuous_const.prodMk
        (schwartzTranslation_continuous_in_τ (ψ_t (Nat.unpair m).2)))
  have h_head_small : ∀ᶠ τ in nhds (0 : ℝ),
      ∑ m ∈ Finset.range N, |f.val m| *
        RapidDecaySeq.rapidDecaySeminorm k
          (GaussianField.mapImage
            (GaussianField.circleTranslation Ls 0)
            (GaussianField.schwartzTranslation τ) m -
           GaussianField.mapImage
            (GaussianField.circleTranslation Ls 0)
            (GaussianField.schwartzTranslation 0) m) < ε / 2 := by
    have h_tendsto : Filter.Tendsto (fun τ : ℝ =>
        ∑ m ∈ Finset.range N, |f.val m| *
          RapidDecaySeq.rapidDecaySeminorm k
            (GaussianField.mapImage
              (GaussianField.circleTranslation Ls 0)
              (GaussianField.schwartzTranslation τ) m -
             GaussianField.mapImage
              (GaussianField.circleTranslation Ls 0)
              (GaussianField.schwartzTranslation 0) m))
        (nhds 0) (nhds 0) := by
      have h_tendsto_sum : Filter.Tendsto (fun τ : ℝ =>
          ∑ m ∈ Finset.range N, |f.val m| *
            RapidDecaySeq.rapidDecaySeminorm k
              (GaussianField.mapImage
                (GaussianField.circleTranslation Ls 0)
                (GaussianField.schwartzTranslation τ) m -
               GaussianField.mapImage
                (GaussianField.circleTranslation Ls 0)
                (GaussianField.schwartzTranslation 0) m))
          (nhds 0) (nhds (∑ m ∈ Finset.range N, |f.val m| * 0)) := by
        apply tendsto_finsetSum
        intro m _
        apply Filter.Tendsto.const_mul
        have h_cont_diff : Continuous (fun τ : ℝ =>
            GaussianField.mapImage
              (GaussianField.circleTranslation Ls 0)
              (GaussianField.schwartzTranslation τ) m -
            GaussianField.mapImage
              (GaussianField.circleTranslation Ls 0)
              (GaussianField.schwartzTranslation 0) m) :=
          (h_mapImage_cont m).sub continuous_const
        have h_comp_cont : Continuous (fun τ : ℝ =>
            RapidDecaySeq.rapidDecaySeminorm k
              (GaussianField.mapImage
                (GaussianField.circleTranslation Ls 0)
                (GaussianField.schwartzTranslation τ) m -
               GaussianField.mapImage
                (GaussianField.circleTranslation Ls 0)
                (GaussianField.schwartzTranslation 0) m)) :=
          (h_ws.continuous_seminorm k).comp h_cont_diff
        have h_val_at_zero : RapidDecaySeq.rapidDecaySeminorm k
            (GaussianField.mapImage
              (GaussianField.circleTranslation Ls 0)
              (GaussianField.schwartzTranslation 0) m -
             GaussianField.mapImage
              (GaussianField.circleTranslation Ls 0)
              (GaussianField.schwartzTranslation 0) m) = 0 := by
          rw [sub_self]
          exact map_zero _
        have h_at := h_comp_cont.continuousAt (x := (0 : ℝ))
        rw [ContinuousAt] at h_at
        simpa only [h_val_at_zero] using h_at
      simpa using h_tendsto_sum
    exact h_tendsto.eventually (Iio_mem_nhds (by linarith))
  have h_small : ∀ᶠ τ in nhds (0 : ℝ), |τ| < 1 := by
    rw [Metric.eventually_nhds_iff]
    refine ⟨1, one_pos, fun τ hτ => ?_⟩
    simpa [Real.dist_eq, sub_zero] using hτ
  have h_mapCLM_basis :
      ∀ (T₁ : E_s →L[ℝ] E_s) (T₂ : E_t →L[ℝ] E_t) (m : ℕ),
      GaussianField.nuclearTensorProduct_mapCLM T₁ T₂ (RapidDecaySeq.basisVec m) =
      GaussianField.mapImage T₁ T₂ m := by
    intro T₁ T₂ m
    have hbv := GaussianField.NuclearTensorProduct.basisVec_eq_pure
      (DyninMityaginSpace.HasBiorthogonalBasis.coeff_basis (E := E_s))
      (DyninMityaginSpace.HasBiorthogonalBasis.coeff_basis (E := E_t)) m
    rw [hbv]
    exact GaussianField.nuclearTensorProduct_mapCLM_pure T₁ T₂ _ _
  have h_hasSum : ∀ (T₁ : E_s →L[ℝ] E_s) (T₂ : E_t →L[ℝ] E_t),
      HasSum (fun m => f.val m • GaussianField.mapImage T₁ T₂ m)
        (GaussianField.nuclearTensorProduct_mapCLM T₁ T₂ f) := by
    intro T₁ T₂
    have h := (RapidDecaySeq.hasSum_basisVec f).mapL
      (GaussianField.nuclearTensorProduct_mapCLM T₁ T₂)
    simp only at h
    convert h using 1
    ext1 m
    calc f.val m • GaussianField.mapImage T₁ T₂ m
        = f.val m • GaussianField.nuclearTensorProduct_mapCLM T₁ T₂
            (RapidDecaySeq.basisVec m) := by rw [h_mapCLM_basis]
      _ = GaussianField.nuclearTensorProduct_mapCLM T₁ T₂
            (f.val m • RapidDecaySeq.basisVec m) :=
          ((GaussianField.nuclearTensorProduct_mapCLM T₁ T₂).map_smul
            (f.val m) (RapidDecaySeq.basisVec m)).symm
  have h_diff_hasSum : ∀ τ : ℝ,
      HasSum (fun m => f.val m •
        (GaussianField.mapImage
          (GaussianField.circleTranslation Ls 0)
          (GaussianField.schwartzTranslation τ) m -
         GaussianField.mapImage
          (GaussianField.circleTranslation Ls 0)
          (GaussianField.schwartzTranslation 0) m))
        (cylinderTranslation Ls 0 τ f - cylinderTranslation Ls 0 0 f) := by
    intro τ
    have h1 := h_hasSum (GaussianField.circleTranslation Ls 0)
      (GaussianField.schwartzTranslation τ)
    have h2 := h_hasSum (GaussianField.circleTranslation Ls 0)
      (GaussianField.schwartzTranslation 0)
    simpa [cylinderTranslation, smul_sub] using h1.sub h2
  filter_upwards [h_head_small, h_small] with τ hv_head hτ_small
  set d := fun m => GaussianField.mapImage
    (GaussianField.circleTranslation Ls 0)
    (GaussianField.schwartzTranslation τ) m -
    GaussianField.mapImage
    (GaussianField.circleTranslation Ls 0)
    (GaussianField.schwartzTranslation 0) m
  have h_dk_summable : Summable (fun m => |f.val m| *
      RapidDecaySeq.rapidDecaySeminorm k (d m)) :=
    hg_summable.of_nonneg_of_le
      (fun m => mul_nonneg (abs_nonneg _) (apply_nonneg _ _))
      (fun m => by
        have h_sub := map_sub_le_add (RapidDecaySeq.rapidDecaySeminorm k)
          (GaussianField.mapImage
            (GaussianField.circleTranslation Ls 0)
            (GaussianField.schwartzTranslation τ) m)
          (GaussianField.mapImage
            (GaussianField.circleTranslation Ls 0)
            (GaussianField.schwartzTranslation 0) m)
        calc |f.val m| * RapidDecaySeq.rapidDecaySeminorm k (d m)
            ≤ |f.val m| * (2 * K * (1 + (m : ℝ)) ^ S) :=
            mul_le_mul_of_nonneg_left
              (calc RapidDecaySeq.rapidDecaySeminorm k (d m)
                  ≤ _ := h_sub
                _ ≤ K * (1 + (m : ℝ)) ^ S +
                    K * (1 + (m : ℝ)) ^ S :=
                  add_le_add (h_uniform_bound τ hτ_small m)
                    (h_uniform_bound 0 (by norm_num) m)
                _ = 2 * K * (1 + (m : ℝ)) ^ S := by ring)
              (abs_nonneg _)
          _ = g m := by simp [g]; ring)
  have h_seminorm_le : RapidDecaySeq.rapidDecaySeminorm k
      (cylinderTranslation Ls 0 τ f - cylinderTranslation Ls 0 0 f) ≤
      ∑' m, |f.val m| * RapidDecaySeq.rapidDecaySeminorm k (d m) := by
    apply le_of_tendsto
      ((h_ws.continuous_seminorm k).continuousAt.tendsto.comp
        (h_diff_hasSum τ).tendsto_sum_nat)
    rw [Filter.Eventually, Filter.mem_atTop_sets]
    refine ⟨0, fun n _ => ?_⟩
    calc (RapidDecaySeq.rapidDecaySeminorm k)
          (∑ m ∈ Finset.range n, f.val m • d m)
        ≤ ∑ m ∈ Finset.range n,
            (RapidDecaySeq.rapidDecaySeminorm k) (f.val m • d m) :=
          (Finset.range n).le_sum_of_subadditive _
            (map_zero (RapidDecaySeq.rapidDecaySeminorm k)).le
            (RapidDecaySeq.rapidDecaySeminorm k).add_le'
            (fun m => f.val m • d m)
      _ = ∑ m ∈ Finset.range n,
            |f.val m| * (RapidDecaySeq.rapidDecaySeminorm k) (d m) := by
          congr 1
          ext m
          change (RapidDecaySeq.rapidDecaySeminorm k) (f.val m • d m) =
            |f.val m| * (RapidDecaySeq.rapidDecaySeminorm k) (d m)
          change ∑' n, |(f.val m • d m).val n| * (1 + (n : ℝ)) ^ k =
            |f.val m| * ∑' n, |(d m).val n| * (1 + (n : ℝ)) ^ k
          conv_lhs =>
            arg 1
            ext n
            rw [show (f.val m • d m).val n = f.val m * (d m).val n from rfl,
              abs_mul, mul_assoc]
          rw [tsum_mul_left]
      _ ≤ ∑' m, |f.val m| * (RapidDecaySeq.rapidDecaySeminorm k) (d m) :=
          h_dk_summable.sum_le_tsum _
            (fun m _ => mul_nonneg (abs_nonneg _) (apply_nonneg _ _))
  have h_tsum_split : ∑' m, |f.val m| *
        RapidDecaySeq.rapidDecaySeminorm k (d m) ≤
      (∑ m ∈ Finset.range N, |f.val m| *
        RapidDecaySeq.rapidDecaySeminorm k (d m)) +
      ∑' m, g (m + N) := by
    have h_dk_le_g : ∀ m, |f.val m| *
        RapidDecaySeq.rapidDecaySeminorm k (d m) ≤ g m := by
      intro m
      calc |f.val m| * RapidDecaySeq.rapidDecaySeminorm k (d m)
          ≤ |f.val m| * (2 * K * (1 + (m : ℝ)) ^ S) :=
            mul_le_mul_of_nonneg_left
              ((map_sub_le_add (RapidDecaySeq.rapidDecaySeminorm k) _ _).trans
                ((add_le_add (h_uniform_bound τ hτ_small m)
                  (h_uniform_bound 0 (by norm_num) m)).trans (by linarith)))
              (abs_nonneg _)
        _ = g m := by simp [g]; ring
    rw [(h_dk_summable.sum_add_tsum_nat_add N).symm]
    exact add_le_add le_rfl
      (Summable.tsum_le_tsum
        (fun m => h_dk_le_g (m + N))
        (h_dk_summable.comp_injective (add_left_injective N))
        (hg_summable.comp_injective (add_left_injective N)))
  calc RapidDecaySeq.rapidDecaySeminorm k
        (cylinderTranslation Ls 0 τ f - cylinderTranslation Ls 0 0 f)
      ≤ ∑' m, |f.val m| * RapidDecaySeq.rapidDecaySeminorm k (d m) :=
        h_seminorm_le
    _ ≤ (∑ m ∈ Finset.range N, |f.val m| *
          RapidDecaySeq.rapidDecaySeminorm k (d m)) +
        ∑' m, g (m + N) := h_tsum_split
    _ < ε / 2 + ε / 2 := add_lt_add hv_head hN_tail
    _ = ε := by ring

variable (Lt Ls : ℝ) [Fact (0 < Lt)] [Fact (0 < Ls)]

/-- Link reflection on asymmetric-torus tests: `t ↦ -t - a`.

The definition is time reflection after time translation by `a`, so on pure
temporal factors it sends `f(t)` to `f(-t - a)`. -/
def asymTorusLinkReflection (a : ℝ) :
    AsymTorusTestFunction Lt Ls →L[ℝ] AsymTorusTestFunction Lt Ls :=
  (asymTorusTimeReflection Lt Ls).comp (asymTorusTranslation Lt Ls (a, 0))

/-- Link reflection on cylinder tests: `t ↦ -t - a`.

The cylinder convention has time in the second tensor factor; this is time
reflection after time translation by `a`. -/
def cylinderLinkReflection (a : ℝ) :
    CylinderTestFunction Ls →L[ℝ] CylinderTestFunction Ls :=
  (cylinderTimeReflection Ls).comp (cylinderTranslation Ls 0 a)

/-- The cylinder-to-torus embedding intertwines the cylinder and torus link reflections. -/
theorem cylinderToTorusEmbed_comp_linkReflection
    (a : ℝ) (f : CylinderTestFunction Ls) :
    cylinderToTorusEmbed Lt Ls (cylinderLinkReflection Ls a f) =
    asymTorusLinkReflection Lt Ls a (cylinderToTorusEmbed Lt Ls f) := by
  simp only [cylinderLinkReflection, asymTorusLinkReflection,
    ContinuousLinearMap.comp_apply]
  rw [cylinderToTorusEmbed_comp_timeReflection]
  rw [cylinderToTorusEmbed_comp_timeTranslation]

/-- As the link spacing goes to zero, torus link reflection tends to site reflection. -/
theorem asymTorusLinkReflection_tendsto_timeReflection
    (f : AsymTorusTestFunction Lt Ls) :
    Tendsto (fun a : ℝ => asymTorusLinkReflection Lt Ls a f)
      (nhds 0) (nhds (asymTorusTimeReflection Lt Ls f)) := by
  have hpair :
      Tendsto (fun a : ℝ => (a, (0 : ℝ)))
        (nhds 0) (nhds ((0 : ℝ), (0 : ℝ))) := by
    exact (continuous_id.prodMk continuous_const).continuousAt.tendsto
  have htrans :
      Tendsto
        (fun a : ℝ => asymTorusTranslation Lt Ls (a, (0 : ℝ)) f)
        (nhds 0)
        (nhds (asymTorusTranslation Lt Ls ((0 : ℝ), (0 : ℝ)) f)) := by
    exact (asymTorusTranslation_continuous_in_v Lt Ls f).continuousAt.tendsto.comp hpair
  have hzero : asymTorusTranslation Lt Ls ((0 : ℝ), (0 : ℝ)) f = f := by
    simp [asymTorusTranslation, circleTranslation_zero, nuclearTensorProduct_mapCLM_id]
  have htrans' :
      Tendsto
        (fun a : ℝ => asymTorusTranslation Lt Ls (a, (0 : ℝ)) f)
        (nhds 0) (nhds f) := by
    simpa [hzero] using htrans
  have hΘ :
      Tendsto
        (fun a : ℝ =>
          asymTorusTimeReflection Lt Ls
            (asymTorusTranslation Lt Ls (a, (0 : ℝ)) f))
        (nhds 0) (nhds (asymTorusTimeReflection Lt Ls f)) := by
    exact (asymTorusTimeReflection Lt Ls).cont.continuousAt.tendsto.comp htrans'
  simpa [asymTorusLinkReflection, ContinuousLinearMap.comp_apply] using hΘ

/-- As the link spacing goes to zero, cylinder link reflection tends to time reflection. -/
theorem cylinderLinkReflection_tendsto_timeReflection
    (f : CylinderTestFunction Ls) :
    Tendsto (fun a : ℝ => cylinderLinkReflection Ls a f)
      (nhds 0) (nhds (cylinderTimeReflection Ls f)) := by
  have htrans :
      Tendsto (fun a : ℝ => cylinderTranslation Ls 0 a f)
        (nhds 0) (nhds f) :=
    cylinderTranslation_tendsto_zero (Ls := Ls) f
  have hΘ :
      Tendsto
        (fun a : ℝ =>
          cylinderTimeReflection Ls (cylinderTranslation Ls 0 a f))
        (nhds 0) (nhds (cylinderTimeReflection Ls f)) := by
    exact (cylinderTimeReflection Ls).cont.continuousAt.tendsto.comp htrans
  simpa [cylinderLinkReflection, ContinuousLinearMap.comp_apply] using hΘ

end Pphi2
