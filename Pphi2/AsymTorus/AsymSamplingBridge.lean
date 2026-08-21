/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/

import Pphi2.AsymTorus.AsymContinuumLimit
import Pphi2.IRLimit.CylinderOS
import Pphi2.GeneralResults.WeakLimitMoment
import GaussianField.ConfigurationEmbedding
import GaussianField.Tightness

/-!
# Raw lattice sampling bridges for the isotropic cylinder route

Finite-grid sampling of torus test functions, and the source-independent
adapter that turns a cutoff exponential-moment bound into a cylinder bound.
This is analysis of `evalAsymTorusAtSite` / Dynin–Mityagin expansions, not the
UV Prokhorov limit itself.
-/


noncomputable section

open MeasureTheory GaussianField Filter

namespace Pphi2

variable (Lt Ls : ℝ) [hLt : Fact (0 < Lt)] [hLs : Fact (0 < Ls)]

/-- Bounded-continuous convergence on asymmetric-torus configurations transfers
an exponential-moment estimate directly to the cylinder pullback measures.

This is the source-independent weak-limit adapter used by the direct cylinder
route.  Its bound may vary with the cutoff index; no comparison with a torus
Green function is required. -/
theorem cylinderPullbackMeasure_exponential_moment_of_tendsto_bc
    (μseq : ℕ → Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    (hμseq_prob : ∀ k, IsProbabilityMeasure (μseq k))
    (hμ_prob : IsProbabilityMeasure μ)
    (hbc : ∀ (g : Configuration (AsymTorusTestFunction Lt Ls) → ℝ),
      Continuous g → (∃ B, ∀ x, |g x| ≤ B) →
      Filter.Tendsto (fun k => ∫ ω, g ω ∂(μseq k)) Filter.atTop
        (nhds (∫ ω, g ω ∂μ)))
    (f : CylinderTestFunction Ls)
    (B : ℕ → ℝ) (Binf : ℝ)
    (hB : Filter.Tendsto B Filter.atTop (nhds Binf))
    (h_unif : ∀ k,
      Integrable (fun ω : Configuration (CylinderTestFunction Ls) =>
        Real.exp (|ω f|)) (cylinderPullbackMeasure Lt Ls (μseq k)) ∧
      ∫ ω : Configuration (CylinderTestFunction Ls),
        Real.exp (|ω f|) ∂(cylinderPullbackMeasure Lt Ls (μseq k)) ≤ B k) :
    Integrable (fun ω : Configuration (CylinderTestFunction Ls) =>
      Real.exp (|ω f|)) (cylinderPullbackMeasure Lt Ls μ) ∧
    ∫ ω : Configuration (CylinderTestFunction Ls),
      Real.exp (|ω f|) ∂(cylinderPullbackMeasure Lt Ls μ) ≤ Binf := by
  letI : IsProbabilityMeasure μ := hμ_prob
  let F : AsymTorusTestFunction Lt Ls := cylinderToTorusEmbed Lt Ls f
  have hmeas : Measurable (cylinderPullback Lt Ls) :=
    configuration_measurable_of_eval_measurable _
      (fun φ => configuration_eval_measurable _)
  have hexp_sm : StronglyMeasurable
      (fun ω : Configuration (CylinderTestFunction Ls) => Real.exp (|ω f|)) :=
    (Real.measurable_exp.comp
      (configuration_eval_measurable f).abs).stronglyMeasurable
  have h_unif_torus : ∀ k,
      Integrable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
        Real.exp (|ω F|)) (μseq k) ∧
      ∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
        Real.exp (|ω F|) ∂(μseq k) ≤ B k := by
    intro k
    obtain ⟨hint_cyl, hle_cyl⟩ := h_unif k
    have hint_comp : Integrable
        ((fun ω : Configuration (CylinderTestFunction Ls) => Real.exp (|ω f|)) ∘
          cylinderPullback Lt Ls) (μseq k) := by
      rw [← integrable_map_measure hexp_sm.aestronglyMeasurable hmeas.aemeasurable]
      exact hint_cyl
    have hint_torus : Integrable
        (fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
          Real.exp (|ω F|)) (μseq k) := by
      refine hint_comp.congr (Filter.Eventually.of_forall fun ω => ?_)
      simp [F, Function.comp_def, cylinderPullback_eval]
    have heq :
        ∫ ω : Configuration (CylinderTestFunction Ls),
            Real.exp (|ω f|) ∂(cylinderPullbackMeasure Lt Ls (μseq k)) =
          ∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
            Real.exp (|ω F|) ∂(μseq k) := by
      unfold cylinderPullbackMeasure
      rw [integral_map_of_stronglyMeasurable hmeas hexp_sm]
      simp [F, Function.comp_def, cylinderPullback_eval]
    refine ⟨hint_torus, ?_⟩
    calc
      ∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
          Real.exp (|ω F|) ∂(μseq k) =
          ∫ ω : Configuration (CylinderTestFunction Ls),
            Real.exp (|ω f|) ∂(cylinderPullbackMeasure Lt Ls (μseq k)) := heq.symm
      _ ≤ B k := hle_cyl
  obtain ⟨hint_torus, hle_torus⟩ := weakLimit_exponential_moment
    μseq hμseq_prob μ hbc F B Binf hB h_unif_torus
  obtain ⟨hint_cyl, heq⟩ :=
    cylinderPullback_expMoment_eq Ls Lt μ f hint_torus
  exact ⟨hint_cyl, heq.le.trans hle_torus⟩

/-! ## Bridge: raw fixed-period sampling bound ⟹ cylinder bound -/

/-! ### Raw finite-grid sampling -/

private theorem asym_zmod_sum_eq_range (N : ℕ) [NeZero N] (g : ℕ → ℝ) :
    ∑ x : ZMod N, g (ZMod.val x) = ∑ n ∈ Finset.range N, g n := by
  rw [show ∑ x : ZMod N, g (ZMod.val x) = ∑ n : Fin N, g n.val
    from Fintype.sum_bijective
      (fun (x : ZMod N) =>
        (⟨ZMod.val x, ZMod.val_lt x⟩ : Fin N))
      ⟨fun a b h => ZMod.val_injective N (Fin.mk.inj h),
       fun ⟨n, hn⟩ =>
        ⟨(n : ZMod N), by
          ext; exact ZMod.val_natCast_of_lt hn⟩⟩
      _ _ (fun _ => rfl),
    ← Finset.sum_range (f := g)]

private theorem asym_circleRestriction_inner_tendsto
    (L : ℝ) [Fact (0 < L)]
    (N : ℕ → ℕ) (hN : ∀ k, NeZero (N k))
    (hNtop : Filter.Tendsto N atTop atTop)
    (f g : SmoothMap_Circle L ℝ) :
    Filter.Tendsto
      (fun k =>
        letI : NeZero (N k) := hN k
        ∑ z : ZMod (N k),
          circleRestriction L (N k) f z * circleRestriction L (N k) g z)
      atTop (nhds (∫ x in Set.Icc 0 L, f x * g x)) := by
  have hN1 : Filter.Tendsto (fun k => N k - 1) atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    obtain ⟨K, hK⟩ := Filter.tendsto_atTop_atTop.mp hNtop (b + 1)
    exact ⟨K, fun k hk => by
      have hkb := hK k hk
      omega⟩
  have hNsucc : ∀ k, (N k - 1) + 1 = N k := fun k =>
    Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (hN k).out)
  let hfg : ℝ → ℝ := fun x => f x * g x
  have hfg_cont : Continuous hfg := f.continuous.mul g.continuous
  have hfg_per : Function.Periodic hfg L := f.periodic.mul g.periodic
  have hriem := riemann_sum_periodic_tendsto L hfg hfg_cont hfg_per
  have hcomp := hriem.comp hN1
  have hrewrite :
      (fun k =>
        letI : NeZero (N k) := hN k
        ∑ z : ZMod (N k),
          circleRestriction L (N k) f z * circleRestriction L (N k) g z) =
      (fun k =>
        ∑ n ∈ Finset.range (N k - 1 + 1),
          (L / (↑(N k - 1 + 1) : ℝ)) *
            hfg ((n : ℝ) * L / (↑(N k - 1 + 1) : ℝ))) := by
    funext k
    letI : NeZero (N k) := hN k
    calc
      ∑ z : ZMod (N k),
          circleRestriction L (N k) f z * circleRestriction L (N k) g z =
          ∑ z : ZMod (N k),
            (L / (N k : ℝ)) *
              (f (circlePoint L (N k) z) * g (circlePoint L (N k) z)) := by
        apply Finset.sum_congr rfl
        intro z hz
        simp only [circleRestriction_apply, circleSpacing_eq]
        have hLN : 0 ≤ L / (N k : ℝ) :=
          (div_pos (Fact.out : (0 : ℝ) < L)
            (Nat.cast_pos.mpr (NeZero.pos (N k)))).le
        rw [show Real.sqrt (L / (N k : ℝ)) * f (circlePoint L (N k) z) *
              (Real.sqrt (L / (N k : ℝ)) * g (circlePoint L (N k) z)) =
            (Real.sqrt (L / (N k : ℝ)) * Real.sqrt (L / (N k : ℝ))) *
              (f (circlePoint L (N k) z) * g (circlePoint L (N k) z)) by ring,
          Real.mul_self_sqrt hLN]
      _ = ∑ n ∈ Finset.range (N k),
          (L / (N k : ℝ)) *
            hfg ((n : ℝ) * L / (N k : ℝ)) := by
        simpa [circlePoint, hfg] using
          (asym_zmod_sum_eq_range (N k)
            (fun n => (L / (N k : ℝ)) *
              hfg ((n : ℝ) * L / (N k : ℝ))))
      _ = ∑ n ∈ Finset.range (N k - 1 + 1),
          (L / (↑(N k - 1 + 1) : ℝ)) *
            hfg ((n : ℝ) * L / (↑(N k - 1 + 1) : ℝ)) := by
        simp only [hNsucc k]
  rw [hrewrite]
  simpa only [Function.comp_def] using hcomp

private theorem asym_basis_pair_tendsto
    (Lt Ls : ℝ) [Fact (0 < Lt)] [Fact (0 < Ls)]
    (Nt Ns : ℕ → ℕ) (a : ℕ → ℝ)
    (hNt : ∀ k, NeZero (Nt k)) (hNs : ∀ k, NeZero (Ns k))
    (hNt_top : Filter.Tendsto Nt atTop atTop)
    (hNs_top : Filter.Tendsto Ns atTop atTop)
    (m n : ℕ) :
    Filter.Tendsto
      (fun k =>
        letI : NeZero (Nt k) := hNt k
        letI : NeZero (Ns k) := hNs k
        ∑ x : AsymLatticeSites (Nt k) (Ns k),
          evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x
              (RapidDecaySeq.basisVec m) *
            evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x
              (RapidDecaySeq.basisVec n))
      atTop (nhds (if m = n then 1 else 0)) := by
  let mt := (Nat.unpair m).1
  let ms := (Nat.unpair m).2
  let nt := (Nat.unpair n).1
  let ns := (Nat.unpair n).2
  let bt : SmoothMap_Circle Lt ℝ := DyninMityaginSpace.basis mt
  let bs : SmoothMap_Circle Ls ℝ := DyninMityaginSpace.basis ms
  let ct : SmoothMap_Circle Lt ℝ := DyninMityaginSpace.basis nt
  let cs : SmoothMap_Circle Ls ℝ := DyninMityaginSpace.basis ns
  have htime0 :
      (∫ x in Set.Icc 0 Lt, bt x * ct x) =
        if mt = nt then 1 else 0 := by
    rw [show bt = SmoothMap_Circle.fourierBasis mt from
          dm_basis_eq_fourierBasis (L := Lt) mt,
      show ct = SmoothMap_Circle.fourierBasis nt from
          dm_basis_eq_fourierBasis (L := Lt) nt]
    rw [show (∫ x in Set.Icc 0 Lt,
        SmoothMap_Circle.fourierBasis mt x *
          SmoothMap_Circle.fourierBasis nt x) =
        ∫ x in Set.Icc 0 Lt,
          SmoothMap_Circle.fourierBasis nt x *
            SmoothMap_Circle.fourierBasis mt x by
          congr 1; funext x; ring]
    exact SmoothMap_Circle.fourierCoeffReal_fourierBasis (L := Lt) mt nt
  have hspace0 :
      (∫ x in Set.Icc 0 Ls, bs x * cs x) =
        if ms = ns then 1 else 0 := by
    rw [show bs = SmoothMap_Circle.fourierBasis ms from
          dm_basis_eq_fourierBasis (L := Ls) ms,
      show cs = SmoothMap_Circle.fourierBasis ns from
          dm_basis_eq_fourierBasis (L := Ls) ns]
    rw [show (∫ x in Set.Icc 0 Ls,
        SmoothMap_Circle.fourierBasis ms x *
          SmoothMap_Circle.fourierBasis ns x) =
        ∫ x in Set.Icc 0 Ls,
          SmoothMap_Circle.fourierBasis ns x *
            SmoothMap_Circle.fourierBasis ms x by
          congr 1; funext x; ring]
    exact SmoothMap_Circle.fourierCoeffReal_fourierBasis (L := Ls) ms ns
  have htime := asym_circleRestriction_inner_tendsto Lt Nt hNt hNt_top bt ct
  have hspace := asym_circleRestriction_inner_tendsto Ls Ns hNs hNs_top bs cs
  have htime' : Filter.Tendsto
      (fun k =>
        letI : NeZero (Nt k) := hNt k
        ∑ z : ZMod (Nt k), circleRestriction Lt (Nt k) bt z *
          circleRestriction Lt (Nt k) ct z)
      atTop (nhds (if mt = nt then 1 else 0)) := by
    simpa [htime0] using htime
  have hspace' : Filter.Tendsto
      (fun k =>
        letI : NeZero (Ns k) := hNs k
        ∑ z : ZMod (Ns k), circleRestriction Ls (Ns k) bs z *
          circleRestriction Ls (Ns k) cs z)
      atTop (nhds (if ms = ns then 1 else 0)) := by
    simpa [hspace0] using hspace
  have hprod :
      (fun k =>
        letI : NeZero (Nt k) := hNt k
        letI : NeZero (Ns k) := hNs k
        ∑ x : AsymLatticeSites (Nt k) (Ns k),
          evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x
              (RapidDecaySeq.basisVec m) *
            evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x
              (RapidDecaySeq.basisVec n)) =
      (fun k =>
        (letI : NeZero (Nt k) := hNt k
         ∑ z : ZMod (Nt k), circleRestriction Lt (Nt k) bt z *
           circleRestriction Lt (Nt k) ct z) *
        (letI : NeZero (Ns k) := hNs k
         ∑ z : ZMod (Ns k), circleRestriction Ls (Ns k) bs z *
           circleRestriction Ls (Ns k) cs z)) := by
    funext k
    letI : NeZero (Nt k) := hNt k
    letI : NeZero (Ns k) := hNs k
    simp_rw [evalAsymTorusAtSite_basisVec]
    rw [Fintype.sum_prod_type]
    calc
      (∑ x : ZMod (Nt k), ∑ y : ZMod (Ns k),
          (circleRestriction Lt (Nt k) bt x * circleRestriction Ls (Ns k) bs y) *
            (circleRestriction Lt (Nt k) ct x * circleRestriction Ls (Ns k) cs y)) =
        ∑ x : ZMod (Nt k), ∑ y : ZMod (Ns k),
          (circleRestriction Lt (Nt k) bt x * circleRestriction Lt (Nt k) ct x) *
            (circleRestriction Ls (Ns k) bs y * circleRestriction Ls (Ns k) cs y) := by
              apply Finset.sum_congr rfl
              intro x hx
              apply Finset.sum_congr rfl
              intro y hy
              ring
      _ = (∑ x : ZMod (Nt k),
          circleRestriction Lt (Nt k) bt x * circleRestriction Lt (Nt k) ct x) *
          (∑ y : ZMod (Ns k),
          circleRestriction Ls (Ns k) bs y * circleRestriction Ls (Ns k) cs y) := by
            rw [Finset.sum_mul_sum]
  rw [hprod]
  have hdelta :
      (if mt = nt then (1 : ℝ) else 0) * (if ms = ns then 1 else 0) =
        (if m = n then 1 else 0) := by
    by_cases hmn : m = n
    · subst n
      simp [mt, ms, nt, ns]
    by_cases hmt : mt = nt
    · by_cases hms : ms = ns
      · have hmn' : m = n := by
          calc
            m = Nat.pair mt ms := by
              simpa [mt, ms] using (Nat.pair_unpair m).symm
            _ = Nat.pair nt ns := by rw [hmt, hms]
            _ = n := by
              simpa [nt, ns] using Nat.pair_unpair n
        exact (hmn hmn').elim
      · simp [hmt, hms, hmn]
    · simp [hmt, hmn]
  simpa only [hdelta] using htime'.mul hspace'

theorem asymTorusSiteEval_sq_tendsto
    (Lt Ls : ℝ) [Fact (0 < Lt)] [Fact (0 < Ls)]
    (Nt Ns : ℕ → ℕ) (a : ℕ → ℝ)
    (hNt : ∀ k, NeZero (Nt k)) (hNs : ∀ k, NeZero (Ns k))
    (ha : ∀ k, 0 < a k)
    (hLt : ∀ k, (Nt k : ℝ) * a k = Lt)
    (hLs : ∀ k, (Ns k : ℝ) * a k = Ls)
    (ha0 : Filter.Tendsto a atTop (nhds 0))
    (f : AsymTorusTestFunction Lt Ls) :
    Filter.Tendsto
      (fun k =>
        letI : NeZero (Nt k) := hNt k
        letI : NeZero (Ns k) := hNs k
        ∑ x : AsymLatticeSites (Nt k) (Ns k),
          (evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x f) ^ 2)
      atTop (nhds (l2InnerProduct f f)) := by
  have ha0' : Filter.Tendsto a atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within a ha0
      (Filter.Eventually.of_forall fun k => ha k)
  have hinv : Filter.Tendsto (fun k => (a k)⁻¹) atTop atTop :=
    tendsto_inv_nhdsGT_zero.comp ha0'
  have hNt_top : Filter.Tendsto Nt atTop atTop := by
    rw [← tendsto_natCast_atTop_iff (R := ℝ)]
    refine (hinv.const_mul_atTop (Fact.out : (0 : ℝ) < Lt)).congr fun k => ?_
    rw [← div_eq_mul_inv, div_eq_iff (ne_of_gt (ha k))]
    exact (hLt k).symm
  have hNs_top : Filter.Tendsto Ns atTop atTop := by
    rw [← tendsto_natCast_atTop_iff (R := ℝ)]
    refine (hinv.const_mul_atTop (Fact.out : (0 : ℝ) < Ls)).congr fun k => ?_
    rw [← div_eq_mul_inv, div_eq_iff (ne_of_gt (ha k))]
    exact (hLs k).symm
  let fN : ℕ → AsymTorusTestFunction Lt Ls := fun N =>
    ∑ m ∈ Finset.range N,
      DyninMityaginSpace.coeff m f • RapidDecaySeq.basisVec m
  have hfN : Filter.Tendsto fN atTop (nhds f) := by
    simpa [fN] using
      (DyninMityaginSpace.hasSum_basis (E := AsymTorusTestFunction Lt Ls) f).tendsto_sum_nat
  have hcoeff_fN : ∀ (N r : ℕ),
      DyninMityaginSpace.coeff r (fN N) =
        if r ∈ Finset.range N then DyninMityaginSpace.coeff r f else 0 := by
    classical
    intro N r
    dsimp [fN]
    have hcoeff_smul (x : ℕ) :
        DyninMityaginSpace.coeff r
              (DyninMityaginSpace.coeff x f • RapidDecaySeq.basisVec x) =
            DyninMityaginSpace.coeff x f *
              DyninMityaginSpace.coeff r (RapidDecaySeq.basisVec x) := by
      simpa only [smul_eq_mul] using
        (DyninMityaginSpace.coeff
          (E := AsymTorusTestFunction Lt Ls) r).map_smul
            (DyninMityaginSpace.coeff x f) (RapidDecaySeq.basisVec x)
    have hcoeff_basis (u v : ℕ) :
        DyninMityaginSpace.coeff u (RapidDecaySeq.basisVec v) =
          if u = v then 1 else 0 := by
      change (RapidDecaySeq.basisVec v).val u =
        if u = v then 1 else 0
      simp [RapidDecaySeq.basisVec]
    rw [map_sum]
    by_cases hr : r ∈ Finset.range N
    · rw [if_pos hr, Finset.sum_eq_single r]
      · calc
          DyninMityaginSpace.coeff r
                (DyninMityaginSpace.coeff r f • RapidDecaySeq.basisVec r) =
              DyninMityaginSpace.coeff r f *
                DyninMityaginSpace.coeff r (RapidDecaySeq.basisVec r) :=
            hcoeff_smul r
          _ = DyninMityaginSpace.coeff r f := by
            calc
              DyninMityaginSpace.coeff r f *
                    DyninMityaginSpace.coeff r (RapidDecaySeq.basisVec r) =
                  DyninMityaginSpace.coeff r f * (if r = r then 1 else 0) :=
                congrArg (fun y : ℝ => DyninMityaginSpace.coeff r f * y)
                  (hcoeff_basis r r)
              _ = DyninMityaginSpace.coeff r f := by simp
      · intro x hx hxr
        calc
          DyninMityaginSpace.coeff r
                (DyninMityaginSpace.coeff x f • RapidDecaySeq.basisVec x) =
              DyninMityaginSpace.coeff x f *
                DyninMityaginSpace.coeff r (RapidDecaySeq.basisVec x) :=
            hcoeff_smul x
          _ = 0 := by
            calc
              DyninMityaginSpace.coeff x f *
                    DyninMityaginSpace.coeff r (RapidDecaySeq.basisVec x) =
                  DyninMityaginSpace.coeff x f * (if r = x then 1 else 0) :=
                congrArg (fun y : ℝ => DyninMityaginSpace.coeff x f * y)
                  (hcoeff_basis r x)
              _ = 0 := by simp [Ne.symm hxr]
      · intro hrN
        exact (hrN hr).elim
    · rw [if_neg hr]
      apply Finset.sum_eq_zero
      intro x hx
      have hrx : r ≠ x := by
        intro hrx
        apply hr
        simpa [hrx] using hx
      calc
        DyninMityaginSpace.coeff r
              (DyninMityaginSpace.coeff x f • RapidDecaySeq.basisVec x) =
            DyninMityaginSpace.coeff x f *
              DyninMityaginSpace.coeff r (RapidDecaySeq.basisVec x) :=
          hcoeff_smul x
        _ = 0 := by
          calc
            DyninMityaginSpace.coeff x f *
                  DyninMityaginSpace.coeff r (RapidDecaySeq.basisVec x) =
                DyninMityaginSpace.coeff x f * (if r = x then 1 else 0) :=
              congrArg (fun y : ℝ => DyninMityaginSpace.coeff x f * y)
                (hcoeff_basis r x)
            _ = 0 := by simp [hrx]
  have hl2_fN : ∀ N,
      l2InnerProduct (fN N) (fN N) =
        ∑ m ∈ Finset.range N, (DyninMityaginSpace.coeff m f) ^ 2 := by
    intro N
    rw [l2InnerProduct]
    have houtside : ∀ r, r ∉ Finset.range N →
        DyninMityaginSpace.coeff r (fN N) *
            DyninMityaginSpace.coeff r (fN N) = 0 := by
      intro r hr
      simp [hcoeff_fN, hr]
    change (∑' r, DyninMityaginSpace.coeff r (fN N) *
      DyninMityaginSpace.coeff r (fN N)) = _
    rw [tsum_eq_sum (s := Finset.range N) houtside]
    apply Finset.sum_congr rfl
    intro r hr
    simp [hcoeff_fN, hr, pow_two]
  have hl2_tendsto : Filter.Tendsto
      (fun N => l2InnerProduct (fN N) (fN N)) atTop
      (nhds (l2InnerProduct f f)) := by
    have hs := (l2InnerProduct_summable f f).hasSum.tendsto_sum_nat
    have hfun : (fun N => l2InnerProduct (fN N) (fN N)) =
        fun N => ∑ m ∈ Finset.range N, (DyninMityaginSpace.coeff m f) ^ 2 :=
      funext hl2_fN
    rw [hfun]
    have hsq :
        (fun N => ∑ m ∈ Finset.range N, (DyninMityaginSpace.coeff m f) ^ 2) =
          fun N => ∑ m ∈ Finset.range N,
            DyninMityaginSpace.coeff m f * DyninMityaginSpace.coeff m f := by
      ext N
      refine Finset.sum_congr rfl fun m _ => pow_two _
    rw [hsq]
    -- `l2InnerProduct` is defeq to the bilinear tsum; do not unfold it
    -- (the expansion is a private name).
    change Filter.Tendsto
        (fun N => ∑ m ∈ Finset.range N,
          DyninMityaginSpace.coeff m f * DyninMityaginSpace.coeff m f)
        atTop
        (nhds
          (∑' r, DyninMityaginSpace.coeff r f *
            DyninMityaginSpace.coeff r f))
    exact hs
  let S : ℕ → AsymTorusTestFunction Lt Ls → ℝ := fun k h =>
    letI : NeZero (Nt k) := hNt k
    letI : NeZero (Ns k) := hNs k
    ∑ x : AsymLatticeSites (Nt k) (Ns k),
      (evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x h) ^ 2
  have hfixed : ∀ N, Filter.Tendsto (fun k => S k (fN N)) atTop
      (nhds (l2InnerProduct (fN N) (fN N))) := by
    intro N
    have hS_expand : ∀ k,
        S k (fN N) =
          ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
            DyninMityaginSpace.coeff m f * DyninMityaginSpace.coeff n f *
              (letI : NeZero (Nt k) := hNt k
               letI : NeZero (Ns k) := hNs k
               ∑ x : AsymLatticeSites (Nt k) (Ns k),
                 evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x
                   (RapidDecaySeq.basisVec m) *
                 evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x
                   (RapidDecaySeq.basisVec n)) := by
      intro k
      dsimp [S, fN]
      simp only [map_sum, pow_two]
      simp_rw [Finset.sum_mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n hn
      calc
        _ = ∑ x : AsymLatticeSites (Nt k) (Ns k),
            (DyninMityaginSpace.coeff m f *
              DyninMityaginSpace.coeff n f) *
              (evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x
                  (RapidDecaySeq.basisVec m) *
                evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x
                  (RapidDecaySeq.basisVec n)) := by
          apply Finset.sum_congr rfl
          intro x hx
          let ev : AsymTorusTestFunction Lt Ls →L[ℝ] ℝ :=
            evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x
          change ev (DyninMityaginSpace.coeff m f • RapidDecaySeq.basisVec m) *
              ev (DyninMityaginSpace.coeff n f • RapidDecaySeq.basisVec n) =
            DyninMityaginSpace.coeff m f * DyninMityaginSpace.coeff n f *
              (ev (RapidDecaySeq.basisVec m) * ev (RapidDecaySeq.basisVec n))
          calc
            ev (DyninMityaginSpace.coeff m f • RapidDecaySeq.basisVec m) *
                ev (DyninMityaginSpace.coeff n f • RapidDecaySeq.basisVec n) =
              (DyninMityaginSpace.coeff m f • ev (RapidDecaySeq.basisVec m)) *
                (DyninMityaginSpace.coeff n f • ev (RapidDecaySeq.basisVec n)) := by
              exact congrArg₂ (fun u v : ℝ => u * v)
                (ev.map_smul (DyninMityaginSpace.coeff m f)
                  (RapidDecaySeq.basisVec m))
                (ev.map_smul (DyninMityaginSpace.coeff n f)
                  (RapidDecaySeq.basisVec n))
            _ = _ := by
              simp only [smul_eq_mul]
              ring
        _ = _ := by
          rw [Finset.mul_sum]
    rw [show (fun k => S k (fN N)) =
        (fun k => ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
          DyninMityaginSpace.coeff m f * DyninMityaginSpace.coeff n f *
            (letI : NeZero (Nt k) := hNt k
             letI : NeZero (Ns k) := hNs k
             ∑ x : AsymLatticeSites (Nt k) (Ns k),
               evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x
                 (RapidDecaySeq.basisVec m) *
               evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x
                 (RapidDecaySeq.basisVec n))) by
          funext k; exact hS_expand k]
    have hsum : Filter.Tendsto
        (fun k => ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
          DyninMityaginSpace.coeff m f * DyninMityaginSpace.coeff n f *
            (letI : NeZero (Nt k) := hNt k
             letI : NeZero (Ns k) := hNs k
             ∑ x : AsymLatticeSites (Nt k) (Ns k),
               evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x
                 (RapidDecaySeq.basisVec m) *
               evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x
                 (RapidDecaySeq.basisVec n))) atTop
        (nhds (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
          DyninMityaginSpace.coeff m f * DyninMityaginSpace.coeff n f *
            (if m = n then 1 else 0))) := by
      apply tendsto_finset_sum
      intro m hm
      apply tendsto_finset_sum
      intro n hn
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        ((asym_basis_pair_tendsto Lt Ls Nt Ns a hNt hNs hNt_top hNs_top m n).const_mul
          (DyninMityaginSpace.coeff m f * DyninMityaginSpace.coeff n f))
    have hdiag :
        (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
        DyninMityaginSpace.coeff m f * DyninMityaginSpace.coeff n f *
          (if m = n then 1 else 0)) =
        l2InnerProduct (fN N) (fN N) := by
      rw [hl2_fN N]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.sum_eq_single m]
      · simp [pow_two]
      · intro b hb hbm
        simp [if_neg (Ne.symm hbm)]
      · intro hmN
        exact (hmN hm).elim
    rw [hdiag] at hsum
    exact hsum
  have hpdiff : Filter.Tendsto
      (fun N => RapidDecaySeq.rapidDecaySeminorm 0 (fN N - f)) atTop (nhds 0) := by
    have hdiff : Filter.Tendsto (fun N => fN N - f) atTop (nhds 0) := by
      have hconst : Filter.Tendsto (fun _ : ℕ => f) atTop (nhds f) :=
        tendsto_const_nhds
      simpa using hfN.sub hconst
    have hp :=
      (RapidDecaySeq.rapidDecay_withSeminorms.continuous_seminorm 0).continuousAt.tendsto.comp
        hdiff
    convert hp using 1
    exact congrArg nhds
      (map_zero (RapidDecaySeq.rapidDecaySeminorm 0)).symm
  obtain ⟨C₀t, hC₀t_pos, hC₀t_bound⟩ :=
    SmoothMap_Circle.sobolevSeminorm_fourierBasis_le (L := Lt) 0
  obtain ⟨C₀s, hC₀s_pos, hC₀s_bound⟩ :=
    SmoothMap_Circle.sobolevSeminorm_fourierBasis_le (L := Ls) 0
  let C₀ := Lt * Ls * C₀t ^ 2 * C₀s ^ 2
  have hC₀_pos : 0 < C₀ := by
    dsimp [C₀]
    exact mul_pos
      (mul_pos
        (mul_pos (Fact.out : (0 : ℝ) < Lt) (Fact.out : (0 : ℝ) < Ls))
        (sq_pos_of_pos hC₀t_pos))
      (sq_pos_of_pos hC₀s_pos)
  have hsample_bound : ∀ k (h : AsymTorusTestFunction Lt Ls),
      ‖WithLp.toLp 2 (fun x : AsymLatticeSites (Nt k) (Ns k) =>
          evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x h)‖ ≤
        Real.sqrt C₀ * RapidDecaySeq.rapidDecaySeminorm 0 h := by
    intro k h
    letI : NeZero (Nt k) := hNt k
    letI : NeZero (Ns k) := hNs k
    have hsquare := asymTorusSiteEval_norm_sq_le_seminorm Lt Ls
      C₀t hC₀t_pos (fun m => by
        simpa only [pow_zero, mul_one] using hC₀t_bound m)
      C₀s hC₀s_pos (fun m => by
        simpa only [pow_zero, mul_one] using hC₀s_bound m) h (Nt k) (Ns k)
    have hsquare' :
        ‖WithLp.toLp 2 (fun x : AsymLatticeSites (Nt k) (Ns k) =>
          evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x h)‖ ^ 2 ≤
          C₀ * (RapidDecaySeq.rapidDecaySeminorm 0 h) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simpa [C₀, Real.norm_eq_abs, sq_abs] using hsquare
    have hp : 0 ≤ RapidDecaySeq.rapidDecaySeminorm 0 h := apply_nonneg _ _
    calc
      ‖WithLp.toLp 2 (fun x : AsymLatticeSites (Nt k) (Ns k) =>
          evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x h)‖ ≤
          Real.sqrt (C₀ * (RapidDecaySeq.rapidDecaySeminorm 0 h) ^ 2) :=
        Real.le_sqrt_of_sq_le hsquare'
      _ = Real.sqrt C₀ * RapidDecaySeq.rapidDecaySeminorm 0 h := by
        rw [Real.sqrt_mul hC₀_pos.le, Real.sqrt_sq_eq_abs, abs_of_nonneg hp]
  rw [Metric.tendsto_atTop]
  intro ε hε
  let p : AsymTorusTestFunction Lt Ls → ℝ :=
    RapidDecaySeq.rapidDecaySeminorm 0
  let A : ℝ := Real.sqrt C₀
  let d : ℝ := p f
  have hden : 0 < 3 * A ^ 2 * (2 * d + 1) := by
    dsimp [A, d]
    have hd : 0 ≤ p f := apply_nonneg _ _
    positivity
  have htarget : ∀ᶠ N in atTop,
      |l2InnerProduct (fN N) (fN N) - l2InnerProduct f f| < ε / 3 := by
    have h := (Metric.tendsto_atTop.mp hl2_tendsto) (ε / 3) (by positivity)
    simpa [Real.dist_eq] using h
  have hsmall : ∀ᶠ N in atTop,
      p (fN N - f) < min 1 (ε / (3 * A ^ 2 * (2 * d + 1))) := by
    have hmin : 0 < min 1 (ε / (3 * A ^ 2 * (2 * d + 1))) := by
      rw [lt_min_iff]
      exact ⟨by norm_num, div_pos hε hden⟩
    have h := (Metric.tendsto_atTop.mp hpdiff)
      (min 1 (ε / (3 * A ^ 2 * (2 * d + 1)))) hmin
    simpa [Real.dist_eq, abs_of_nonneg (apply_nonneg _ _)] using h
  rcases eventually_atTop.1 (htarget.and hsmall) with ⟨N₀, hN₀⟩
  have hNtarget := hN₀ N₀ le_rfl |>.1
  have hNsmall := hN₀ N₀ le_rfl |>.2
  obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.mp (hfixed N₀)) (ε / 3) (by positivity)
  refine ⟨K, fun k hk => ?_⟩
  have hfixed_k := hK k hk
  rw [Real.dist_eq] at hfixed_k ⊢
  let vf : EuclideanSpace ℝ (AsymLatticeSites (Nt k) (Ns k)) :=
    WithLp.toLp 2 (fun x =>
      evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x f)
  let vn : EuclideanSpace ℝ (AsymLatticeSites (Nt k) (Ns k)) :=
    WithLp.toLp 2 (fun x =>
      evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x (fN N₀))
  let vd : EuclideanSpace ℝ (AsymLatticeSites (Nt k) (Ns k)) :=
    WithLp.toLp 2 (fun x =>
      evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x (f - fN N₀))
  have hvd : vd = vf - vn := by
    ext x
    simp [vd, vf, vn, map_sub]
  have hnorm_f := hsample_bound k f
  have hnorm_n := hsample_bound k (fN N₀)
  have hnorm_d := hsample_bound k (f - fN N₀)
  have hpfn : p (fN N₀) ≤ d + 1 := by
    have hdecomp : (fN N₀ - f) + f = fN N₀ := by abel
    have htriangle := (RapidDecaySeq.rapidDecaySeminorm 0).add_le'
      (fN N₀ - f) f
    have hdiff' := hNsmall.trans_le (min_le_left _ _)
    calc
      p (fN N₀) = p ((fN N₀ - f) + f) := by rw [hdecomp]
      _ ≤ p (fN N₀ - f) + p f := htriangle
      _ ≤ 1 + d := by
        have hdiff'' : p (fN N₀ - f) ≤ 1 := hdiff'.le
        dsimp [d]
        linarith
      _ = d + 1 := by ring
  have hnorm_sum : ‖vf‖ + ‖vn‖ ≤ A * (2 * d + 1) := by
    have h1 := hnorm_f
    have h2 := hnorm_n
    dsimp [A, p, d] at *
    have hpf : 0 ≤ RapidDecaySeq.rapidDecaySeminorm 0 f := apply_nonneg _ _
    have hpn : 0 ≤ RapidDecaySeq.rapidDecaySeminorm 0 (fN N₀) := apply_nonneg _ _
    have hA : 0 ≤ A := by
      dsimp [A]
      exact Real.sqrt_nonneg _
    nlinarith
  have hnorm_diff : ‖vf - vn‖ ≤ A * p (fN N₀ - f) := by
    rw [← hvd]
    have := hsample_bound k (f - fN N₀)
    have heq :
        RapidDecaySeq.rapidDecaySeminorm 0 (f - fN N₀) =
          RapidDecaySeq.rapidDecaySeminorm 0 (fN N₀ - f) := by
      rw [show f - fN N₀ = -(fN N₀ - f) by abel]
      exact map_neg_eq_map _ _
    rw [heq] at this
    exact this
  have hsqdiff :
      |S k f - S k (fN N₀)| ≤
        (‖vf‖ + ‖vn‖) * ‖vf - vn‖ := by
    dsimp [S]
    change
      |(∑ x, vf x ^ 2) - (∑ x, vn x ^ 2)| ≤
        (‖vf‖ + ‖vn‖) * ‖vf - vn‖
    rw [← EuclideanSpace.real_norm_sq_eq vf,
      ← EuclideanSpace.real_norm_sq_eq vn]
    rw [show ‖vf‖ ^ 2 - ‖vn‖ ^ 2 =
        (‖vf‖ - ‖vn‖) * (‖vf‖ + ‖vn‖) by ring, abs_mul]
    have hsum_nonneg : 0 ≤ ‖vf‖ + ‖vn‖ :=
      add_nonneg (norm_nonneg vf) (norm_nonneg vn)
    rw [abs_of_nonneg hsum_nonneg]
    calc
      |‖vf‖ - ‖vn‖| * (‖vf‖ + ‖vn‖) =
          (‖vf‖ + ‖vn‖) * |‖vf‖ - ‖vn‖| := mul_comm _ _
      _ ≤ (‖vf‖ + ‖vn‖) * ‖vf - vn‖ :=
        mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le vf vn) hsum_nonneg
  have hsqdiff' : |S k f - S k (fN N₀)| < ε / 3 := by
    calc
      |S k f - S k (fN N₀)| ≤
          (‖vf‖ + ‖vn‖) * ‖vf - vn‖ := hsqdiff
      _ ≤ A * (2 * d + 1) * (A * p (fN N₀ - f)) := by
        have hA : 0 ≤ A := by
          dsimp [A]
          exact Real.sqrt_nonneg _
        have hd : 0 ≤ d := by
          dsimp [d]
          exact apply_nonneg _ _
        have hsumfac : 0 ≤ A * (2 * d + 1) := by positivity
        calc
          (‖vf‖ + ‖vn‖) * ‖vf - vn‖ ≤
              A * (2 * d + 1) * ‖vf - vn‖ :=
            mul_le_mul_of_nonneg_right hnorm_sum (norm_nonneg _)
          _ ≤ A * (2 * d + 1) * (A * p (fN N₀ - f)) :=
            mul_le_mul_of_nonneg_left hnorm_diff hsumfac
      _ < ε / 3 := by
        have hsmall' := hNsmall.trans_le (min_le_right _ _)
        have heq : A * (2 * d + 1) * (A * p (fN N₀ - f)) =
            A ^ 2 * (2 * d + 1) * p (fN N₀ - f) := by ring
        rw [heq]
        have hcoef : 0 < A ^ 2 * (2 * d + 1) := by
          nlinarith [hden]
        have hA_pos : 0 < A := by
          dsimp [A]
          exact Real.sqrt_pos.2 hC₀_pos
        have hfac_pos : 0 < 2 * d + 1 := by
          have hd : 0 ≤ d := by
            dsimp [d, p]
            exact apply_nonneg _ _
          linarith
        have hmul := mul_lt_mul_of_pos_left hsmall' hcoef
        calc
          A ^ 2 * (2 * d + 1) * p (fN N₀ - f) <
              A ^ 2 * (2 * d + 1) *
                (ε / (3 * A ^ 2 * (2 * d + 1))) := hmul
          _ = ε / 3 := by
            field_simp [ne_of_gt hden, ne_of_gt hcoef,
              ne_of_gt hA_pos, ne_of_gt hfac_pos]
  calc
    |S k f - l2InnerProduct f f| ≤
        |S k f - S k (fN N₀)| +
          |S k (fN N₀) - l2InnerProduct (fN N₀) (fN N₀)| +
          |l2InnerProduct (fN N₀) (fN N₀) - l2InnerProduct f f| := by
      calc
        |S k f - l2InnerProduct f f| ≤
            |S k f - S k (fN N₀)| +
              |S k (fN N₀) - l2InnerProduct f f| := abs_sub_le _ _ _
        _ ≤ |S k f - S k (fN N₀)| +
              (|S k (fN N₀) - l2InnerProduct (fN N₀) (fN N₀)| +
                |l2InnerProduct (fN N₀) (fN N₀) - l2InnerProduct f f|) :=
          by
            have htri := abs_sub_le (S k (fN N₀))
              (l2InnerProduct (fN N₀) (fN N₀))
              (l2InnerProduct f f)
            exact add_le_add_right htri _
        _ = _ := by ring
    _ < ε / 3 + ε / 3 + ε / 3 := by
      gcongr
    _ = ε := by ring

/-- The normalized squared lattice pullback converges to the asymmetric-torus
`L²` coefficient norm along every fixed-physical-size UV sequence. -/
theorem asymTorusIso_raw_sampling_tendsto_of_siteEval
    (Lt Ls : ℝ) [Fact (0 < Lt)] [Fact (0 < Ls)]
    (Nt Ns : ℕ → ℕ) (a : ℕ → ℝ)
    (hNt : ∀ k, NeZero (Nt k)) (hNs : ∀ k, NeZero (Ns k))
    (ha : ∀ k, 0 < a k)
    (hLt_phys : ∀ k, (Nt k : ℝ) * a k = Lt)
    (hLs_phys : ∀ k, (Ns k : ℝ) * a k = Ls)
    (ha0 : Filter.Tendsto a Filter.atTop (nhds 0)) :
    ∀ f : CylinderTestFunction Ls,
      Filter.Tendsto
        (fun k =>
          letI : NeZero (Nt k) := hNt k
          letI : NeZero (Ns k) := hNs k
          (a k ^ 2 : ℝ)⁻¹ *
            ∑ x : AsymLatticeSites (Nt k) (Ns k),
              (asymLatticeTestFnIso Lt Ls (Nt k) (Ns k) (a k)
                (cylinderToTorusEmbed Lt Ls f) x) ^ 2)
        Filter.atTop
        (nhds (l2InnerProduct (cylinderToTorusEmbed Lt Ls f)
          (cylinderToTorusEmbed Lt Ls f))) := by
  intro f
  have hsite :=
    asymTorusSiteEval_sq_tendsto Lt Ls Nt Ns a hNt hNs ha
      hLt_phys hLs_phys ha0 (cylinderToTorusEmbed Lt Ls f)
  have hscale :
      (fun k =>
        letI : NeZero (Nt k) := hNt k
        letI : NeZero (Ns k) := hNs k
        (a k ^ 2 : ℝ)⁻¹ *
          ∑ x : AsymLatticeSites (Nt k) (Ns k),
            (asymLatticeTestFnIso Lt Ls (Nt k) (Ns k) (a k)
              (cylinderToTorusEmbed Lt Ls f) x) ^ 2) =
      (fun k =>
        letI : NeZero (Nt k) := hNt k
        letI : NeZero (Ns k) := hNs k
        ∑ x : AsymLatticeSites (Nt k) (Ns k),
          (evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x
            (cylinderToTorusEmbed Lt Ls f)) ^ 2) := by
    funext k
    letI : NeZero (Nt k) := hNt k
    letI : NeZero (Ns k) := hNs k
    exact asymLatticeTestFnIso_scaled_sq_sum_eq_evalAsymTorusAtSite_sq_sum
      Lt Ls (Nt k) (Ns k) (a k) (ha k)
        (cylinderToTorusEmbed Lt Ls f)
  rw [hscale]
  simpa using hsite

/-- A raw finite-grid sampling limit turns the sitewise massive variance estimate
into a cylinder exponential-moment bound after the UV weak limit.  The cutoff
estimate is supplied on the selected sequence; the physical mesh identities
and `a → 0` now discharge the sampling limit internally. -/
theorem asymTorusIso_measureHasCylinderExpMomentBound_of_raw_sampling
    (mass : ℝ) (hmass : 0 < mass)
    (K C : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (Nt Ns : ℕ → ℕ) (a : ℕ → ℝ)
    (hNt : ∀ k, NeZero (Nt k)) (hNs : ∀ k, NeZero (Ns k))
    (ha : ∀ k, 0 < a k)
    (hLt_phys : ∀ k, (Nt k : ℝ) * a k = Lt)
    (hLs_phys : ∀ k, (Ns k : ℝ) * a k = Ls)
    (ha0 : Filter.Tendsto a Filter.atTop (nhds 0))
    (ν : ℕ → Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    (hν_prob : ∀ k, IsProbabilityMeasure (ν k))
    (hμ_prob : IsProbabilityMeasure μ)
    (hbc : ∀ (g : Configuration (AsymTorusTestFunction Lt Ls) → ℝ),
      Continuous g → (∃ B, ∀ x, |g x| ≤ B) →
      Filter.Tendsto (fun k => ∫ ω, g ω ∂(ν k)) Filter.atTop
        (nhds (∫ ω, g ω ∂μ)))
    (hcutoff : ∀ k,
      letI : NeZero (Nt k) := hNt k
      letI : NeZero (Ns k) := hNs k
      ∀ F : AsymTorusTestFunction Lt Ls,
        Integrable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
          Real.exp (|ω F|)) (ν k) ∧
        ∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
          Real.exp (|ω F|) ∂(ν k) ≤
          K * Real.exp (C *
            ∫ ω : Configuration (AsymLatticeField (Nt k) (Ns k)),
              (ω (fun x => |asymLatticeTestFnIso Lt Ls (Nt k) (Ns k) (a k) F x|)) ^ 2
              ∂(latticeGaussianMeasureAsym (Nt k) (Ns k) (a k)
                mass (ha k) hmass)))
    (hLt1 : 1 ≤ Lt) :
    ∃ q : Seminorm ℝ (CylinderTestFunction Ls), Continuous q ∧
      MeasureHasCylinderExpMomentBound Ls K (C * mass⁻¹ ^ 2) q μ := by
  have hraw := asymTorusIso_raw_sampling_tendsto_of_siteEval
    Lt Ls Nt Ns a hNt hNs ha hLt_phys hLs_phys ha0
  obtain ⟨q, hq_cont, hq_bound⟩ :=
    GaussianField.embed_l2_uniform_bound (Ls := Ls)
  refine ⟨q, hq_cont, ?_⟩
  intro f
  let F : AsymTorusTestFunction Lt Ls := cylinderToTorusEmbed Lt Ls f
  let R : ℕ → ℝ := fun k =>
    letI : NeZero (Nt k) := hNt k
    letI : NeZero (Ns k) := hNs k
    (a k ^ 2 : ℝ)⁻¹ *
      ∑ x : AsymLatticeSites (Nt k) (Ns k),
        (asymLatticeTestFnIso Lt Ls (Nt k) (Ns k) (a k) F x) ^ 2
  have hR : Filter.Tendsto R Filter.atTop
      (nhds (l2InnerProduct F F)) := by
    simpa [R, F] using hraw f
  let D : ℝ := C * mass⁻¹ ^ 2
  let B : ℕ → ℝ := fun k => K * Real.exp (D * R k)
  let Binf : ℝ := K * Real.exp (D * l2InnerProduct F F)
  have hB : Filter.Tendsto B Filter.atTop (nhds Binf) := by
    dsimp [B, Binf]
    exact ((Real.continuous_exp.tendsto _).comp (hR.const_mul D)).const_mul K
  have h_unif : ∀ k,
      Integrable (fun ω : Configuration (CylinderTestFunction Ls) =>
        Real.exp (|ω f|)) (cylinderPullbackMeasure Lt Ls (ν k)) ∧
      ∫ ω : Configuration (CylinderTestFunction Ls),
        Real.exp (|ω f|) ∂(cylinderPullbackMeasure Lt Ls (ν k)) ≤ B k := by
    intro k
    letI : NeZero (Nt k) := hNt k
    letI : NeZero (Ns k) := hNs k
    letI : IsProbabilityMeasure (ν k) := hν_prob k
    obtain ⟨hT_int, hT_bound⟩ := hcutoff k F
    have hT_int' :
        Integrable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
          Real.exp (|ω (cylinderToTorusEmbed Lt Ls f)|)) (ν k) := by
      simpa [F] using hT_int
    have hT_bound' :
        ∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
            Real.exp (|ω (cylinderToTorusEmbed Lt Ls f)|) ∂(ν k) ≤
          K * Real.exp (C *
            ∫ ω : Configuration (AsymLatticeField (Nt k) (Ns k)),
              (ω (fun x => |asymLatticeTestFnIso Lt Ls (Nt k) (Ns k) (a k)
                (cylinderToTorusEmbed Lt Ls f) x|)) ^ 2
              ∂(latticeGaussianMeasureAsym (Nt k) (Ns k) (a k)
                mass (ha k) hmass)) := by
      simpa [F] using hT_bound
    obtain ⟨hCyl_int, hEq⟩ :=
      cylinderPullback_expMoment_eq Ls Lt (ν k) f hT_int'
    have hvar :
        (∫ ω : Configuration (AsymLatticeField (Nt k) (Ns k)),
          (ω (fun x => |asymLatticeTestFnIso Lt Ls (Nt k) (Ns k) (a k)
            (cylinderToTorusEmbed Lt Ls f) x|)) ^ 2
          ∂(latticeGaussianMeasureAsym (Nt k) (Ns k) (a k)
            mass (ha k) hmass)) ≤
        mass⁻¹ ^ 2 * R k := by
      calc
        _ ≤ (a k ^ 2 : ℝ)⁻¹ * mass⁻¹ ^ 2 *
            ∑ x : AsymLatticeSites (Nt k) (Ns k),
              (asymLatticeTestFnIso Lt Ls (Nt k) (Ns k) (a k)
                (cylinderToTorusEmbed Lt Ls f) x) ^ 2 :=
          asymFreeVariance_sitewiseAbs_le_mass_inv_sq
            (Nt k) (Ns k) (a k) mass (ha k) hmass
            (asymLatticeTestFnIso Lt Ls (Nt k) (Ns k) (a k)
              (cylinderToTorusEmbed Lt Ls f))
        _ = mass⁻¹ ^ 2 * R k := by
          dsimp [R, F]
          ring
    refine ⟨hCyl_int, hEq.le.trans ?_⟩
    calc
      ∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
          Real.exp (|ω (cylinderToTorusEmbed Lt Ls f)|) ∂(ν k) ≤
          K * Real.exp (C *
            ∫ ω : Configuration (AsymLatticeField (Nt k) (Ns k)),
              (ω (fun x => |asymLatticeTestFnIso Lt Ls (Nt k) (Ns k) (a k)
                (cylinderToTorusEmbed Lt Ls f) x|)) ^ 2
              ∂(latticeGaussianMeasureAsym (Nt k) (Ns k) (a k)
                mass (ha k) hmass)) := hT_bound'
      _ ≤ K * Real.exp (D * R k) := by
        apply mul_le_mul_of_nonneg_left _ hK
        apply Real.exp_le_exp.mpr
        calc
          C * _ ≤ C * (mass⁻¹ ^ 2 * R k) :=
            mul_le_mul_of_nonneg_left hvar hC
          _ = D * R k := by
            dsimp [D]
            ring
      _ = B k := by rfl
  obtain ⟨hint_cyl, hle_cyl⟩ :=
    cylinderPullbackMeasure_exponential_moment_of_tendsto_bc
      Lt Ls ν μ hν_prob hμ_prob hbc f B Binf hB h_unif
  have hL2 : l2InnerProduct F F ≤ q f ^ 2 := by
    simpa [F, Pphi2.cylinderToTorusEmbed,
      GaussianField.cylinderToTorusEmbed] using hq_bound Lt hLt1 f
  refine ⟨hint_cyl, ?_⟩
  calc
    ∫ ω : Configuration (CylinderTestFunction Ls),
        Real.exp (|ω f|) ∂(cylinderPullbackMeasure Lt Ls μ) ≤ Binf := hle_cyl
    _ ≤ K * Real.exp (D * q f ^ 2) := by
      have hD : 0 ≤ D := by
        dsimp [D]
        exact mul_nonneg hC (sq_nonneg mass⁻¹)
      apply mul_le_mul_of_nonneg_left _ hK
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hL2 hD)
    _ = K * Real.exp ((C * mass⁻¹ ^ 2) * q f ^ 2) := by
      simp [D]

/-- A sequence-level cylinder exponential-moment estimate passes through the
isotropic UV weak limit with the same constants and seminorm.

The cutoff premise is imposed only on the selected UV sequence.  This keeps
threshold and mesh hypotheses upstream, where that sequence is chosen. -/
theorem asymTorusIso_measureHasCylinderExpMomentBound_of_cutoff
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (K C : ℝ) (q : Seminorm ℝ (CylinderTestFunction Ls))
    (Nt Ns : ℕ → ℕ) (a : ℕ → ℝ)
    (hNt : ∀ k, NeZero (Nt k)) (hNs : ∀ k, NeZero (Ns k))
    (ha : ∀ k, 0 < a k)
    (hvolt : ∀ k, (Nt k : ℝ) * a k = Lt)
    (hvols : ∀ k, (Ns k : ℝ) * a k = Ls)
    (ha0 : Filter.Tendsto a Filter.atTop (nhds 0))
    (hcutoff : ∀ k,
      letI : NeZero (Nt k) := hNt k
      letI : NeZero (Ns k) := hNs k
      ∀ f : CylinderTestFunction Ls,
        Integrable (fun ω : Configuration (CylinderTestFunction Ls) =>
          Real.exp (|ω f|))
          (cylinderPullbackMeasure Lt Ls
            (asymTorusInteractingMeasureIso Lt Ls (Nt k) (Ns k) (a k)
              P mass (ha k) hmass)) ∧
        ∫ ω : Configuration (CylinderTestFunction Ls),
          Real.exp (|ω f|) ∂(cylinderPullbackMeasure Lt Ls
            (asymTorusInteractingMeasureIso Lt Ls (Nt k) (Ns k) (a k)
              P mass (ha k) hmass)) ≤
          K * Real.exp (C * q f ^ 2)) :
    ∃ μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)),
      IsProbabilityMeasure μ ∧
      MeasureHasCylinderExpMomentBound Ls K C q μ := by
  obtain ⟨μ, hμ_prob, φ, hφ_mono, hconv⟩ :=
    asymTorusIso_interacting_limit_exists Lt Ls P mass hmass
      Nt Ns a hNt hNs ha hvolt hvols ha0
  set ν : ℕ → Measure (Configuration (AsymTorusTestFunction Lt Ls)) := fun n =>
    haveI := hNt (φ n)
    haveI := hNs (φ n)
    asymTorusInteractingMeasureIso Lt Ls (Nt (φ n)) (Ns (φ n)) (a (φ n))
      P mass (ha (φ n)) hmass with hν_def
  have hν_prob : ∀ n, IsProbabilityMeasure (ν n) := fun n => by
    haveI := hNt (φ n)
    haveI := hNs (φ n)
    exact asymTorusInteractingMeasureIso_isProbability Lt Ls
      (Nt (φ n)) (Ns (φ n)) (a (φ n)) P mass (ha (φ n)) hmass
  have hbc : ∀ (g : Configuration (AsymTorusTestFunction Lt Ls) → ℝ),
      Continuous g → (∃ D, ∀ x, |g x| ≤ D) →
      Filter.Tendsto (fun n => ∫ ω, g ω ∂(ν n)) Filter.atTop
        (nhds (∫ ω, g ω ∂μ)) := by
    intro g hg hg_bound
    simpa [ν] using hconv g hg hg_bound
  refine ⟨μ, hμ_prob, ?_⟩
  intro f
  apply cylinderPullbackMeasure_exponential_moment_of_tendsto_bc
    Lt Ls ν μ hν_prob hμ_prob hbc f
    (fun _ => K * Real.exp (C * q f ^ 2))
    (K * Real.exp (C * q f ^ 2)) tendsto_const_nhds
  intro n
  haveI := hNt (φ n)
  haveI := hNs (φ n)
  simpa [ν] using hcutoff (φ n) f

/-- Convert the thresholded torus absolute-variance estimate into the direct
cylinder-seminorm estimate once the finite-grid variance has been bounded by
that seminorm.  This lemma contains only pushforward and monotonicity algebra;
the sampling estimate remains an explicit premise. -/
theorem asymTorusInteractingMeasureIso_cylinderExpMoment_of_absVarianceBound
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (ha : 0 < a)
    (K C D : ℝ) (hK : 0 ≤ K) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (q : Seminorm ℝ (CylinderTestFunction Ls))
    (f : CylinderTestFunction Ls)
    (hTorus :
      Integrable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
        Real.exp (|ω (cylinderToTorusEmbed Lt Ls f)|))
        (asymTorusInteractingMeasureIso Lt Ls Nt Ns a P mass ha hmass) ∧
      ∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
        Real.exp (|ω (cylinderToTorusEmbed Lt Ls f)|)
          ∂(asymTorusInteractingMeasureIso Lt Ls Nt Ns a P mass ha hmass) ≤
        K * Real.exp (C *
          ∫ ω : Configuration (AsymLatticeField Nt Ns),
            (ω (fun x => |asymLatticeTestFnIso Lt Ls Nt Ns a
              (cylinderToTorusEmbed Lt Ls f) x|)) ^ 2
            ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass)))
    (hVariance :
      ∫ ω : Configuration (AsymLatticeField Nt Ns),
          (ω (fun x => |asymLatticeTestFnIso Lt Ls Nt Ns a
            (cylinderToTorusEmbed Lt Ls f) x|)) ^ 2
          ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) ≤
        D * q f ^ 2) :
    Integrable (fun ω : Configuration (CylinderTestFunction Ls) =>
      Real.exp (|ω f|))
      (cylinderPullbackMeasure Lt Ls
        (asymTorusInteractingMeasureIso Lt Ls Nt Ns a P mass ha hmass)) ∧
    ∫ ω : Configuration (CylinderTestFunction Ls),
      Real.exp (|ω f|) ∂(cylinderPullbackMeasure Lt Ls
        (asymTorusInteractingMeasureIso Lt Ls Nt Ns a P mass ha hmass)) ≤
      K * Real.exp ((C * D) * q f ^ 2) := by
  let μ := asymTorusInteractingMeasureIso Lt Ls Nt Ns a P mass ha hmass
  letI : IsProbabilityMeasure μ :=
    asymTorusInteractingMeasureIso_isProbability Lt Ls Nt Ns a P mass ha hmass
  obtain ⟨hint_cyl, heq⟩ :=
    cylinderPullback_expMoment_eq Ls Lt μ f hTorus.1
  refine ⟨hint_cyl, heq.le.trans ?_⟩
  calc
    ∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
        Real.exp (|ω (cylinderToTorusEmbed Lt Ls f)|) ∂μ ≤
        K * Real.exp (C *
          ∫ ω : Configuration (AsymLatticeField Nt Ns),
            (ω (fun x => |asymLatticeTestFnIso Lt Ls Nt Ns a
              (cylinderToTorusEmbed Lt Ls f) x|)) ^ 2
            ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass)) := hTorus.2
    _ ≤ K * Real.exp (C * (D * q f ^ 2)) := by
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hVariance hC)) hK
    _ = K * Real.exp ((C * D) * q f ^ 2) := by ring


end Pphi2

end
