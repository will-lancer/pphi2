/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Pphi2.ClusterExpansion.ContinuousConfig
import Pphi2.WickOrdering.WickPolynomial

/-!
# Continuous-spin Wick interactions

The local block interaction is
`a² ∑ x ∈ B, wickPolynomial P c (φ x)`.  Its Boltzmann factor is controlled
by a pointwise lower bound.  No supremum norm on an unbounded spin space is
used.
-/

open MeasureTheory

namespace Pphi2.ClusterExpansion

variable {Site : Type*}

/-- Formal polynomial whose evaluation is the Wick monomial. -/
noncomputable def wickMonomialFormal : ℕ → ℝ → Polynomial ℝ
  | 0, _ => 1
  | 1, _ => Polynomial.X
  | n + 2, c =>
      Polynomial.X * wickMonomialFormal (n + 1) c -
        Polynomial.C ((n + 1 : ℝ) * c) * wickMonomialFormal n c

theorem wickMonomialFormal_eval : ∀ (n : ℕ) (c x : ℝ),
    (wickMonomialFormal n c).eval x = wickMonomial n c x
  | 0, _, x => by simp [wickMonomialFormal, wickMonomial]
  | 1, _, x => by simp [wickMonomialFormal, wickMonomial]
  | n + 2, c, x => by
      simp only [wickMonomialFormal, wickMonomial_succ_succ,
        Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_mul,
        Polynomial.eval_sub, wickMonomialFormal_eval (n + 1) c x,
        wickMonomialFormal_eval n c x]

/-- Formal polynomial representing the Wick-ordered interaction. -/
noncomputable def wickPolynomialFormal (P : InteractionPolynomial) (c : ℝ) :
    Polynomial ℝ :=
  Polynomial.C (1 / P.n : ℝ) * wickMonomialFormal P.n c +
    ∑ m : Fin P.n, Polynomial.C (P.coeff m) *
      wickMonomialFormal (m : ℕ) c

theorem wickPolynomialFormal_eval
    (P : InteractionPolynomial) (c x : ℝ) :
    (wickPolynomialFormal P c).eval x = wickPolynomial P c x := by
  simp only [wickPolynomialFormal, wickPolynomial, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_finset_sum,
    wickMonomialFormal_eval]

/-- The single-site factor `exp (-a² :P(x):_c)`. -/
noncomputable def singleSiteBoltzmannWeight
    (P : InteractionPolynomial) (a c x : ℝ) : ℝ :=
  Real.exp (-(a ^ 2 * wickPolynomial P c x))

theorem singleSiteBoltzmannWeight_pos
    (P : InteractionPolynomial) (a c x : ℝ) :
    0 < singleSiteBoltzmannWeight P a c x :=
  Real.exp_pos _

theorem singleSiteBoltzmannWeight_continuous
    (P : InteractionPolynomial) (a c : ℝ) :
    Continuous (singleSiteBoltzmannWeight P a c) := by
  have hwick : Continuous (fun x : ℝ => wickPolynomial P c x) :=
    (wickPolynomial_continuous₂ P).comp
      (continuous_const.prodMk continuous_id)
  exact Real.continuous_exp.comp
    ((continuous_const.mul hwick).neg)

/-- Joint continuity in the spacing, Wick constant, and spin. -/
theorem singleSiteBoltzmannWeight_continuous₃
    (P : InteractionPolynomial) :
    Continuous (fun q : (ℝ × ℝ) × ℝ =>
      singleSiteBoltzmannWeight P q.1.1 q.1.2 q.2) := by
  have ha : Continuous (fun q : (ℝ × ℝ) × ℝ => q.1.1) :=
    continuous_fst.comp continuous_fst
  have hc : Continuous (fun q : (ℝ × ℝ) × ℝ => q.1.2) :=
    continuous_snd.comp continuous_fst
  have hx : Continuous (fun q : (ℝ × ℝ) × ℝ => q.2) :=
    continuous_snd
  have hwick : Continuous (fun q : (ℝ × ℝ) × ℝ =>
      wickPolynomial P q.1.2 q.2) :=
    (wickPolynomial_continuous₂ P).comp (hc.prodMk hx)
  exact Real.continuous_exp.comp (((ha.pow 2).mul hwick).neg)

theorem singleSiteBoltzmannWeight_measurable
    (P : InteractionPolynomial) (a c : ℝ) :
    Measurable (singleSiteBoltzmannWeight P a c) :=
  (singleSiteBoltzmannWeight_continuous P a c).measurable

/-- The interaction carried by a finite block of sites. -/
noncomputable def blockInteraction (P : InteractionPolynomial) (a c : ℝ)
    (B : Finset Site) (φ : ContinuousConfig Site) : ℝ :=
  a ^ 2 * ∑ x ∈ B, wickPolynomial P c (φ x)

theorem blockInteraction_continuous (P : InteractionPolynomial) (a c : ℝ)
    (B : Finset Site) :
    Continuous (blockInteraction P a c B) := by
  unfold blockInteraction
  apply Continuous.const_mul
  apply continuous_finset_sum
  intro x _
  exact (wickPolynomial_continuous₂ P).comp
    (continuous_const.prodMk (continuousConfig_eval_continuous x))

/-- Joint continuity of the finite-block interaction in the spacing, Wick
constant, and unbounded configuration. -/
theorem blockInteraction_continuous₃ (P : InteractionPolynomial)
    (B : Finset Site) :
    Continuous (fun q : (ℝ × ℝ) × ContinuousConfig Site =>
      blockInteraction P q.1.1 q.1.2 B q.2) := by
  have ha : Continuous
      (fun q : (ℝ × ℝ) × ContinuousConfig Site => q.1.1) :=
    continuous_fst.comp continuous_fst
  have hc : Continuous
      (fun q : (ℝ × ℝ) × ContinuousConfig Site => q.1.2) :=
    continuous_snd.comp continuous_fst
  have hsum : Continuous
      (fun q : (ℝ × ℝ) × ContinuousConfig Site =>
        ∑ x ∈ B, wickPolynomial P q.1.2 (q.2 x)) := by
    apply continuous_finset_sum
    intro x _
    exact (wickPolynomial_continuous₂ P).comp
      (hc.prodMk ((continuousConfig_eval_continuous x).comp continuous_snd))
  exact (ha.pow 2).mul hsum

theorem blockInteraction_measurable (P : InteractionPolynomial) (a c : ℝ)
    (B : Finset Site) :
    Measurable (blockInteraction P a c B) := by
  unfold blockInteraction
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro x _
  exact (wickPolynomial_continuous₂ P).measurable.comp
    (measurable_const.prodMk (measurable_pi_apply x))

/-- Joint measurability follows from coordinate measurability in the product
sigma-algebra; it does not identify that sigma-algebra with the Borel space of
an infinite product. -/
theorem blockInteraction_measurable₃ (P : InteractionPolynomial)
    (B : Finset Site) :
    Measurable (fun q : (ℝ × ℝ) × ContinuousConfig Site =>
      blockInteraction P q.1.1 q.1.2 B q.2) := by
  have ha : Measurable
      (fun q : (ℝ × ℝ) × ContinuousConfig Site => q.1.1) :=
    measurable_fst.comp measurable_fst
  have hc : Measurable
      (fun q : (ℝ × ℝ) × ContinuousConfig Site => q.1.2) :=
    measurable_snd.comp measurable_fst
  have hsum : Measurable
      (fun q : (ℝ × ℝ) × ContinuousConfig Site =>
        ∑ x ∈ B, wickPolynomial P q.1.2 (q.2 x)) := by
    apply Finset.measurable_sum
    intro x _
    exact (wickPolynomial_continuous₂ P).measurable.comp
      (hc.prodMk ((measurable_pi_apply x).comp measurable_snd))
  exact (ha.pow_const 2).mul hsum

/-- Every finite block interaction has a pointwise lower bound. -/
theorem blockInteraction_bounded_below
    (P : InteractionPolynomial) (a c : ℝ) (B : Finset Site) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ φ : ContinuousConfig Site, -K ≤ blockInteraction P a c B φ := by
  obtain ⟨A, hA, hwick⟩ := wickPolynomial_bounded_below P c
  refine ⟨a ^ 2 * B.card * A, by positivity, fun φ => ?_⟩
  have ha : 0 ≤ a ^ 2 := sq_nonneg a
  calc
    -(a ^ 2 * B.card * A)
        = a ^ 2 * ∑ x ∈ B, (-A) := by
            simp [Finset.sum_const]
            ring
    _ ≤ a ^ 2 * ∑ x ∈ B, wickPolynomial P c (φ x) := by
      refine mul_le_mul_of_nonneg_left ?_ ha
      exact Finset.sum_le_sum fun x _ => hwick (φ x)
    _ = blockInteraction P a c B φ := rfl

/-- The block Boltzmann factor. -/
noncomputable def blockBoltzmannWeight (P : InteractionPolynomial) (a c : ℝ)
    (B : Finset Site) (φ : ContinuousConfig Site) : ℝ :=
  Real.exp (-blockInteraction P a c B φ)

theorem blockBoltzmannWeight_pos (P : InteractionPolynomial) (a c : ℝ)
    (B : Finset Site) (φ : ContinuousConfig Site) :
    0 < blockBoltzmannWeight P a c B φ :=
  Real.exp_pos _

theorem blockBoltzmannWeight_measurable
    (P : InteractionPolynomial) (a c : ℝ) (B : Finset Site) :
    Measurable (blockBoltzmannWeight P a c B) :=
  (blockInteraction_measurable P a c B).neg.exp

theorem blockBoltzmannWeight_continuous₃ (P : InteractionPolynomial)
    (B : Finset Site) :
    Continuous (fun q : (ℝ × ℝ) × ContinuousConfig Site =>
      blockBoltzmannWeight P q.1.1 q.1.2 B q.2) :=
  Real.continuous_exp.comp (blockInteraction_continuous₃ P B).neg

theorem blockBoltzmannWeight_measurable₃ (P : InteractionPolynomial)
    (B : Finset Site) :
    Measurable (fun q : (ℝ × ℝ) × ContinuousConfig Site =>
      blockBoltzmannWeight P q.1.1 q.1.2 B q.2) :=
  (blockInteraction_measurable₃ P B).neg.exp

/-- A finite-block Boltzmann factor is integrable against every probability
measure on the product Borel configuration space. -/
theorem blockBoltzmannWeight_integrable
    (μ : Measure (ContinuousConfig Site)) [IsProbabilityMeasure μ]
    (P : InteractionPolynomial) (a c : ℝ) (B : Finset Site) :
    Integrable (blockBoltzmannWeight P a c B) μ := by
  obtain ⟨K, _, hK⟩ := blockInteraction_bounded_below P a c B
  apply Integrable.of_bound (C := Real.exp K)
  · exact (blockBoltzmannWeight_measurable P a c B).aestronglyMeasurable
  · filter_upwards [] with φ
    rw [Real.norm_eq_abs, abs_of_pos (blockBoltzmannWeight_pos P a c B φ)]
    exact Real.exp_le_exp_of_le (by
      have := hK φ
      linarith)

end Pphi2.ClusterExpansion
