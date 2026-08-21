/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# DDJ source normalization on the heterogeneous asymmetric lattice

This file records the normalization needed when a torus test function is
viewed as a finite-lattice source.  The lattice pullback contains the GJ
factor `a`; the source entering the physical `a²` pairing is therefore
`(a²)⁻¹ • g`.  The definitions here are bookkeeping interfaces for a future
finite source estimate.  They do not assert that such an estimate holds.
This is not Dimock–Dang–Jäkel (DDJ) 5.3/6.1.
-/

import Mathlib.Analysis.MeanInequalities
import Pphi2.AsymTorus.AsymTorusEmbeddingIso

noncomputable section

open GaussianField MeasureTheory

namespace Pphi2

/-! ## Physical source normalization -/

/-- The unweighted physical source associated to a GJ-normalized lattice field.

The lattice pairing is `a² * ∑ x, φ x * asymRawSource a g x`.  Since
`asymLatticeTestFnIso ... a f` already includes one factor of `a`, this source
is `a⁻¹` times the bare torus site evaluation under the physical hypotheses.
-/
def asymRawSource {Nt Ns : ℕ} [NeZero Nt] [NeZero Ns]
    (a : ℝ) (g : AsymLatticeField Nt Ns) : AsymLatticeField Nt Ns :=
  (a ^ 2 : ℝ)⁻¹ • g

/-- The cell-area-weighted `p`-power of a finite lattice field. -/
def asymWeightedLpPow {Nt Ns : ℕ} [NeZero Nt] [NeZero Ns]
    (p a : ℝ) (h : AsymLatticeField Nt Ns) : ℝ :=
  a ^ 2 * ∑ x : AsymLatticeSites Nt Ns, Real.rpow |h x| p

/-- A finite weighted interpolation estimate.  The weight is the cell area
`a²`; the hypothesis at exponent one is the corresponding weighted `L¹`
bound.  This is the elementary bridge used when a pointwise source estimate
and a weighted decay estimate are available separately. -/
theorem asymWeightedLpPow_le_of_sup_of_weightedL1
    {Nt Ns : ℕ} [NeZero Nt] [NeZero Ns]
    (p a M L : ℝ) (h : AsymLatticeField Nt Ns)
    (hp : 1 ≤ p) (hM : 0 ≤ M)
    (hsup : ∀ x : AsymLatticeSites Nt Ns, |h x| ≤ M)
    (hL : asymWeightedLpPow 1 a h ≤ L) :
    asymWeightedLpPow p a h ≤ Real.rpow M (p - 1) * L := by
  have hp_sub : 0 ≤ p - 1 := sub_nonneg.mpr hp
  have hpoint : ∀ x : AsymLatticeSites Nt Ns,
      Real.rpow |h x| p ≤ Real.rpow M (p - 1) * |h x| := by
    intro x
    calc
      Real.rpow |h x| p =
          Real.rpow |h x| (p - 1) * Real.rpow |h x| 1 := by
        simpa using
          (Real.rpow_add' (abs_nonneg (h x))
            (by linarith : (p - 1) + 1 ≠ 0))
      _ = Real.rpow |h x| (p - 1) * |h x| := by
        change |h x| ^ (p - 1) * |h x| ^ (1 : ℝ) =
          |h x| ^ (p - 1) * |h x|
        rw [Real.rpow_one]
      _ ≤ Real.rpow M (p - 1) * |h x| := by
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (abs_nonneg _) (hsup x) hp_sub)
          (abs_nonneg _)
  have hsum :
      ∑ x : AsymLatticeSites Nt Ns, Real.rpow |h x| p ≤
        ∑ x : AsymLatticeSites Nt Ns,
          Real.rpow M (p - 1) * |h x| :=
    Finset.sum_le_sum fun x _ => hpoint x
  have ha2 : 0 ≤ a ^ 2 := sq_nonneg a
  calc
    asymWeightedLpPow p a h =
        a ^ 2 * ∑ x : AsymLatticeSites Nt Ns, Real.rpow |h x| p := rfl
    _ ≤ a ^ 2 * ∑ x : AsymLatticeSites Nt Ns,
        Real.rpow M (p - 1) * |h x| :=
      mul_le_mul_of_nonneg_left hsum ha2
    _ = Real.rpow M (p - 1) * asymWeightedLpPow 1 a h := by
      simp only [asymWeightedLpPow]
      have hrpow_one : ∀ z : ℝ, Real.rpow z (1 : ℝ) = z := by
        intro z
        exact Real.rpow_one z
      simp_rw [hrpow_one]
      calc
        a ^ 2 * ∑ x : AsymLatticeSites Nt Ns,
              Real.rpow M (p - 1) * |h x| =
            ∑ x : AsymLatticeSites Nt Ns,
              a ^ 2 * (Real.rpow M (p - 1) * |h x|) := by
          rw [Finset.mul_sum]
        _ = ∑ x : AsymLatticeSites Nt Ns,
              (a ^ 2 * |h x|) * Real.rpow M (p - 1) := by
          apply Finset.sum_congr rfl
          intro x hx
          ring
        _ = Real.rpow M (p - 1) *
              (a ^ 2 * ∑ x : AsymLatticeSites Nt Ns, |h x|) := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro x hx
          ring
    _ ≤ Real.rpow M (p - 1) * L :=
      mul_le_mul_of_nonneg_left hL (Real.rpow_nonneg hM _)

/-! ## The finite weighted Hölder bridge -/

/-- Weighted finite-dimensional Hölder in the normalization used by the lattice source.

The two factors are scaled by `a ^ (2 / p)` and `a ^ (2 / q)`.  Consequently the
`p`- and `q`-power sums are the cell-area-weighted sums, while their product is the
physical pairing `a² ∑ u v`.  Keeping this elementary bridge separate makes the
source-control theorem below independent of the interaction polynomial. -/
theorem asymWeightedPairing_pow_le
    {α : Type*} [Fintype α]
    (n : ℕ) (hn : 1 < n)
    (a : ℝ) (ha : 0 < a)
    (u v : α → ℝ) :
    |a ^ 2 * ∑ x : α, u x * v x| ^ n ≤
      (a ^ 2 * ∑ x : α,
        Real.rpow |u x| ((n : ℝ) / ((n : ℝ) - 1))) ^ (n - 1) *
      (a ^ 2 * ∑ x : α, |v x| ^ n) := by
  let p : ℝ := (n : ℝ) / ((n : ℝ) - 1)
  let r : ℝ := 2 / p
  let s : ℝ := 2 / (n : ℝ)
  let F : α → ℝ := fun x => a ^ r * |u x|
  let G : α → ℝ := fun x => a ^ s * |v x|
  have hn_real : 1 < (n : ℝ) := by exact_mod_cast hn
  have hn_pos : 0 < (n : ℝ) := by linarith
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have hn_sub_ne : (n : ℝ) - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hn_real)
  have hp_pos : 0 < p := by
    dsimp [p]
    positivity
  have hpq : p.HolderConjugate (n : ℝ) := by
    simpa [p, Real.conjExponent] using
      (Real.HolderConjugate.conjExponent hn_real).symm
  have hrp : r * p = 2 := by
    dsimp [r]
    field_simp [hp_pos.ne']
  have hsn : s * (n : ℝ) = 2 := by
    dsimp [s]
    field_simp [hn_pos.ne']
  have hrs : r + s = 2 := by
    dsimp [r, s, p]
    field_simp [hn_ne, hn_sub_ne]
    ring
  have hF_nonneg : ∀ x, 0 ≤ F x := by
    intro x
    exact mul_nonneg (Real.rpow_nonneg ha.le _) (abs_nonneg _)
  have hG_nonneg : ∀ x, 0 ≤ G x := by
    intro x
    exact mul_nonneg (Real.rpow_nonneg ha.le _) (abs_nonneg _)
  have hF_pow :
      ∑ x : α, F x ^ p =
        a ^ 2 * ∑ x : α, Real.rpow |u x| p := by
    calc
      ∑ x : α, F x ^ p =
          ∑ x : α, (a ^ r) ^ p * Real.rpow |u x| p := by
        apply Finset.sum_congr rfl
        intro x hx
        dsimp [F]
        rw [Real.mul_rpow (Real.rpow_nonneg ha.le _) (abs_nonneg _)]
      _ = ∑ x : α, a ^ (r * p) * Real.rpow |u x| p := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [← Real.rpow_mul ha.le]
      _ = ∑ x : α, a ^ (2 : ℝ) * Real.rpow |u x| p := by rw [hrp]
      _ = a ^ 2 * ∑ x : α, Real.rpow |u x| p := by
        simp only [Real.rpow_two]
        rw [Finset.mul_sum]
  have hG_pow :
      ∑ x : α, G x ^ (n : ℝ) =
        a ^ 2 * ∑ x : α, |v x| ^ n := by
    calc
      ∑ x : α, G x ^ (n : ℝ) =
          ∑ x : α, (a ^ s) ^ (n : ℝ) * Real.rpow |v x| (n : ℝ) := by
        apply Finset.sum_congr rfl
        intro x hx
        dsimp [G]
        rw [Real.mul_rpow (Real.rpow_nonneg ha.le _) (abs_nonneg _)]
      _ = ∑ x : α, a ^ (s * (n : ℝ)) * Real.rpow |v x| (n : ℝ) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [← Real.rpow_mul ha.le]
      _ = ∑ x : α, a ^ (2 : ℝ) * Real.rpow |v x| (n : ℝ) := by rw [hsn]
      _ = a ^ 2 * ∑ x : α, |v x| ^ n := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        change a ^ 2 * (|v x| ^ (n : ℝ)) = a ^ 2 * |v x| ^ n
        simpa only [Real.rpow_two, Real.rpow_natCast]
  have hpair :
      |a ^ 2 * ∑ x : α, u x * v x| ≤ ∑ x : α, F x * G x := by
    calc
      |a ^ 2 * ∑ x : α, u x * v x| =
          a ^ 2 * |∑ x : α, u x * v x| := by
            rw [abs_mul, abs_of_nonneg (sq_nonneg a)]
      _ ≤ a ^ 2 * ∑ x : α, |u x * v x| :=
        mul_le_mul_of_nonneg_left
          (Finset.abs_sum_le_sum_abs (fun x : α => u x * v x) Finset.univ)
          (sq_nonneg a)
      _ = ∑ x : α, F x * G x := by
        calc
          a ^ 2 * ∑ x : α, |u x * v x| =
              ∑ x : α, a ^ 2 * (|u x| * |v x|) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro x hx
                rw [abs_mul]
          _ = ∑ x : α, F x * G x := by
            apply Finset.sum_congr rfl
            intro x hx
            dsimp [F, G]
            symm
            calc
              (a ^ r * |u x|) * (a ^ s * |v x|) =
                  (a ^ r * a ^ s) * (|u x| * |v x|) := by ring
              _ = a ^ (r + s) * (|u x| * |v x|) := by
                rw [← Real.rpow_add ha]
              _ = a ^ (2 : ℝ) * (|u x| * |v x|) := by rw [hrs]
              _ = a ^ 2 * (|u x| * |v x|) := by rw [Real.rpow_two]
  have hholder :
      (∑ x : α, F x * G x) ≤
        (∑ x : α, F x ^ p) ^ (1 / p) *
          (∑ x : α, G x ^ (n : ℝ)) ^ (1 / (n : ℝ)) := by
    apply Real.inner_le_Lp_mul_Lq_of_nonneg (s := Finset.univ) hpq
    · intro x hx
      exact hF_nonneg x
    · intro x hx
      exact hG_nonneg x
  have hpow := pow_le_pow_left₀ (abs_nonneg _) (hpair.trans hholder) n
  rw [hF_pow, hG_pow] at hpow
  have hA_nonneg : 0 ≤ a ^ 2 * ∑ x : α, Real.rpow |u x| p := by
    exact mul_nonneg (sq_nonneg a)
      (Finset.sum_nonneg fun x _ => Real.rpow_nonneg (abs_nonneg _) _)
  have hB_nonneg : 0 ≤ a ^ 2 * ∑ x : α, |v x| ^ n := by
    exact mul_nonneg (sq_nonneg a)
      (Finset.sum_nonneg fun x _ => pow_nonneg (abs_nonneg _) _)
  have hnorm_pow :
      ((a ^ 2 * ∑ x : α, Real.rpow |u x| p) ^ (1 / p) *
          (a ^ 2 * ∑ x : α, |v x| ^ n) ^ (1 / (n : ℝ))) ^ n =
        (a ^ 2 * ∑ x : α, Real.rpow |u x| p) ^ (n - 1) *
          (a ^ 2 * ∑ x : α, |v x| ^ n) := by
    rw [mul_pow]
    conv_lhs =>
      arg 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul hA_nonneg]
    conv_lhs =>
      arg 2
      rw [← Real.rpow_natCast, ← Real.rpow_mul hB_nonneg]
    have hp_exp : (1 / p) * (n : ℝ) = (n : ℝ) - 1 := by
      dsimp [p]
      field_simp [hn_ne, hn_sub_ne]
    have hn_exp : (1 / (n : ℝ)) * (n : ℝ) = 1 := by
      field_simp [hn_pos.ne']
    rw [hp_exp, hn_exp, Real.rpow_one]
    have hcast : (n : ℝ) - 1 = ((n - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]
      norm_num
    rw [hcast, Real.rpow_natCast]
  exact hpow.trans_eq hnorm_pow

/-- Applying the physical source normalization to a torus pullback removes
one, but not both, of the factors supplied by the GJ site map. -/
theorem asymRawSource_asymLatticeTestFnIso_apply
    (Lt Ls : ℝ) [Fact (0 < Lt)] [Fact (0 < Ls)]
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a : ℝ) (ha : 0 < a)
    (f : AsymTorusTestFunction Lt Ls)
    (x : AsymLatticeSites Nt Ns) :
    asymRawSource a (asymLatticeTestFnIso Lt Ls Nt Ns a f) x =
      a⁻¹ * evalAsymTorusAtSite Lt Ls Nt Ns x f := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha0
  simp only [asymRawSource, Pi.smul_apply, smul_eq_mul,
    asymLatticeTestFnIso, evalAsymTorusAtSiteGJ_apply]
  field_simp [ha0, ha2] <;> ring

/-- The finite lattice pairing of a configuration with a GJ pullback can be
written using the physical cell-area pairing and `asymRawSource`. -/
theorem asymRawSource_pairing_eq
    (Lt Ls : ℝ) [Fact (0 < Lt)] [Fact (0 < Ls)]
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a : ℝ) (ha : 0 < a)
    (f : AsymTorusTestFunction Lt Ls)
    (ω : Configuration (AsymLatticeField Nt Ns)) :
    ω (asymLatticeTestFnIso Lt Ls Nt Ns a f) =
      a ^ 2 * ∑ x : AsymLatticeSites Nt Ns,
        (ω (asymLatticeDelta Nt Ns x)) *
          asymRawSource a (asymLatticeTestFnIso Lt Ls Nt Ns a f) x := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha0
  calc
    ω (asymLatticeTestFnIso Lt Ls Nt Ns a f) =
        ∑ x : AsymLatticeSites Nt Ns,
          (asymLatticeTestFnIso Lt Ls Nt Ns a f) x *
            ω (asymLatticeDelta Nt Ns x) := by
      have hexpand := congrArg ω
        (asymLatticeTestFnIso_expand Lt Ls Nt Ns a f)
      rw [map_sum] at hexpand
      simpa only [map_smul, smul_eq_mul] using hexpand
    _ = ∑ x : AsymLatticeSites Nt Ns,
        a ^ 2 * ((ω (asymLatticeDelta Nt Ns x)) *
          (asymRawSource a
            (asymLatticeTestFnIso Lt Ls Nt Ns a f) x)) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [asymRawSource, Pi.smul_apply, smul_eq_mul]
      field_simp [ha0, ha2] <;> ring
    _ = a ^ 2 * ∑ x : AsymLatticeSites Nt Ns,
        (ω (asymLatticeDelta Nt Ns x)) *
          asymRawSource a (asymLatticeTestFnIso Lt Ls Nt Ns a f) x := by
      rw [Finset.mul_sum]

/-! ## Source control for the finite interacting measure -/

/-- A weighted `Lᵖ` source ball gives the pointwise source estimate consumed by
`interactingLatticeMeasureAsym_integrable_exp_of_source_control`.

The witness `η` is allowed to depend on the source-ball radius.  This is the exact
finite Holder/Young step; all uniformity in `a`, the physical volume, and the test
function belongs to the theorem which supplies `hLp`. -/
theorem asymSourceControl_of_weightedLpPow
    (Lt Ls : ℝ) [Fact (0 < Lt)] [Fact (0 < Ls)]
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a : ℝ) (ha : 0 < a)
    (f : AsymTorusTestFunction Lt Ls)
    (hLp :
      asymWeightedLpPow
          ((P.n : ℝ) / ((P.n : ℝ) - 1)) a
          (asymRawSource a (asymLatticeTestFnIso Lt Ls Nt Ns a f)) ≤
      (1 / 2 : ℝ) ^ ((P.n : ℝ) / ((P.n : ℝ) - 1))) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧
      ∀ ω : Configuration (AsymLatticeField Nt Ns),
        (ω (asymLatticeTestFnIso Lt Ls Nt Ns a f)) ^ P.n / (P.n : ℝ) ≤
          a ^ 2 * ∑ x : AsymLatticeSites Nt Ns,
            ((1 - η) / (P.n : ℝ)) *
              |ω (asymLatticeDelta Nt Ns x)| ^ P.n := by
  let p : ℝ := (P.n : ℝ) / ((P.n : ℝ) - 1)
  let A : ℝ := a ^ 2 * ∑ x : AsymLatticeSites Nt Ns,
    Real.rpow |asymRawSource a
      (asymLatticeTestFnIso Lt Ls Nt Ns a f) x| p
  let y : ℝ := ((1 / 2 : ℝ) ^ p) ^ (P.n - 1)
  let η : ℝ := 1 - y
  have hn_nat : 1 < P.n := by
    have h := P.hn_ge
    omega
  have hn_real : 1 < (P.n : ℝ) := by exact_mod_cast hn_nat
  have hn_pos : 0 < (P.n : ℝ) := by linarith
  have hp_pos : 0 < p := by
    dsimp [p]
    positivity
  have hbase_pos : 0 < (1 / 2 : ℝ) ^ p :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hbase_lt_one : (1 / 2 : ℝ) ^ p < 1 :=
    Real.rpow_lt_one (by norm_num) (by norm_num) hp_pos
  have hy_pos : 0 < y := by
    dsimp [y]
    exact pow_pos hbase_pos _
  have hy_lt_one : y < 1 := by
    dsimp [y]
    exact pow_lt_one₀ hbase_pos.le hbase_lt_one (by omega)
  have hη_pos : 0 < η := by
    dsimp [η]
    exact sub_pos.mpr hy_lt_one
  have hη_lt_one : η < 1 := by
    dsimp [η]
    exact sub_lt_self 1 hy_pos
  have hA : A ≤ (1 / 2 : ℝ) ^ p := by
    simpa [A, p, asymWeightedLpPow] using hLp
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (sq_nonneg a)
      (Finset.sum_nonneg fun x _ => Real.rpow_nonneg (abs_nonneg _) _)
  have hA_pow : A ^ (P.n - 1) ≤ y := by
    dsimp [y]
    exact (pow_le_pow_left₀ hA_nonneg hA (P.n - 1))
  refine ⟨η, hη_pos, hη_lt_one, ?_⟩
  intro ω
  let g : AsymLatticeField Nt Ns := asymLatticeTestFnIso Lt Ls Nt Ns a f
  let u : AsymLatticeField Nt Ns := asymRawSource a g
  let v : AsymLatticeField Nt Ns := fun x =>
    ω (asymLatticeDelta Nt Ns x)
  have hpair := asymWeightedPairing_pow_le
    (α := AsymLatticeSites Nt Ns) P.n hn_nat a ha u v
  have hB_nonneg : 0 ≤ a ^ 2 * ∑ x : AsymLatticeSites Nt Ns, |v x| ^ P.n := by
    exact mul_nonneg (sq_nonneg a)
      (Finset.sum_nonneg fun x _ => pow_nonneg (abs_nonneg _) _)
  have hpair_bound :
      |a ^ 2 * ∑ x : AsymLatticeSites Nt Ns, u x * v x| ^ P.n ≤
        y * (a ^ 2 * ∑ x : AsymLatticeSites Nt Ns, |v x| ^ P.n) := by
    calc
      |a ^ 2 * ∑ x : AsymLatticeSites Nt Ns, u x * v x| ^ P.n ≤
          A ^ (P.n - 1) *
            (a ^ 2 * ∑ x : AsymLatticeSites Nt Ns, |v x| ^ P.n) := by
        simpa [u, A, p] using hpair
      _ ≤ y * (a ^ 2 * ∑ x : AsymLatticeSites Nt Ns, |v x| ^ P.n) :=
        mul_le_mul_of_nonneg_right hA_pow hB_nonneg
  have hpair_div := div_le_div_of_nonneg_right hpair_bound
    (show 0 ≤ (P.n : ℝ) by positivity)
  have hswap :
      ∑ x : AsymLatticeSites Nt Ns,
          v x * u x = ∑ x : AsymLatticeSites Nt Ns, u x * v x := by
    apply Finset.sum_congr rfl
    intro x hx
    ring
  calc
    (ω g) ^ P.n / (P.n : ℝ) =
        |a ^ 2 * ∑ x : AsymLatticeSites Nt Ns, u x * v x| ^ P.n /
          (P.n : ℝ) := by
      dsimp [g, u, v]
      rw [asymRawSource_pairing_eq Lt Ls Nt Ns a ha f ω]
      rw [hswap, P.hn_even.pow_abs]
    _ ≤ y * (a ^ 2 * ∑ x : AsymLatticeSites Nt Ns, |v x| ^ P.n) /
          (P.n : ℝ) := hpair_div
    _ = a ^ 2 * ∑ x : AsymLatticeSites Nt Ns,
          ((1 - η) / (P.n : ℝ)) * |v x| ^ P.n := by
      dsimp [η, y]
      rw [div_eq_mul_inv]
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      ring

/-- Finite-grid integrability obtained from the weighted source ball and the Wick
coercivity bridge.  This is a per-grid statement; no uniform estimate is claimed. -/
theorem interactingLatticeMeasureAsym_integrable_exp_of_weightedLpPow
    (Lt Ls : ℝ) [Fact (0 < Lt)] [Fact (0 < Ls)]
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f : AsymTorusTestFunction Lt Ls)
    (hLp :
      asymWeightedLpPow
          ((P.n : ℝ) / ((P.n : ℝ) - 1)) a
          (asymRawSource a (asymLatticeTestFnIso Lt Ls Nt Ns a f)) ≤
        (1 / 2 : ℝ) ^ ((P.n : ℝ) / ((P.n : ℝ) - 1))) :
    Integrable
      (fun ω : Configuration (AsymLatticeField Nt Ns) =>
        Real.exp ((ω (asymLatticeTestFnIso Lt Ls Nt Ns a f)) ^ P.n / (P.n : ℝ)))
      (interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) := by
  obtain ⟨η, hη_pos, hη_lt_one, hsource⟩ :=
    asymSourceControl_of_weightedLpPow Lt Ls Nt Ns P a ha f hLp
  exact interactingLatticeMeasureAsym_integrable_exp_of_source_control
    Nt Ns P a mass ha hmass (asymLatticeTestFnIso Lt Ls Nt Ns a f) η
    hη_pos hη_lt_one hsource

end Pphi2
