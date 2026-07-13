/-
Mirrored from GibbsMeasure `Ch6Subtree/AppendixProofs/Cluster/TsumFacts.lean`
@ origin/feat/Ch6InfVolume (030b2fafc18db5c26deb3ffbcf44223304534cfe), 2026-07-13.
Generic Kotecký–Preiss engine (no spin/lattice dependence). Candidate for
standalone-library extraction (planning/keystone-18-campaign.md K18-0);
keep divergence minimal.
-/
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # tsum infrastructure for the cluster expansion

Infinite-sum (`tsum`) facts used by the Kotecký–Preiss cluster expansion:

* `tsum_pi_prod_ennreal` / `tsum_pi_prod` — finite dependent Fubini: the sum of a
  product of `k` independent factors over a finite product of index types
  factorizes as the product of the sums (`ℝ≥0∞` and absolutely summable `ℝ`
  versions);
* `tsum_pow_eq_tsum_pi_ennreal` / `tsum_pow_eq_tsum_pi` — the power `(∑' a, g a) ^ k`
  as a sum over `k`-tuples;
* `fiberPiEquiv` — factorization of a function space along the fibers of a map into
  `Fin k`;
* `tsum_sum_pin_eq_card_mul_pinned` — symmetrization: for a permutation-invariant
  weight, summing an occupation count over all tuples equals `(n+1)` times the sum
  pinned at index `0`;
* `tsum_eq_factorial_mul_tsum_finset_ennreal` / `tsum_eq_factorial_mul_tsum_finset`
  — a permutation-invariant weight supported on injective tuples sums to `n!` times
  its sum over `n`-element finite sets (enumerated increasingly).
-/

open scoped BigOperators ENNReal

set_option linter.unusedSectionVars false

namespace PolymerKP

/-- `tsum` over a `Unique` index type. -/
private theorem tsum_of_unique {ι M : Type*} [Unique ι] [AddCommMonoid M]
    [TopologicalSpace M] [T2Space M] (f : ι → M) : ∑' i, f i = f default :=
  tsum_eq_single default fun b' hb' => absurd (Subsingleton.elim b' default) hb'

/-! ## T1: finite dependent Fubini, `ℝ≥0∞` version -/

theorem tsum_pi_prod_ennreal {k : ℕ} {A : Fin k → Type*} (g : ∀ j, A j → ℝ≥0∞) :
    ∑' x : ∀ j, A j, ∏ j, g j (x j) = ∏ j, ∑' a, g j a := by
  induction k with
  | zero =>
    rw [tsum_of_unique]
    simp
  | succ k ih =>
    calc ∑' x : ∀ j, A j, ∏ j, g j (x j)
        = ∑' p : A 0 × (∀ j : Fin k, A j.succ), ∏ j, g j (Fin.consEquiv A p j) :=
          ((Fin.consEquiv A).tsum_eq fun x => ∏ j, g j (x j)).symm
      _ = ∑' p : A 0 × (∀ j : Fin k, A j.succ), g 0 p.1 * ∏ j, g j.succ (p.2 j) :=
          tsum_congr fun p => by simp [Fin.prod_univ_succ]
      _ = ∑' a : A 0, ∑' b : ∀ j : Fin k, A j.succ, g 0 a * ∏ j, g j.succ (b j) :=
          ENNReal.tsum_prod
            (f := fun (a : A 0) (b : ∀ j : Fin k, A j.succ) => g 0 a * ∏ j, g j.succ (b j))
      _ = (∑' a : A 0, g 0 a) * ∑' b : ∀ j : Fin k, A j.succ, ∏ j, g j.succ (b j) := by
          simp_rw [ENNReal.tsum_mul_left]
          exact ENNReal.tsum_mul_right
      _ = (∑' a : A 0, g 0 a) * ∏ j : Fin k, ∑' a, g j.succ a := by
          rw [ih (fun j => g j.succ)]
      _ = ∏ j, ∑' a, g j a := (Fin.prod_univ_succ fun j => ∑' a, g j a).symm

/-- T1' : the `k`-th power of a sum as a sum over `k`-tuples, `ℝ≥0∞` version. -/
theorem tsum_pow_eq_tsum_pi_ennreal {A : Type*} (g : A → ℝ≥0∞) (k : ℕ) :
    (∑' a, g a) ^ k = ∑' x : Fin k → A, ∏ j, g (x j) := by
  rw [tsum_pi_prod_ennreal (fun _ : Fin k => g), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-! ## T2: finite dependent Fubini, real version -/

/-- Norm-summability propagates to finite products over dependent tuples. -/
theorem summable_norm_pi_prod {k : ℕ} {A : Fin k → Type*} (g : ∀ j, A j → ℝ)
    (hg : ∀ j, Summable fun a => ‖g j a‖) :
    Summable fun x : ∀ j, A j => ‖∏ j, g j (x j)‖ := by
  induction k with
  | zero => exact Summable.of_finite
  | succ k ih =>
    have htail : Summable fun b : ∀ j : Fin k, A j.succ => ‖∏ j, g j.succ (b j)‖ :=
      ih (fun j => g j.succ) fun j => hg j.succ
    have key := (hg 0).mul_norm htail
    refine ((Fin.consEquiv A).summable_iff
      (f := fun x : ∀ j : Fin (k + 1), A j => ‖∏ j, g j (x j)‖)).mp
      (key.congr fun p => ?_)
    simp [Function.comp, Fin.prod_univ_succ]

theorem summable_pi_prod {k : ℕ} {A : Fin k → Type*} (g : ∀ j, A j → ℝ)
    (hg : ∀ j, Summable fun a => ‖g j a‖) :
    Summable fun x : ∀ j, A j => ∏ j, g j (x j) :=
  (summable_norm_pi_prod g hg).of_norm

theorem tsum_pi_prod {k : ℕ} {A : Fin k → Type*} (g : ∀ j, A j → ℝ)
    (hg : ∀ j, Summable fun a => ‖g j a‖) :
    ∑' x : ∀ j, A j, ∏ j, g j (x j) = ∏ j, ∑' a, g j a := by
  induction k with
  | zero =>
    rw [tsum_of_unique]
    simp
  | succ k ih =>
    calc ∑' x : ∀ j, A j, ∏ j, g j (x j)
        = ∑' p : A 0 × (∀ j : Fin k, A j.succ), ∏ j, g j (Fin.consEquiv A p j) :=
          ((Fin.consEquiv A).tsum_eq fun x => ∏ j, g j (x j)).symm
      _ = ∑' p : A 0 × (∀ j : Fin k, A j.succ), g 0 p.1 * ∏ j, g j.succ (p.2 j) :=
          tsum_congr fun p => by simp [Fin.prod_univ_succ]
      _ = (∑' a : A 0, g 0 a) * ∑' b : ∀ j : Fin k, A j.succ, ∏ j, g j.succ (b j) :=
          (tsum_mul_tsum_of_summable_norm (hg 0)
            (summable_norm_pi_prod (fun j => g j.succ) fun j => hg j.succ)).symm
      _ = (∑' a : A 0, g 0 a) * ∏ j : Fin k, ∑' a, g j.succ a := by
          rw [ih (fun j => g j.succ) fun j => hg j.succ]
      _ = ∏ j, ∑' a, g j a := (Fin.prod_univ_succ fun j => ∑' a, g j a).symm

/-- T2' : the `k`-th power of a sum as a sum over `k`-tuples, real version. -/
theorem tsum_pow_eq_tsum_pi {A : Type*} (g : A → ℝ) (hg : Summable fun a => ‖g a‖) (k : ℕ) :
    (∑' a, g a) ^ k = ∑' x : Fin k → A, ∏ j, g (x j) := by
  rw [tsum_pi_prod (fun _ : Fin k => g) fun _ => hg, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

theorem summable_pi_prod_const {A : Type*} (g : A → ℝ) (hg : Summable fun a => ‖g a‖) (k : ℕ) :
    Summable fun x : Fin k → A => ∏ j, g (x j) :=
  summable_pi_prod (fun _ : Fin k => g) fun _ => hg

/-! ## T3: fiber factorization of a function space -/

/-- A function `ι → P` is the same as a family of functions on the fibers of a map
`f : ι → Fin k`. -/
def fiberPiEquiv {ι : Type*} {k : ℕ} (f : ι → Fin k) (P : Type*) :
    (ι → P) ≃ ∀ j : Fin k, ({i : ι // f i = j} → P) where
  toFun γ j i := γ i.1
  invFun h i := h (f i) ⟨i, rfl⟩
  left_inv γ := rfl
  right_inv h := by
    funext j i
    obtain ⟨i, hi⟩ := i
    subst hi
    rfl

theorem fiberPiEquiv_apply {ι : Type*} {k : ℕ} (f : ι → Fin k) {P : Type*}
    (γ : ι → P) (j : Fin k) (i : {i : ι // f i = j}) :
    fiberPiEquiv f P γ j i = γ i.1 :=
  rfl

/-! ## T5: pinned-index symmetrization -/

/-- Precomposition with a permutation, as a self-equivalence of a function space. -/
def precompEquiv {ι P : Type*} (σ : Equiv.Perm ι) : (ι → P) ≃ (ι → P) where
  toFun γ := γ ∘ σ
  invFun γ := γ ∘ σ.symm
  left_inv γ := funext fun i => by simp
  right_inv γ := funext fun i => by simp

@[simp] theorem precompEquiv_apply {ι P : Type*} (σ : Equiv.Perm ι) (γ : ι → P) :
    precompEquiv σ γ = γ ∘ σ :=
  rfl

open Classical in
/-- For a permutation-invariant weight `F` on `(n+1)`-tuples, summing the number of
entries satisfying `r` against `F` equals `n + 1` times the sum of `F` pinned to
tuples whose `0`-th entry satisfies `r`. -/
theorem tsum_sum_pin_eq_card_mul_pinned {P : Type*} {n : ℕ}
    (F : (Fin (n + 1) → P) → ℝ≥0∞)
    (hF : ∀ (σ : Equiv.Perm (Fin (n + 1))) (γ : Fin (n + 1) → P), F (γ ∘ σ) = F γ)
    (r : P → Prop) :
    ∑' γ : Fin (n + 1) → P, F γ * (∑ j : Fin (n + 1), if r (γ j) then 1 else 0)
      = (n + 1) * ∑' γ : Fin (n + 1) → P, (if r (γ 0) then F γ else 0) := by
  have hswap : ∀ j : Fin (n + 1),
      ∑' γ : Fin (n + 1) → P, (if r (γ j) then F γ else 0)
        = ∑' γ : Fin (n + 1) → P, (if r (γ 0) then F γ else 0) := by
    intro j
    refine (tsum_congr fun γ => ?_).trans
      ((precompEquiv (P := P) (Equiv.swap 0 j)).tsum_eq
        fun γ => if r (γ 0) then F γ else 0)
    simp only [precompEquiv_apply, Function.comp_apply, Equiv.swap_apply_left,
      hF (Equiv.swap 0 j) γ]
  calc ∑' γ : Fin (n + 1) → P, F γ * (∑ j : Fin (n + 1), if r (γ j) then 1 else 0)
      = ∑' γ : Fin (n + 1) → P, ∑ j : Fin (n + 1), (if r (γ j) then F γ else 0) := by
        refine tsum_congr fun γ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_ite, mul_one, mul_zero]
    _ = ∑ j : Fin (n + 1), ∑' γ : Fin (n + 1) → P, (if r (γ j) then F γ else 0) :=
        Summable.tsum_finsetSum (f := fun j γ => if r (γ j) then F γ else 0)
          fun _ _ => ENNReal.summable
    _ = ∑ _j : Fin (n + 1), ∑' γ : Fin (n + 1) → P, (if r (γ 0) then F γ else 0) :=
        Finset.sum_congr rfl fun j _ => hswap j
    _ = (n + 1) * ∑' γ : Fin (n + 1) → P, (if r (γ 0) then F γ else 0) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Nat.cast_add, Nat.cast_one]

/-! ## T4: injective tuples versus `n`-element finite sets -/

section InjectiveTuples

variable {P : Type*} [LinearOrder P] {n : ℕ}

/-- The increasing enumeration of an `n`-element finite set, as a tuple. -/
private def enum (S : {S : Finset P // S.card = n}) : Fin n → P :=
  fun i => (S.1.orderIsoOfFin S.2 i : P)

private theorem enum_injective (S : {S : Finset P // S.card = n}) :
    Function.Injective (enum S) := fun _i _j hij =>
  (S.1.orderIsoOfFin S.2).toEquiv.injective (Subtype.ext hij)

private theorem enum_orderIsoOfFin_symm (S : {S : Finset P // S.card = n})
    (x : {a : P // a ∈ S.1}) :
    enum S ((S.1.orderIsoOfFin S.2).symm x) = x.1 := by
  simp [enum]

private theorem image_enum (S : {S : Finset P // S.card = n}) :
    Finset.univ.image (enum S) = S.1 := by
  ext a
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact (S.1.orderIsoOfFin S.2 i).2
  · intro ha
    exact ⟨(S.1.orderIsoOfFin S.2).symm ⟨a, ha⟩, enum_orderIsoOfFin_symm S ⟨a, ha⟩⟩

private theorem image_comp_perm (γ : Fin n → P) (σ : Equiv.Perm (Fin n)) :
    Finset.univ.image (γ ∘ σ) = Finset.univ.image γ := by
  ext a
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨σ i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨σ.symm i, by simp⟩

/-- A pair (an `n`-element finite set, a permutation) yields an injective tuple:
the increasing enumeration reshuffled by the permutation. -/
private def toInjTuple (p : Σ _S : {S : Finset P // S.card = n}, Equiv.Perm (Fin n)) :
    {γ : Fin n → P // Function.Injective γ} :=
  ⟨enum p.1 ∘ p.2, (enum_injective p.1).comp p.2.injective⟩

private theorem toInjTuple_bijective :
    Function.Bijective (toInjTuple (P := P) (n := n)) := by
  constructor
  · rintro ⟨S, σ⟩ ⟨T, τ⟩ h
    have hval : enum S ∘ ⇑σ = enum T ∘ ⇑τ := congrArg Subtype.val h
    have himg : Finset.univ.image (enum S ∘ ⇑σ) = Finset.univ.image (enum T ∘ ⇑τ) :=
      congrArg (Finset.image · Finset.univ) hval
    rw [image_comp_perm, image_comp_perm, image_enum, image_enum] at himg
    have hST : S = T := Subtype.ext himg
    subst hST
    have hστ : σ = τ := Equiv.ext fun i => enum_injective S (congrFun hval i)
    exact congrArg (Sigma.mk S) hστ
  · rintro ⟨γ, hγ⟩
    have hcard : (Finset.univ.image γ).card = n := by
      rw [Finset.card_image_of_injective _ hγ, Finset.card_univ, Fintype.card_fin]
    have hmem : ∀ i, γ i ∈ Finset.univ.image γ := fun i =>
      Finset.mem_image_of_mem γ (Finset.mem_univ i)
    have hbij : Function.Bijective
        (fun i => (⟨γ i, hmem i⟩ : {a : P // a ∈ Finset.univ.image γ})) := by
      rw [Fintype.bijective_iff_injective_and_card]
      refine ⟨fun i j hij => hγ (congrArg Subtype.val hij), ?_⟩
      rw [Fintype.card_fin, Fintype.card_coe, hcard]
    refine ⟨⟨⟨Finset.univ.image γ, hcard⟩,
      (Equiv.ofBijective _ hbij).trans
        (((Finset.univ.image γ).orderIsoOfFin hcard).symm).toEquiv⟩, ?_⟩
    apply Subtype.ext
    funext i
    exact enum_orderIsoOfFin_symm ⟨Finset.univ.image γ, hcard⟩ ⟨γ i, hmem i⟩

/-- Injective `n`-tuples are pairs (an `n`-element finite set, a permutation). -/
private noncomputable def injTupleEquiv :
    (Σ _S : {S : Finset P // S.card = n}, Equiv.Perm (Fin n)) ≃
      {γ : Fin n → P // Function.Injective γ} :=
  Equiv.ofBijective toInjTuple toInjTuple_bijective

end InjectiveTuples

/-- T4, `ℝ≥0∞` version: a permutation-invariant weight supported on injective tuples
sums to `n!` times its sum over `n`-element finite sets. -/
theorem tsum_eq_factorial_mul_tsum_finset_ennreal {P : Type*} [LinearOrder P] {n : ℕ}
    (F : (Fin n → P) → ℝ≥0∞)
    (hF0 : ∀ γ : Fin n → P, ¬ Function.Injective γ → F γ = 0)
    (hFperm : ∀ (σ : Equiv.Perm (Fin n)) (γ : Fin n → P), F (γ ∘ σ) = F γ) :
    ∑' γ : Fin n → P, F γ
      = (n.factorial : ℝ≥0∞) *
          ∑' S : {S : Finset P // S.card = n}, F (fun i => (S.1.orderIsoOfFin S.2 i : P)) := by
  have hsupp : Function.support F ⊆ {γ : Fin n → P | Function.Injective γ} := by
    intro γ hγ
    by_contra h
    exact hγ (hF0 γ h)
  calc ∑' γ : Fin n → P, F γ
      = ∑' γ : {γ : Fin n → P // Function.Injective γ}, F γ.1 :=
        (tsum_subtype_eq_of_support_subset hsupp).symm
    _ = ∑' p : Σ _S : {S : Finset P // S.card = n}, Equiv.Perm (Fin n), F (enum p.1 ∘ p.2) :=
        ((injTupleEquiv (P := P) (n := n)).tsum_eq fun γ => F γ.1).symm
    _ = ∑' S : {S : Finset P // S.card = n}, ∑' σ : Equiv.Perm (Fin n), F (enum S ∘ σ) :=
        ENNReal.tsum_sigma
          (f := fun (S : {S : Finset P // S.card = n}) (σ : Equiv.Perm (Fin n)) =>
            F (enum S ∘ σ))
    _ = ∑' S : {S : Finset P // S.card = n}, (n.factorial : ℝ≥0∞) * F (enum S) :=
        tsum_congr fun S => by
          calc ∑' σ : Equiv.Perm (Fin n), F (enum S ∘ σ)
              = ∑' _σ : Equiv.Perm (Fin n), F (enum S) :=
                tsum_congr fun σ => hFperm σ (enum S)
            _ = (n.factorial : ℝ≥0∞) * F (enum S) := by
                rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
                  Fintype.card_fin, nsmul_eq_mul]
    _ = (n.factorial : ℝ≥0∞) * ∑' S : {S : Finset P // S.card = n}, F (enum S) :=
        ENNReal.tsum_mul_left
    _ = (n.factorial : ℝ≥0∞) *
          ∑' S : {S : Finset P // S.card = n}, F (fun i => (S.1.orderIsoOfFin S.2 i : P)) :=
        rfl

/-- T4, real version: a summable permutation-invariant weight supported on injective
tuples sums to `n!` times its sum over `n`-element finite sets. -/
theorem tsum_eq_factorial_mul_tsum_finset {P : Type*} [LinearOrder P] {n : ℕ}
    (F : (Fin n → P) → ℝ) (hs : Summable F)
    (hF0 : ∀ γ : Fin n → P, ¬ Function.Injective γ → F γ = 0)
    (hFperm : ∀ (σ : Equiv.Perm (Fin n)) (γ : Fin n → P), F (γ ∘ σ) = F γ) :
    ∑' γ : Fin n → P, F γ
      = (n.factorial : ℝ) *
          ∑' S : {S : Finset P // S.card = n}, F (fun i => (S.1.orderIsoOfFin S.2 i : P)) := by
  have hsupp : Function.support F ⊆ {γ : Fin n → P | Function.Injective γ} := by
    intro γ hγ
    by_contra h
    exact hγ (hF0 γ h)
  have hs1 : Summable fun γ : {γ : Fin n → P // Function.Injective γ} => F γ.1 :=
    hs.subtype _
  have hs2 : Summable fun p : Σ _S : {S : Finset P // S.card = n}, Equiv.Perm (Fin n) =>
      F (enum p.1 ∘ p.2) :=
    ((injTupleEquiv (P := P) (n := n)).summable_iff
      (f := fun γ : {γ : Fin n → P // Function.Injective γ} => F γ.1)).mpr hs1
  calc ∑' γ : Fin n → P, F γ
      = ∑' γ : {γ : Fin n → P // Function.Injective γ}, F γ.1 :=
        (tsum_subtype_eq_of_support_subset hsupp).symm
    _ = ∑' p : Σ _S : {S : Finset P // S.card = n}, Equiv.Perm (Fin n), F (enum p.1 ∘ p.2) :=
        ((injTupleEquiv (P := P) (n := n)).tsum_eq fun γ => F γ.1).symm
    _ = ∑' S : {S : Finset P // S.card = n}, ∑' σ : Equiv.Perm (Fin n), F (enum S ∘ σ) :=
        hs2.tsum_sigma
    _ = ∑' S : {S : Finset P // S.card = n}, (n.factorial : ℝ) * F (enum S) :=
        tsum_congr fun S => by
          calc ∑' σ : Equiv.Perm (Fin n), F (enum S ∘ σ)
              = ∑' _σ : Equiv.Perm (Fin n), F (enum S) :=
                tsum_congr fun σ => hFperm σ (enum S)
            _ = (n.factorial : ℝ) * F (enum S) := by
                rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
                  Fintype.card_fin, nsmul_eq_mul]
    _ = (n.factorial : ℝ) * ∑' S : {S : Finset P // S.card = n}, F (enum S) :=
        tsum_mul_left
    _ = (n.factorial : ℝ) *
          ∑' S : {S : Finset P // S.card = n}, F (fun i => (S.1.orderIsoOfFin S.2 i : P)) :=
        rfl

end PolymerKP
