/-
Mirrored from GibbsMeasure `Ch6Subtree/AppendixProofs/Cluster/Counting.lean`
@ origin/feat/Ch6InfVolume (030b2fafc18db5c26deb3ffbcf44223304534cfe), 2026-07-13.
Generic Kotecký–Preiss engine (no spin/lattice dependence). Candidate for
standalone-library extraction (planning/keystone-18-campaign.md K18-0);
keep divergence minimal.
-/
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Pphi2.ClusterExpansion.KP.Graphs

/-! # Counting lemmas: partitions vs fibered functions -/

open scoped BigOperators ENNReal

set_option linter.unusedSectionVars false

namespace PolymerKP

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-! ### Fibers of a function into `Fin k` -/

section Fibers

variable {k : ℕ}

/-- If all fibers of `f` are nonempty, the fiber map is injective. -/
theorem fiber_injective {f : ι → Fin k}
    (hf : ∀ j, (Finset.univ.filter (fun i => f i = j)).Nonempty) :
    Function.Injective (fun j : Fin k => Finset.univ.filter (fun i => f i = j)) := by
  intro j j' h
  have h' : Finset.univ.filter (fun i => f i = j)
      = Finset.univ.filter (fun i => f i = j') := h
  obtain ⟨i, hi⟩ := hf j
  rw [Finset.mem_filter] at hi
  have hi' : i ∈ Finset.univ.filter (fun i => f i = j') := by
    rw [← h']
    exact Finset.mem_filter.2 ⟨Finset.mem_univ i, hi.2⟩
  rw [Finset.mem_filter] at hi'
  exact hi.2.symm.trans hi'.2

/-- The fibers of a function with nonempty fibers form a partition of `univ`. -/
theorem fiberPartition_mem_partitionsOn {f : ι → Fin k}
    (hf : ∀ j, (Finset.univ.filter (fun i => f i = j)).Nonempty) :
    Finset.univ.image (fun j : Fin k => Finset.univ.filter (fun i => f i = j))
      ∈ partitionsOn (Finset.univ : Finset ι) := by
  refine mem_partitionsOn.2 ⟨?_, ?_, ?_⟩
  · intro W hW
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hW
    exact hf j
  · intro W hW W' hW' hne
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hW)
    obtain ⟨j', -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hW')
    rw [Finset.disjoint_left]
    intro i hi hi'
    rw [Finset.mem_filter] at hi hi'
    exact hne (by rw [hi.2.symm.trans hi'.2])
  · apply Finset.Subset.antisymm
    · intro x _
      exact Finset.mem_univ x
    · intro i _
      rw [Finset.mem_sup]
      exact ⟨Finset.univ.filter (fun i' => f i' = f i),
        Finset.mem_image_of_mem _ (Finset.mem_univ (f i)),
        Finset.mem_filter.2 ⟨Finset.mem_univ i, rfl⟩⟩

/-- A function with nonempty fibers has exactly `k` distinct fibers. -/
theorem card_fiberPartition {f : ι → Fin k}
    (hf : ∀ j, (Finset.univ.filter (fun i => f i = j)).Nonempty) :
    (Finset.univ.image
        (fun j : Fin k => Finset.univ.filter (fun i => f i = j))).card = k := by
  rw [Finset.card_image_of_injOn (fiber_injective hf).injOn, Finset.card_univ,
    Fintype.card_fin]

end Fibers

/-! ### Block assignments: functions with a prescribed fiber partition -/

section BlockAssignment

variable {P : Finset (Finset ι)} {k : ℕ}

/-- The unique block of the partition `P` of `univ` containing `i`. -/
def blockOfMem (hP : P ∈ partitionsOn (Finset.univ : Finset ι)) (i : ι) : Finset ι :=
  P.choose (fun W => i ∈ W) (exists_unique_block hP (Finset.mem_univ i))

theorem blockOfMem_mem (hP : P ∈ partitionsOn (Finset.univ : Finset ι)) (i : ι) :
    blockOfMem hP i ∈ P :=
  Finset.choose_mem _ _ _

theorem mem_blockOfMem (hP : P ∈ partitionsOn (Finset.univ : Finset ι)) (i : ι) :
    i ∈ blockOfMem hP i :=
  Finset.choose_property (fun W => i ∈ W) P
    (exists_unique_block hP (Finset.mem_univ i))

theorem blockOfMem_eq (hP : P ∈ partitionsOn (Finset.univ : Finset ι))
    {W : Finset ι} {i : ι} (hW : W ∈ P) (hi : i ∈ W) :
    blockOfMem hP i = W :=
  ExistsUnique.unique (exists_unique_block hP (Finset.mem_univ i))
    ⟨blockOfMem_mem hP i, mem_blockOfMem hP i⟩ ⟨hW, hi⟩

theorem fiber_mem_of_image_eq {f : ι → Fin k}
    (hf2 : Finset.univ.image
      (fun j : Fin k => Finset.univ.filter (fun i => f i = j)) = P)
    (j : Fin k) :
    Finset.univ.filter (fun i => f i = j) ∈ P := by
  rw [← hf2]
  exact Finset.mem_image_of_mem _ (Finset.mem_univ j)

/-- The function determined by an enumeration `φ` of the blocks of `P`:
`i` is sent to the index of its block. -/
def ofBlockEquiv (hP : P ∈ partitionsOn (Finset.univ : Finset ι))
    (φ : Fin k ≃ {W // W ∈ P}) : ι → Fin k :=
  fun i => φ.symm ⟨blockOfMem hP i, blockOfMem_mem hP i⟩

theorem fiber_ofBlockEquiv (hP : P ∈ partitionsOn (Finset.univ : Finset ι))
    (φ : Fin k ≃ {W // W ∈ P}) (j : Fin k) :
    Finset.univ.filter (fun i => ofBlockEquiv hP φ i = j) = (φ j).1 := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ofBlockEquiv]
  rw [Equiv.symm_apply_eq]
  constructor
  · intro h
    have hval : blockOfMem hP i = (φ j).1 := congrArg Subtype.val h
    rw [← hval]
    exact mem_blockOfMem hP i
  · intro hi
    exact Subtype.ext (blockOfMem_eq hP (φ j).2 hi)

theorem ofBlockEquiv_fibers_nonempty (hP : P ∈ partitionsOn (Finset.univ : Finset ι))
    (φ : Fin k ≃ {W // W ∈ P}) :
    ∀ j, (Finset.univ.filter (fun i => ofBlockEquiv hP φ i = j)).Nonempty := by
  intro j
  rw [fiber_ofBlockEquiv]
  exact (mem_partitionsOn.1 hP).1 _ (φ j).2

theorem ofBlockEquiv_image_eq (hP : P ∈ partitionsOn (Finset.univ : Finset ι))
    (φ : Fin k ≃ {W // W ∈ P}) :
    Finset.univ.image
      (fun j : Fin k => Finset.univ.filter (fun i => ofBlockEquiv hP φ i = j)) = P := by
  ext W
  rw [Finset.mem_image]
  constructor
  · rintro ⟨j, -, rfl⟩
    rw [fiber_ofBlockEquiv]
    exact (φ j).2
  · intro hW
    refine ⟨φ.symm ⟨W, hW⟩, Finset.mem_univ _, ?_⟩
    rw [fiber_ofBlockEquiv, Equiv.apply_symm_apply]

/-- There are exactly `k!` functions `ι → Fin k` whose fiber partition is a
given partition `P` of `univ` with `k` blocks. -/
theorem card_filter_fiberPartition_eq
    (hP : P ∈ partitionsOn (Finset.univ : Finset ι)) (hPk : P.card = k) :
    ((Finset.univ : Finset (ι → Fin k)).filter
        (fun f => (∀ j, (Finset.univ.filter (fun i => f i = j)).Nonempty) ∧
          Finset.univ.image
            (fun j : Fin k => Finset.univ.filter (fun i => f i = j)) = P)).card
      = k.factorial := by
  classical
  -- the subtype of admissible functions is equivalent to block enumerations
  have E : {f : ι → Fin k // (∀ j, (Finset.univ.filter (fun i => f i = j)).Nonempty) ∧
        Finset.univ.image
          (fun j : Fin k => Finset.univ.filter (fun i => f i = j)) = P}
      ≃ (Fin k ≃ {W // W ∈ P}) := by
    refine
      ⟨fun fp => Equiv.ofBijective
          (fun j => (⟨Finset.univ.filter (fun i => fp.1 i = j),
            fiber_mem_of_image_eq fp.2.2 j⟩ : {W // W ∈ P})) ⟨?_, ?_⟩,
        fun φ => ⟨ofBlockEquiv hP φ,
          ofBlockEquiv_fibers_nonempty hP φ, ofBlockEquiv_image_eq hP φ⟩,
        ?_, ?_⟩
    · -- injectivity of the fiber enumeration
      intro j j' h
      exact fiber_injective fp.2.1 (congrArg Subtype.val h)
    · -- surjectivity of the fiber enumeration
      rintro ⟨W, hW⟩
      have hW' := hW
      rw [← fp.2.2] at hW'
      obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hW'
      exact ⟨j, Subtype.ext hj⟩
    · -- left inverse
      rintro ⟨f, hf1, hf2⟩
      apply Subtype.ext
      funext i
      simp only [ofBlockEquiv]
      rw [Equiv.symm_apply_eq]
      apply Subtype.ext
      simp only [Equiv.ofBijective_apply]
      exact blockOfMem_eq hP (fiber_mem_of_image_eq hf2 (f i))
        (Finset.mem_filter.2 ⟨Finset.mem_univ i, rfl⟩)
    · -- right inverse
      intro φ
      apply Equiv.ext
      intro j
      apply Subtype.ext
      simp only [Equiv.ofBijective_apply]
      exact fiber_ofBlockEquiv hP φ j
  have hsub : ∀ f : ι → Fin k,
      f ∈ (Finset.univ : Finset (ι → Fin k)).filter
        (fun f => (∀ j, (Finset.univ.filter (fun i => f i = j)).Nonempty) ∧
          Finset.univ.image
            (fun j : Fin k => Finset.univ.filter (fun i => f i = j)) = P)
      ↔ (∀ j, (Finset.univ.filter (fun i => f i = j)).Nonempty) ∧
          Finset.univ.image
            (fun j : Fin k => Finset.univ.filter (fun i => f i = j)) = P := by
    intro f
    rw [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ f, h⟩⟩
  have hcards : Fintype.card (Fin k) = Fintype.card {W // W ∈ P} := by
    rw [Fintype.card_fin, Fintype.card_coe, hPk]
  rw [← Fintype.card_of_subtype _ hsub, Fintype.card_congr E,
    Fintype.card_equiv (Fintype.equivOfCardEq hcards), Fintype.card_fin]

end BlockAssignment

/-! ### C1: partitions with `k` blocks vs surjections onto `Fin k` -/

/-- **C1 (equality form).**  Summing `∏ u` over partitions of `univ` with exactly
`k` blocks, multiplied by `k!`, equals the sum over all functions `ι → Fin k`
with nonempty fibers of the product of `u` over the fibers. -/
theorem factorial_mul_sum_partitions_card {M : Type*} [CommSemiring M]
    (u : Finset ι → M) (k : ℕ) :
    (k.factorial : M) *
      ∑ P ∈ (partitionsOn (Finset.univ : Finset ι)).filter (fun P => P.card = k),
        ∏ W ∈ P, u W
    = ∑ f ∈ (Finset.univ : Finset (ι → Fin k)).filter
        (fun f => ∀ j, (Finset.univ.filter (fun i => f i = j)).Nonempty),
        ∏ j : Fin k, u (Finset.univ.filter (fun i => f i = j)) := by
  classical
  have hmaps : ∀ f ∈ (Finset.univ : Finset (ι → Fin k)).filter
      (fun f => ∀ j, (Finset.univ.filter (fun i => f i = j)).Nonempty),
      Finset.univ.image (fun j : Fin k => Finset.univ.filter (fun i => f i = j))
        ∈ (partitionsOn (Finset.univ : Finset ι)).filter (fun P => P.card = k) := by
    intro f hf
    rw [Finset.mem_filter] at hf
    rw [Finset.mem_filter]
    exact ⟨fiberPartition_mem_partitionsOn hf.2, card_fiberPartition hf.2⟩
  calc (k.factorial : M) *
      ∑ P ∈ (partitionsOn (Finset.univ : Finset ι)).filter (fun P => P.card = k),
        ∏ W ∈ P, u W
      = ∑ P ∈ (partitionsOn (Finset.univ : Finset ι)).filter (fun P => P.card = k),
          (k.factorial : M) * ∏ W ∈ P, u W := Finset.mul_sum _ _ _
    _ = ∑ P ∈ (partitionsOn (Finset.univ : Finset ι)).filter (fun P => P.card = k),
          ∑ f ∈ ((Finset.univ : Finset (ι → Fin k)).filter
              (fun f => ∀ j, (Finset.univ.filter (fun i => f i = j)).Nonempty)).filter
            (fun f => Finset.univ.image
              (fun j : Fin k => Finset.univ.filter (fun i => f i = j)) = P),
          ∏ j : Fin k, u (Finset.univ.filter (fun i => f i = j)) := ?_
    _ = ∑ f ∈ (Finset.univ : Finset (ι → Fin k)).filter
          (fun f => ∀ j, (Finset.univ.filter (fun i => f i = j)).Nonempty),
          ∏ j : Fin k, u (Finset.univ.filter (fun i => f i = j)) :=
        Finset.sum_fiberwise_of_maps_to hmaps _
  refine Finset.sum_congr rfl fun P hP => ?_
  rw [Finset.mem_filter] at hP
  obtain ⟨hPmem, hPk⟩ := hP
  have hcardF : (((Finset.univ : Finset (ι → Fin k)).filter
      (fun f => ∀ j, (Finset.univ.filter (fun i => f i = j)).Nonempty)).filter
        (fun f => Finset.univ.image
          (fun j : Fin k => Finset.univ.filter (fun i => f i = j)) = P)).card
      = k.factorial := by
    rw [Finset.filter_filter]
    exact card_filter_fiberPartition_eq hPmem hPk
  have hconst : ∀ f ∈ ((Finset.univ : Finset (ι → Fin k)).filter
      (fun f => ∀ j, (Finset.univ.filter (fun i => f i = j)).Nonempty)).filter
        (fun f => Finset.univ.image
          (fun j : Fin k => Finset.univ.filter (fun i => f i = j)) = P),
      (∏ j : Fin k, u (Finset.univ.filter (fun i => f i = j))) = ∏ W ∈ P, u W := by
    intro f hf
    rw [Finset.mem_filter, Finset.mem_filter] at hf
    obtain ⟨⟨-, hf1⟩, hf2⟩ := hf
    rw [← hf2]
    exact (Finset.prod_image fun j _ j' _ h => fiber_injective hf1 h).symm
  calc (k.factorial : M) * ∏ W ∈ P, u W
      = ((((Finset.univ : Finset (ι → Fin k)).filter
          (fun f => ∀ j, (Finset.univ.filter (fun i => f i = j)).Nonempty)).filter
            (fun f => Finset.univ.image
              (fun j : Fin k => Finset.univ.filter (fun i => f i = j)) = P)).card : M)
          * ∏ W ∈ P, u W := by rw [hcardF]
    _ = ∑ _f ∈ ((Finset.univ : Finset (ι → Fin k)).filter
          (fun f => ∀ j, (Finset.univ.filter (fun i => f i = j)).Nonempty)).filter
            (fun f => Finset.univ.image
              (fun j : Fin k => Finset.univ.filter (fun i => f i = j)) = P),
          ∏ W ∈ P, u W := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = ∑ f ∈ ((Finset.univ : Finset (ι → Fin k)).filter
          (fun f => ∀ j, (Finset.univ.filter (fun i => f i = j)).Nonempty)).filter
            (fun f => Finset.univ.image
              (fun j : Fin k => Finset.univ.filter (fun i => f i = j)) = P),
          ∏ j : Fin k, u (Finset.univ.filter (fun i => f i = j)) :=
        Finset.sum_congr rfl fun f hf => (hconst f hf).symm

/-- **C1 (inequality form, `ℝ≥0∞`).**  Dropping the surjectivity constraint
gives an upper bound by the full sum over all functions, divided by `k!`. -/
theorem sum_partitions_card_le (u : Finset ι → ℝ≥0∞) (k : ℕ) :
    ∑ P ∈ (partitionsOn (Finset.univ : Finset ι)).filter (fun P => P.card = k),
        ∏ W ∈ P, u W
    ≤ (k.factorial : ℝ≥0∞)⁻¹ *
        ∑ f : ι → Fin k, ∏ j : Fin k, u (Finset.univ.filter (fun i => f i = j)) := by
  classical
  have hk0 : (k.factorial : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
  have hktop : (k.factorial : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hrw : ∑ P ∈ (partitionsOn (Finset.univ : Finset ι)).filter (fun P => P.card = k),
      ∏ W ∈ P, u W
      = (k.factorial : ℝ≥0∞)⁻¹ * ((k.factorial : ℝ≥0∞) *
        ∑ P ∈ (partitionsOn (Finset.univ : Finset ι)).filter (fun P => P.card = k),
          ∏ W ∈ P, u W) := by
    rw [← mul_assoc, ENNReal.inv_mul_cancel hk0 hktop, one_mul]
  rw [hrw, factorial_mul_sum_partitions_card u k]
  exact mul_le_mul_right (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)) _

/-! ### C2: functions with prescribed fiber cardinalities (the multinomial) -/

/-- Splitting the fiber count of `f : Fin (n+1) → Fin k` at the first
coordinate. -/
theorem card_filter_fin_succ {n k : ℕ} (f : Fin (n + 1) → Fin k) (j : Fin k) :
    (Finset.univ.filter (fun i => f i = j)).card
      = (if f 0 = j then 1 else 0)
        + (Finset.univ.filter (fun i : Fin n => f i.succ = j)).card := by
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]

/-- **C2.**  The number of functions `Fin n → Fin k` with prescribed fiber
cardinalities `m j`, times `∏ (m j)!`, is `n!` (the multinomial identity). -/
theorem card_fiber_sizes_mul_factorials {n k : ℕ} (m : Fin k → ℕ)
    (hm : ∑ j, m j = n) :
    ((Finset.univ : Finset (Fin n → Fin k)).filter
        (fun f => ∀ j, (Finset.univ.filter (fun i => f i = j)).card = m j)).card
      * ∏ j, (m j).factorial = n.factorial := by
  induction n generalizing m with
  | zero =>
      have hm0 : ∀ j, m j = 0 := fun j =>
        Nat.le_zero.1 (hm ▸ Finset.single_le_sum
          (fun i _ => Nat.zero_le (m i)) (Finset.mem_univ j))
      have hfilter : (Finset.univ : Finset (Fin 0 → Fin k)).filter
          (fun f => ∀ j, (Finset.univ.filter (fun i => f i = j)).card = m j)
          = Finset.univ := by
        refine Finset.filter_true_of_mem fun f _ => fun j => ?_
        rw [hm0 j]
        simp
      rw [hfilter]
      simp [hm0]
  | succ n ih =>
      have hsplit : ((Finset.univ : Finset (Fin (n + 1) → Fin k)).filter
          (fun f => ∀ j, (Finset.univ.filter (fun i => f i = j)).card = m j)).card
          = ∑ j₀ : Fin k, (((Finset.univ : Finset (Fin (n + 1) → Fin k)).filter
              (fun f => ∀ j, (Finset.univ.filter (fun i => f i = j)).card = m j)).filter
                (fun f => f 0 = j₀)).card :=
        Finset.card_eq_sum_card_fiberwise (fun f _ => Finset.mem_univ (f 0))
      have hterm : ∀ j₀ : Fin k,
          (((Finset.univ : Finset (Fin (n + 1) → Fin k)).filter
            (fun f => ∀ j, (Finset.univ.filter (fun i => f i = j)).card = m j)).filter
              (fun f => f 0 = j₀)).card * ∏ j, (m j).factorial
          = m j₀ * n.factorial := by
        intro j₀
        rcases Nat.eq_zero_or_pos (m j₀) with hmj | hpos
        · -- no function can have an empty fiber over the value of `f 0`
          have hempty : ((Finset.univ : Finset (Fin (n + 1) → Fin k)).filter
              (fun f => ∀ j, (Finset.univ.filter (fun i => f i = j)).card = m j)).filter
                (fun f => f 0 = j₀) = ∅ := by
            rw [Finset.filter_eq_empty_iff]
            intro f hf hf0
            rw [Finset.mem_filter] at hf
            have h0mem : (0 : Fin (n + 1)) ∈ Finset.univ.filter (fun i => f i = j₀) :=
              Finset.mem_filter.2 ⟨Finset.mem_univ _, hf0⟩
            have hcard0 := hf.2 j₀
            rw [hmj, Finset.card_eq_zero] at hcard0
            rw [hcard0] at h0mem
            exact Finset.notMem_empty _ h0mem
          rw [hempty, Finset.card_empty, hmj, zero_mul, zero_mul]
        · obtain ⟨s, hmj⟩ : ∃ s, m j₀ = s + 1 := ⟨m j₀ - 1, by omega⟩
          -- bijection with functions `Fin n → Fin k` of fiber sizes `update m j₀ s`
          have hcard : (((Finset.univ : Finset (Fin (n + 1) → Fin k)).filter
              (fun f => ∀ j, (Finset.univ.filter (fun i => f i = j)).card = m j)).filter
                (fun f => f 0 = j₀)).card
              = ((Finset.univ : Finset (Fin n → Fin k)).filter
                  (fun g => ∀ j, (Finset.univ.filter (fun i => g i = j)).card
                    = Function.update m j₀ s j)).card := by
            refine Finset.card_bij' (fun f _ => fun i : Fin n => f i.succ)
              (fun g _ => Fin.cons j₀ g) ?_ ?_ ?_ ?_
            · -- forward membership
              intro f hf
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
              obtain ⟨hfib, hf0⟩ := hf
              intro j
              have hkey := card_filter_fin_succ f j
              rw [hfib j, hf0] at hkey
              rcases eq_or_ne j j₀ with rfl | hj
              · rw [Function.update_self]
                rw [if_pos rfl, hmj] at hkey
                omega
              · rw [Function.update_of_ne hj]
                rw [if_neg (Ne.symm hj)] at hkey
                omega
            · -- backward membership
              intro g hg
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
              refine ⟨fun j => ?_, by simp⟩
              have hkey := card_filter_fin_succ (Fin.cons j₀ g) j
              have hsucc : (Finset.univ.filter
                    (fun i : Fin n => (Fin.cons j₀ g : Fin (n + 1) → Fin k) i.succ = j))
                  = Finset.univ.filter (fun i : Fin n => g i = j) :=
                Finset.filter_congr fun i _ => by rw [Fin.cons_succ]
              rw [hsucc, hg j, Fin.cons_zero] at hkey
              rcases eq_or_ne j j₀ with rfl | hj
              · rw [hkey, if_pos rfl, Function.update_self, hmj]
                omega
              · rw [hkey, if_neg (Ne.symm hj), Function.update_of_ne hj]
                omega
            · -- left inverse
              intro f hf
              simp only [Finset.mem_filter] at hf
              show (Fin.cons j₀ (fun i => f i.succ) : Fin (n + 1) → Fin k) = f
              rw [← hf.2]
              exact Fin.cons_self_tail f
            · -- right inverse
              intro g _
              funext i
              apply Fin.cons_succ
          have hsum' : ∑ j, Function.update m j₀ s j = n := by
            have h1 : Function.update m j₀ s j₀
                + ∑ j ∈ Finset.univ.erase j₀, Function.update m j₀ s j
                = ∑ j, Function.update m j₀ s j :=
              Finset.add_sum_erase Finset.univ (fun j => Function.update m j₀ s j)
                (Finset.mem_univ j₀)
            have h2 : m j₀ + ∑ j ∈ Finset.univ.erase j₀, m j = ∑ j, m j :=
              Finset.add_sum_erase Finset.univ m (Finset.mem_univ j₀)
            have h3 : ∑ j ∈ Finset.univ.erase j₀, Function.update m j₀ s j
                = ∑ j ∈ Finset.univ.erase j₀, m j :=
              Finset.sum_congr rfl fun j hj =>
                Function.update_of_ne (Finset.ne_of_mem_erase hj) _ _
            rw [Function.update_self, h3] at h1
            omega
          have hprod : ∏ j, (m j).factorial
              = m j₀ * ∏ j, (Function.update m j₀ s j).factorial := by
            have h1 : (m j₀).factorial * ∏ j ∈ Finset.univ.erase j₀, (m j).factorial
                = ∏ j, (m j).factorial :=
              Finset.mul_prod_erase Finset.univ (fun j => (m j).factorial)
                (Finset.mem_univ j₀)
            have h2 : (Function.update m j₀ s j₀).factorial
                * ∏ j ∈ Finset.univ.erase j₀, (Function.update m j₀ s j).factorial
                = ∏ j, (Function.update m j₀ s j).factorial :=
              Finset.mul_prod_erase Finset.univ
                (fun j => (Function.update m j₀ s j).factorial) (Finset.mem_univ j₀)
            have h3 : ∏ j ∈ Finset.univ.erase j₀, (Function.update m j₀ s j).factorial
                = ∏ j ∈ Finset.univ.erase j₀, (m j).factorial :=
              Finset.prod_congr rfl fun j hj => by
                rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
            rw [Function.update_self, h3] at h2
            rw [← h1, ← h2, hmj, Nat.factorial_succ]
            ring
          calc (((Finset.univ : Finset (Fin (n + 1) → Fin k)).filter
                (fun f => ∀ j, (Finset.univ.filter (fun i => f i = j)).card = m j)).filter
                  (fun f => f 0 = j₀)).card * ∏ j, (m j).factorial
              = ((Finset.univ : Finset (Fin n → Fin k)).filter
                  (fun g => ∀ j, (Finset.univ.filter (fun i => g i = j)).card
                    = Function.update m j₀ s j)).card
                * (m j₀ * ∏ j, (Function.update m j₀ s j).factorial) := by
                  rw [hcard, hprod]
            _ = m j₀ * (((Finset.univ : Finset (Fin n → Fin k)).filter
                  (fun g => ∀ j, (Finset.univ.filter (fun i => g i = j)).card
                    = Function.update m j₀ s j)).card
                * ∏ j, (Function.update m j₀ s j).factorial) := by ring
            _ = m j₀ * n.factorial := by rw [ih _ hsum']
      calc ((Finset.univ : Finset (Fin (n + 1) → Fin k)).filter
            (fun f => ∀ j, (Finset.univ.filter (fun i => f i = j)).card = m j)).card
            * ∏ j, (m j).factorial
          = (∑ j₀ : Fin k, (((Finset.univ : Finset (Fin (n + 1) → Fin k)).filter
              (fun f => ∀ j, (Finset.univ.filter (fun i => f i = j)).card = m j)).filter
                (fun f => f 0 = j₀)).card) * ∏ j, (m j).factorial := by rw [hsplit]
        _ = ∑ j₀ : Fin k, (((Finset.univ : Finset (Fin (n + 1) → Fin k)).filter
              (fun f => ∀ j, (Finset.univ.filter (fun i => f i = j)).card = m j)).filter
                (fun f => f 0 = j₀)).card * ∏ j, (m j).factorial :=
            Finset.sum_mul _ _ _
        _ = ∑ j₀ : Fin k, m j₀ * n.factorial :=
            Finset.sum_congr rfl fun j₀ _ => hterm j₀
        _ = (∑ j₀ : Fin k, m j₀) * n.factorial := (Finset.sum_mul _ _ _).symm
        _ = (n + 1) * n.factorial := by rw [hm]
        _ = (n + 1).factorial := (Nat.factorial_succ n).symm

/-! ### C3: grouping a fiber-size-dependent sum by the size vector -/

/-- **C3.**  A sum over all functions `Fin n → Fin k` of a product depending
only on the fiber cardinalities groups by the vector of fiber sizes. -/
theorem sum_pi_prod_fiber_card (n k : ℕ) (v : ℕ → ℝ≥0∞) :
    ∑ f : Fin n → Fin k, ∏ j : Fin k, v ((Finset.univ.filter (fun i => f i = j)).card)
      = ∑ m ∈ Finset.piAntidiag (Finset.univ : Finset (Fin k)) n,
          (((Finset.univ : Finset (Fin n → Fin k)).filter
              (fun f => ∀ j, (Finset.univ.filter (fun i => f i = j)).card = m j)).card
            : ℝ≥0∞)
          * ∏ j : Fin k, v (m j) := by
  classical
  have hmaps : ∀ f ∈ (Finset.univ : Finset (Fin n → Fin k)),
      (fun j : Fin k => (Finset.univ.filter (fun i => f i = j)).card)
        ∈ Finset.piAntidiag (Finset.univ : Finset (Fin k)) n := by
    intro f _
    rw [Finset.mem_piAntidiag]
    refine ⟨?_, fun i _ => Finset.mem_univ i⟩
    have hcard := Finset.card_eq_sum_card_fiberwise
      (f := f) (s := (Finset.univ : Finset (Fin n)))
      (t := (Finset.univ : Finset (Fin k))) (fun x _ => Finset.mem_univ (f x))
    rw [Finset.card_univ, Fintype.card_fin] at hcard
    exact hcard.symm
  calc ∑ f : Fin n → Fin k,
        ∏ j : Fin k, v ((Finset.univ.filter (fun i => f i = j)).card)
      = ∑ m ∈ Finset.piAntidiag (Finset.univ : Finset (Fin k)) n,
          ∑ f ∈ (Finset.univ : Finset (Fin n → Fin k)).filter
            (fun f => (fun j : Fin k => (Finset.univ.filter (fun i => f i = j)).card) = m),
          ∏ j : Fin k, v ((Finset.univ.filter (fun i => f i = j)).card) :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ = ∑ m ∈ Finset.piAntidiag (Finset.univ : Finset (Fin k)) n,
          (((Finset.univ : Finset (Fin n → Fin k)).filter
              (fun f => ∀ j, (Finset.univ.filter (fun i => f i = j)).card = m j)).card
            : ℝ≥0∞)
          * ∏ j : Fin k, v (m j) := ?_
  refine Finset.sum_congr rfl fun m hm => ?_
  have hfeq : ((Finset.univ : Finset (Fin n → Fin k)).filter
      (fun f => (fun j : Fin k => (Finset.univ.filter (fun i => f i = j)).card) = m))
      = (Finset.univ : Finset (Fin n → Fin k)).filter
        (fun f => ∀ j, (Finset.univ.filter (fun i => f i = j)).card = m j) :=
    Finset.filter_congr fun f _ => funext_iff
  rw [hfeq]
  have hconst : ∀ f ∈ (Finset.univ : Finset (Fin n → Fin k)).filter
      (fun f => ∀ j, (Finset.univ.filter (fun i => f i = j)).card = m j),
      (∏ j : Fin k, v ((Finset.univ.filter (fun i => f i = j)).card))
        = ∏ j : Fin k, v (m j) := by
    intro f hf
    rw [Finset.mem_filter] at hf
    exact Finset.prod_congr rfl fun j _ => by rw [hf.2 j]
  calc ∑ f ∈ (Finset.univ : Finset (Fin n → Fin k)).filter
        (fun f => ∀ j, (Finset.univ.filter (fun i => f i = j)).card = m j),
        ∏ j : Fin k, v ((Finset.univ.filter (fun i => f i = j)).card)
      = ∑ _f ∈ (Finset.univ : Finset (Fin n → Fin k)).filter
          (fun f => ∀ j, (Finset.univ.filter (fun i => f i = j)).card = m j),
          ∏ j : Fin k, v (m j) :=
        Finset.sum_congr rfl hconst
    _ = (((Finset.univ : Finset (Fin n → Fin k)).filter
          (fun f => ∀ j, (Finset.univ.filter (fun i => f i = j)).card = m j)).card
          : ℝ≥0∞)
        * ∏ j : Fin k, v (m j) := by
        rw [Finset.sum_const, nsmul_eq_mul]

end PolymerKP
